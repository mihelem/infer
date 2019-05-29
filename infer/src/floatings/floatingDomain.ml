(*      InferNaL - Not a Linter     *)
(* Copyright (c) 2019-present 5Kids *)

open! IStd
open! Float
module F = Format
module Hashtbl = Caml.Hashtbl

(* The following min, max, eq functions cope with the sign of 0. and with NaN *)
let min_nan (a:float) (b:float) : float = 
  match (classify_float a, classify_float b) with
  | (FP_nan, _) | (_, FP_nan) -> nan
  | (FP_zero, FP_zero) -> if (min (copysign 1. a) (copysign 1. b))=(-1.) then (-0.) else 0.
  | _ -> min a b

let max_nan (a:float) (b:float) : float = 
  match (classify_float a, classify_float b) with
  | (FP_nan, _) | (_, FP_nan) -> nan
  | (FP_zero, FP_zero) -> if (max (copysign 1. a) (copysign 1. b))=1. then 0. else (-0.)
  | _ -> max a b

let eq_nan (a:float) (b:float) : bool =
  match (classify_float a, classify_float b) with
  | (FP_nan, FP_nan) -> true
  | (FP_nan, _)
  | (_, FP_nan) -> false 
  | (FP_zero, FP_zero) -> (copysign 1. a) = (copysign 1. b)
  | _ -> a=b

(** Add pp or unneeded? *)

module Range_el = struct
  type t = 
  | Range of float*float
  | Bottom

  let ( <= ) (lhs:t) (rhs:t) : bool = 
    match (lhs, rhs) with
    | (Bottom, _)   -> true
    | (Range _, Bottom) -> false
    | (Range (lhs_l, lhs_u), Range (rhs_l, rhs_u))  
      -> (eq_nan (min_nan lhs_l rhs_l) rhs_l) && (eq_nan (max_nan lhs_u rhs_u) rhs_u)
  
  let merge (a:t) (b:t) : t =
    match (a,b) with
    | (Bottom, x) | (x, Bottom) -> x
    | (Range (a_l, a_u), Range (b_l, b_u)) -> Range (min_nan a_l b_l, max_nan a_u b_u)
  (* !!! XƏBƏRDARLIQ: min/max is now considering NaN !!! *) 

  let constrain (base:t) (constr:t) : t =
    match (base,constr) with
    | (Bottom, _) | (_, Bottom) -> Bottom
    | (Range (a_l, a_u), Range (b_l, b_u)) -> 
      let canonic_range (rng:t) =
        match rng with
        | Range (l,u) when eq_nan (min_nan l u) l -> rng
        | _ -> Bottom
      in canonic_range (Range (max a_l b_l, min a_u b_u))
end

let all_R = Range_el.Range (neg_infinity, infinity)

module Range_el_opt = struct
  type t = Range_el.t option

  let ( <= ) (lhs:t) (rhs:t) : bool =
    match (lhs, rhs) with
    | (None, _) -> true
    | (Some l, Some r) -> Range_el.(l <= r)
    | (_, None) -> false
  
  let merge (a:t) (b:t) : t =
    match (a,b) with
    | (None, b) -> b
    | (a, None) -> a
    | (Some a', Some b') -> Some (Range_el.merge a' b')

  let constrain (base:t) (constr:t) : t =
    match (base,constr) with
    | (None,constr) -> None
    | (a,None) -> a
    | (Some base',Some constr') -> Some (Range_el.constrain base' constr')
(** Naive approach, again... Purpose: testing the framework! *)
(** TODO: implement the table from Bagnara's paper *)
  let plus (a:t) (b:t) : t =
    match (a,b) with
    | (Some (Range_el.Range (a_l, a_u)), Some (Range_el.Range (b_l, b_u))) 
        -> Some (Range_el.Range (a_l+b_l, a_u+b_u))
    | _ -> None

  let minus (a:t) (b:t) : t =
    match (a,b) with
    | (Some (Range_el.Range (a_l, a_u)), Some (Range_el.Range (b_l, b_u))) 
        -> Some (Range_el.Range (a_l-b_u, a_u-b_l))
    | _ -> None
end

(* (Ocaml) -- First steps to make this parametric... **)
(**
type key = string
module Value = Range_el
module Value_opt = Range_el_opt *)

type t = (string, Range_el.t) Hashtbl.t
let find_opt tbl k = Hashtbl.find_opt tbl k
let add tbl k v = Hashtbl.add tbl k v
let replace tbl k v = Hashtbl.replace tbl k v

type summary = t

let ( <= ) ~lhs ~rhs = 
  let cmp (k:string) (v:Range_el.t) (cum:bool) =
    cum && Range_el_opt.(<=) (Some v) (Hashtbl.find_opt rhs k)
  in Hashtbl.fold cmp lhs true

let combine (a:t) (b:t) ~combiner:combiner : t =
  let combine_els (k:string) (v:Range_el.t) (cum:t) =
    let replace_opt (tbl:t) (k:string) (v_opt:Range_el_opt.t) =
      match v_opt with
      | None -> tbl
      | Some v' -> Hashtbl.replace tbl k v'; tbl
    in replace_opt cum k (combiner (Some v) (Hashtbl.find_opt cum k))
  in Hashtbl.fold combine_els a b

let join = combine ~combiner:Range_el_opt.merge

(* constrain may be used when there is a Prune (a guard) *)
let constrain = combine ~combiner:Range_el_opt.constrain

let widening_threshold = 5          (** CHECK *)

let widen ~prev ~next ~num_iters = 
  join prev next
(**  if num_iters<widening_threshold   
    then join prev next
  else next *)

let pp _ _ = ()

let initial:t = Hashtbl.create 100

(*
let join (a:t) (b:t) : t = 
  let merge_els (str:string) (rng:Range_el.t) (cum:t) =
    let replace_opt (tbl:t) (str:string) (rng_opt:Range_el_opt.t) =
      match rng_opt with
      | None -> tbl
      | Some rng' -> Hashtbl.replace tbl str rng'; tbl
    in replace_opt cum str (Range_el_opt.merge (Some rng) (Hashtbl.find_opt cum str))
  in Hashtbl.fold merge_els a b

let constrain (bases:t) (constrs:t) : t = 
  let constrain_els (str:string) (rng:Range_el.t) (cum:t) =
    let replace_opt (tbl:t) (str:string) (rng_opt:Range_el_opt.t) =
      match rng_opt with
      | None -> tbl
      | Some rng' -> Hashtbl.replace tbl str rng'; tbl
    in replace_opt cum str (Range_el_opt.constrain (Some rng) (Hashtbl.find_opt cum str))
  in Hashtbl.fold merge_els a b
**)