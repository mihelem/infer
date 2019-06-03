(*      InferNaL - Not a Linter     *)
(* Copyright (c) 2019-present 5Kids *)

open! IStd

module F = Format
module Hashtbl = Caml.Hashtbl

(**
type t =
| Infinite
| Nan
| Normal
| Subnormal
| Zero *)

(* The following min, max, eq functions cope with the sign of 0. and with NaN *)
let min_nan (a:float) (b:float) : float = 
  let open Float in
  match (classify a, classify b) with
  | (Nan, _) | (_, Nan) -> nan
  | (Zero, Zero) -> 
    if (min (copysign 1. a) (copysign 1. b)) = (-1.) then (-0.) else 0.
  | _ -> min a b

let max_nan (a:float) (b:float) : float = 
  let open Float in
  match (classify a, classify b) with
  | (Nan, _) | (_, Nan) -> nan
  | (Zero, Zero) -> if (max (copysign 1. a) (copysign 1. b))=1. then 0. else (-0.)
  | _ -> max a b

let eq_nan (a:float) (b:float) : bool =
  let open Float in
  match (classify a, classify b) with
  | (Nan, Nan) -> true
  | (_, Nan) | (Nan, _) -> false
  | (Zero, Zero) -> (copysign 1. a) = (copysign 1. b)
  | _ -> a = b

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

let all_R = Range_el.Range (Float.neg_infinity, Float.infinity)

module Range_el_opt = struct
  type t = Range_el.t option

  let to_range_el (rng_o : t) : Range_el.t =
    match rng_o with
    | Some rng -> rng
    | None -> all_R

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
    | (None, constr) -> None
    | (a, None) -> a
    | (Some base', Some constr') -> Some (Range_el.constrain base' constr')
(** Naive approach, again... Purpose: testing the framework! *)
(** TODO: implement the table from Bagnara's paper *)
  let plus (a:t) (b:t) : t =
    match (a,b) with
    | (Some (Range_el.Range (a_l, a_u)), Some (Range_el.Range (b_l, b_u))) 
        -> Some (Range_el.Range (a_l+.b_l, a_u+.b_u))
    | _ -> None

  let minus (a:t) (b:t) : t =
    match (a, b) with
    | (Some (Range_el.Range (a_l, a_u)), Some (Range_el.Range (b_l, b_u))) 
        -> Some (Range_el.Range (a_l-.b_u, a_u-.b_l))
    | _ -> None

  let mult (a:t) (b:t) : t =
    match (a, b) with
    | (Some (Range_el.Range (a_l, a_u)), Some (Range_el.Range (b_l, b_u)))
        -> let extr = [a_l*.b_l ; a_l*.b_u ; a_u*.b_l ; a_u*.b_u]
        in let (Some r_l, Some r_u) = ((List.reduce ~f:min_nan extr), (List.reduce ~f:max_nan extr))
        in Some (Range_el.Range (r_l, r_u))
    | _ -> None

  let div (a:t) (b:t) : t =
    let open Float in
    match (a, b) with
    | (Some (Range_el.Range (a_l, a_u)), Some (Range_el.Range (b_l, b_u))) 
        -> (let extr = [a_l/.b_l ; a_l/.b_u ; a_u/.b_l ; a_u/.b_u]
        in match [(copysign 1. a_l) = (copysign 1. a_u); (copysign 1. b_l) = (copysign 1. b_u)] with
        | [_; true] 
          -> let (Some r_l, Some r_u) = ((List.reduce ~f:min_nan extr), (List.reduce ~f:max_nan extr))
          in Some (Range_el.Range (r_l, r_u))
        | [true; false] when not (a_l=0. || a_u=0.) -> Some all_R
        | _ -> Some (Range_el.Range (nan, nan)))
    | _ -> None  

  let open_left (a:t) : t =
    match a with
    | Some (Range_el.Range (l, r)) when not (eq_nan l Float.nan) -> Some (Range_el.Range (Float.neg_infinity, r))
    | _ -> a

  let open_right (a:t) : t =
    match a with
    | Some (Range_el.Range (l, r)) when not (eq_nan r Float.nan) -> Some (Range_el.Range (l, Float.infinity))
    | _ -> a
end

(* (Ocaml) -- First steps to make this parametric... **)
(**
type key = string
module Value = Range_el
module Value_opt = Range_el_opt *)
type ranges_t = (string, Range_el.t) Hashtbl.t
type aliases_t = (string, string) Hashtbl.t
type t = {ranges : ranges_t; aliases : aliases_t}
type summary = t
let get_ranges {ranges} = ranges
let get_aliases {aliases} = aliases
let find_opt {ranges = tbl} k = Hashtbl.find_opt tbl k
let add {ranges = tbl} k v = Hashtbl.add tbl k v
let replace {ranges = tbl} k v = Hashtbl.replace tbl k v
let alias_find_opt {aliases = tbl} k = Hashtbl.find_opt tbl k
let alias_add {aliases = tbl} k v = Hashtbl.add tbl k v
let alias_replace {aliases = tbl} k v = Hashtbl.replace tbl k v
let copy {ranges; aliases} = {ranges = Hashtbl.copy ranges; aliases = Hashtbl.copy aliases}
let initial:t = {ranges = Hashtbl.create 100; aliases = Hashtbl.create 100}
let empty_d ?(n = 10) _ : t = {ranges = Hashtbl.create n; aliases = Hashtbl.create n}
let make_empty ?(n = 10) _ : t = copy (empty_d ~n:n ())
let id2t (in_d : t) (e : Exp.t) (rng : Range_el_opt.t) : t =
  match rng with
  | None -> make_empty ~n:0 ()
  | Some rng' -> 
    (match e with
   (** Exp.Lvar pvar -> Domain.alias_replace astate (Ident.to_string id) (Pvar.to_string pvar); *)
    | Exp.Var id -> 
      let out_d = make_empty ~n:2 () in
      let id_string = Ident.to_string id in
      let id_rng = Range_el_opt.to_range_el (find_opt in_d id_string) in
      let rng'' = Range_el.constrain rng' id_rng in
      let id_alias = alias_find_opt in_d (Ident.to_string id) in
      let rng_out =
        (match id_alias with
        | None -> rng''
        | Some id_alias' ->
          let alias_rng = Range_el_opt.to_range_el (find_opt in_d id_alias') in
          let rng_out = Range_el.constrain alias_rng rng'' in
          (add out_d id_alias' rng_out;
          rng_out)
        ) in
      add out_d id_string rng_out;
      out_d
    (** | Exp.Lvar pvar *)
    | _ -> make_empty ~n:0 ())
let print_only {ranges; aliases} : unit =
  let print_couple (k:string) (v:Range_el.t) =
    (Logging.progress "%s:" k; 
    match v with
    | Bottom -> Logging.progress "[] "
    | Range (l,u) -> Logging.progress "[%f, %f] " l u)
  in Hashtbl.iter print_couple ranges
let print (in_d : t) : t =
  (print_only in_d);
  in_d

let ( <= ) ~lhs ~rhs = 
  let ({ranges = l}, {ranges = r}) = (lhs, rhs) in
  let cmp (k:string) (v:Range_el.t) (cum:bool) =
    cum && Range_el_opt.(<=) (Some v) (Hashtbl.find_opt r k)
  in Hashtbl.fold cmp l true

(** TODO: combine aliases, if needed *)
let combine ({ranges = a; aliases = aa}:t) ({ranges = b}:t) ~combiner:combiner : t =
  let combine_els (k:string) (v:Range_el.t) (cum:ranges_t) =
    let replace_opt (tbl:ranges_t) (k:string) (v_opt:Range_el_opt.t) =
      match v_opt with
      | None -> tbl
      | Some v' -> Hashtbl.replace tbl k v'; tbl
    in replace_opt cum k (combiner (Some v) (Hashtbl.find_opt cum k))
  in let ab = Hashtbl.fold combine_els a b
  in {ranges = ab; aliases = aa}

let join = combine ~combiner:Range_el_opt.merge

(* constrain may be used when there is a Prune (a guard) *)
let constrain = combine ~combiner:Range_el_opt.constrain

let max_iters = 5          (** CHECK *)

let widen ~prev ~next ~num_iters = 
  if phys_equal prev next || Int.(num_iters >= max_iters) then prev
  else join prev next

let pp f _ = F.pp_print_string f "()"




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