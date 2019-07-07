(*      InferNaL - Not a Linter     *)
(* Copyright (c) 2019-present 5Kids *)
(* MAYDO                            *)
(* - Rounding mode                  *)
(* - Fix then diff btw < and <= etc *)
(* - Fix Widen                      *)

open! IStd

module F = Format
module L = Logging
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
    | (None, _) -> false
    | (_, None) -> true
    | (Some l, Some r) -> Range_el.(l <= r)
  
  let merge (a:t) (b:t) : t =
    match (a,b) with
    | (None, _) -> None
    | (_, None) -> None
    | (Some a', Some b') -> Some (Range_el.merge a' b')

  let constrain (base:t) (constr:t) : t =
    match (base,constr) with
    | (None, constr) -> constr
    | (base, None) -> base
    | (Some base', Some constr') -> Some (Range_el.constrain base' constr')
(** Naive approach, again... Purpose: testing the framework! *)
(** TODO: implement the table from Bagnara's paper (C bindings) *)
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
let replace_opt {ranges = tbl} k v_opt = 
  match v_opt with
  | None -> ()
  | Some v -> Hashtbl.replace tbl k v
let remove d k = Hashtbl.remove d.ranges k; Hashtbl.remove d.aliases k
let alias_find_opt {aliases = tbl} k = Hashtbl.find_opt tbl k
let alias_add {aliases = tbl} k v = Hashtbl.add tbl k v
let alias_replace {aliases = tbl} k v = Hashtbl.replace tbl k v
let copy {ranges; aliases} = {ranges = Hashtbl.copy ranges; aliases = Hashtbl.copy aliases}
let initial:t = {ranges = Hashtbl.create 100; aliases = Hashtbl.create 100}
let empty_d ?(n = 10) _ : t = {ranges = Hashtbl.create n; aliases = Hashtbl.create n}
let make_empty ?(n = 10) _ : t = copy (empty_d ~n:n ())
let create (n_r:int) (n_a:int) : t = {ranges=Hashtbl.create n_r; aliases=Hashtbl.create n_a}
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
    (Logging.progress "%s∈" k; 
    match v with
    | Bottom -> Logging.progress "[] "
    | Range (l,u) -> Logging.progress "[%f, %f] " l u) in
  Logging.progress "\n\tAState § "; 
  Hashtbl.iter print_couple ranges(*; 
  Logging.progress " where ";
  let print_alias (k:string) (alias:string) =
    Logging.progress " %s<->%s" k alias in
  Hashtbl.iter print_alias aliases*)
let print (in_d : t) : t =
  (print_only in_d);
  in_d


let ( <= ) ~lhs ~rhs = 
  let ({ranges = l}, {ranges = r}) = (lhs, rhs) in
  let cmp (k:string) (v:Range_el.t) (cum:bool) =
    cum && Range_el_opt.(<=) (Hashtbl.find_opt l k) (Some v) in
  Hashtbl.fold cmp r true

(** TODO: combine aliases, if needed *)
let combine_copy (a:t) (b:t) ~combiner:combiner : t =
  let result = create ((Hashtbl.length a.ranges)+(Hashtbl.length b.ranges)) ((Hashtbl.length a.aliases)+(Hashtbl.length b.aliases)) in
  let replace_opt (tbl : ranges_t) (k : string) (v_opt : Range_el_opt.t) =
    match v_opt with
    | None -> ()
    | Some v -> Hashtbl.replace tbl k v in
  let iter_step (k:string) (v:Range_el.t) ~lookup_tbl =
    replace_opt result.ranges k (combiner (Some v) (Hashtbl.find_opt lookup_tbl k)) in
  Hashtbl.iter (iter_step ~lookup_tbl:b.ranges) a.ranges;
  Hashtbl.iter (iter_step ~lookup_tbl:a.ranges) b.ranges;
  Hashtbl.iter (fun k al -> Hashtbl.replace result.aliases k al) a.aliases;
  Hashtbl.iter (fun k al -> Hashtbl.replace result.aliases k al) b.aliases;
  result

let combine ({ranges = a; aliases = aa}:t) ({ranges = b; aliases = _ba}:t) ~combiner:combiner : t =
  let f k rng ~tbl1 ~tbl2 =
    let v = combiner (Some rng) (Hashtbl.find_opt tbl2 k) in
    match v with
    | None -> Hashtbl.remove tbl1 k
    | Some v' -> Hashtbl.replace tbl1 k v' in
  Hashtbl.iter (f ~tbl1:a ~tbl2:a) b;
  Hashtbl.iter (f ~tbl1:a ~tbl2:b) a;
  {ranges=a;aliases=aa}

let merge = combine_copy ~combiner:Range_el_opt.merge
let merge_inplace = combine ~combiner:Range_el_opt.merge
(* constrain may be used when there is a Prune (a guard) *)
let constrain = combine_copy ~combiner:Range_el_opt.constrain
let constrain_inplace = combine ~combiner:Range_el_opt.constrain

let join a b = 
  L.progress "  JOIN\n";print_only a;L.progress " JOIN ";print_only b;L.progress " = "; 
  let ab = print (merge a b) in
  L.progress "\n"; ab

let widen_to_infty ~prev ~next =
  let ab = merge prev next in
  let f k rng =
    let r_ab = find_opt ab k in
    let open Range_el_opt in
    ((if not ((open_right r_ab) <= (open_right (Some rng))) then
      replace_opt ab k (open_left r_ab));
    (if not ((open_left r_ab) <= (open_left (Some rng))) then
      replace_opt ab k (open_right r_ab))) in
  Hashtbl.iter f prev.ranges;
  Logging.progress "\tTO INFTY";print_only ab;Logging.progress "\n";ab

let max_local_iters = 3
let max_iters = 5          (** CHECK *)
(** MAYDO: fix the diverging widening *)
let widen ~prev ~next ~num_iters = 
  Logging.progress "\n  WIDEN";
  if phys_equal prev next || Int.(num_iters >= max_iters) then 
    (Logging.progress " STOPPED after %d/%d iterations\n " num_iters max_iters; prev)
  else 
    (Logging.progress"\n";
    match num_iters%max_local_iters with
    | 0 -> widen_to_infty ~prev ~next
    | _ -> join prev next)
    
let pp f _ = F.pp_print_string f "()"

let pp_summary f {ranges;aliases=_aliases} = 
  let pp_k_rng k rng =
  (F.fprintf f "%s:" k;
  let open Range_el in
  match rng with
  | Bottom -> F.fprintf f "[] "
  | Range (l,u) -> F.fprintf f "[%f, %f] " l u) in
  Hashtbl.iter pp_k_rng ranges