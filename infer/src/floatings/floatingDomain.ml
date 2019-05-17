(* Copyright (c) 2019-present 5Kids *)

(*open! IStd
module F = Format
*)
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
	| (FP_nan, x) | (x, FP_nan) -> x=FP_nan 
	| (FP_zero, FP_zero) -> (copysign 1. a) = (copysign 1. b)
	| _ -> a=b

module Range_el = struct
	type t = 
		| Range of float*float
		| Bottom

	let ( <= ) (lhs:t) (rhs:t) : bool = 
		match (lhs, rhs) with
		| (Bottom, _)		-> true
		| (Range _, Bottom)	-> false
		| (Range (lhs_l, lhs_u), Range (rhs_l, rhs_u))	
			-> (eq_nan (min_nan lhs_l rhs_l) rhs_l) && (eq_nan (max_nan lhs_u rhs_u) rhs_u)
	
	let merge (a:t) (b:t) : t =
		match (a,b) with
		| (Bottom, x) | (x, Bottom) -> x
		| (Range (a_l, a_u), Range (b_l, b_u)) -> Range (min_nan a_l b_l, max_nan a_u b_u)
	(* !!! XƏBƏRDARLIQ: min/max is not considering NaN !!! *)	
end

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
end

type t = (string, Range_el.t) Hashtbl.t

let ( <= ) ~lhs ~rhs = 
	let cmp (str:string) (rng:Range_el.t) (cum:bool) =
		cum && Range_el_opt.((Some rng) <= Hashtbl.find_opt rhs str)
	in Hashtbl.fold cmp lhs true

let join (a:t) (b:t) : t = 
	let merge_els (str:string) (rng:Range_el.t) (cum:t) =
		let replace_opt (tbl:t) (str:string) (rng_opt:Range_el_opt.t) =
			match rng_opt with
			| None -> tbl
			| Some rng' -> Hashtbl.replace tbl str rng'; tbl
		in replace_opt cum str (Range_el_opt.merge (Some rng) (Hashtbl.find_opt cum str))
	in Hashtbl.fold merge_els a b

let widening_threshold = 5

let widen ~prev ~next ~num_iters = 
	if num_iters<widening_threshold 
		then join prev next
	else next

let pp fmt () = ()

let initial:t = Hashtbl.create 100

type summary = t