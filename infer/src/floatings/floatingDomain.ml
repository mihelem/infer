(* Copyright (c) 2019-present 5Kids *)

open! IStd
module F = Format

type range_el = 
	| Range of float*float
	| Bottom

type t = (string, range_el) Hashtbl.t

let ( <= ) ~lhs:range_el ~rhs:range_el = 
	match (lhs, rhs) with
		| (Bottom, _)		-> true
		| (Range _, Bottom)	-> false
		| (Range (lhs_l, lhs_u), Range (rhs_l, rhs_u))	-> (lhs_l >=. rhs_l) && (lhs_u <=. rhs_u)

let ( <= ) ~lhs:(range_el option) ~rhs:(range_el option) =
	match (lhs, rhs) with
	| (None, _) | (_, None) -> true
	| (Some l, Some r) -> l <= r

let ( <= ) ~lhs:t ~rhs:t = 
	let cmp (bind:string*range_el) (cum:bool) =
		match bind with
		| (str, rng) -> cum && (rng <= Hashtbl.find_opt rhs str)
	in Hashtbl.fold cmp lhs true

let merge_r (a:range_el) (b:range_el) : range_el =
	match (a,b) with
	| (Bottom, x) | (x, Bottom) -> x
	| (Range (a_l, a_u), Range (b_l, b_u)) -> Range (min a_l b_l, max a_u b_u)
(* !!! XƏBƏRDARLIQ: min/max is not considering NaN !!! *)	

let merge_ro (a:range_el option) (b:range_el option) : (range_el option) =
	match (a,b) with
	| (None, b) -> b
	| (a, None) -> a
	| (Some a', Some b') -> Some (merge_r a' b')

let join (a:t) (b:t) = 
	let merge_els ((str:string), (rng_a:range_el)) (tbl:t) =
		let merge_maybe (tbl:t) (str:string) (rng:range_el option) =
			match rng with
			| None -> tbl
			| Some rng' -> Hashtbl.replace tbl str rng'; tbl
		in merge_maybe tbl str (merge_ro (Some rng_a) (Hashtbl.find_opt str))
	in Hashtbl.fold merge_els a b

let widen ~prev:_ ~next:_ ~num_iters:_ = 

let pp fmt () =

let initial:t = Hashtbl.create 100

type summary = t