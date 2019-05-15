(* Copyright (c) 2019-present 5Kids *)

open! IStd
module F = Format

type range_el = 
	  range of float*float
	| bottom

type t = (string, range_el) Hashtbl.t

let ( <= ) lhs:range_el rhs:range_el = match (lhs, rhs) with
	  (bottom, _)		-> true
	| (range _, bottom)	-> false
	| (range (lhs_l, lhs_u), range (rhs_l, rhs_u))	-> (lhs_l >=. rhs_l) && (lhs_u <=. rhs_u)

let ( <= ) ~lhs:t ~rhs:t =

( <= ) rhs:5.6 lhs:345.

let join (a:t) (~b:t) = (min ,

let widen ~prev:_ ~next:_ ~num_iters:_ = 

let pp fmt () =

let initial =

let got_NaR =

type summary = t