(*      InferNaL - Not a Linter     *)
(* Copyright (c) 2019-present 5Kids *)

open! IStd

module Hashtbl = Caml.Hashtbl

include AbstractDomain.S  (* Why? *)

(** type t *)

(** val got_NaR : t -> bool *)

module Range_el : sig
  type t = Range of float * float | Bottom
  val ( <= ) : t -> t -> bool
  val merge : t -> t -> t
  val constrain : t -> t -> t
end

val all_R : Range_el.t

module Range_el_opt : sig
  type t = Range_el.t option
  val ( <= ) : t -> t -> bool
  val merge : t -> t -> t
  val constrain : t -> t -> t
  val plus : t -> t -> t
  val minus : t -> t -> t
  val mult : t -> t -> t
  val div : t -> t -> t
  val open_left : t -> t
  val open_right : t -> t
end

type ranges_t = (string, Range_el.t) Hashtbl.t
type aliases_t = (string, string) Hashtbl.t
(** type t = {ranges : ranges_t; aliases : aliases_t} *)
val get_ranges : t -> ranges_t
val get_aliases : t -> aliases_t
val find_opt : t -> string -> Range_el_opt.t
val add : t -> string -> Range_el.t -> unit
val replace : t -> string -> Range_el.t -> unit
val alias_find_opt : t -> string -> string option
val alias_add : t -> string -> string -> unit
val alias_replace : t -> string -> string -> unit
val copy : t -> t

type summary = t

val (<=) : lhs:t -> rhs:t -> bool
val join : t -> t -> t
val constrain : t -> t -> t
val widen : prev:t -> next:t -> num_iters:int -> t
val initial : t