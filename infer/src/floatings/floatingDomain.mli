(*      InferNaL - Not a Linter     *)
(* Copyright (c) 2019-present 5Kids *)

open! IStd
open! Float

include AbstractDomain.S  (* Why? *)

(* val find_opt : ('a, 'b) Hashtbl.t -> 'a -> 'b option *)

(** type t *)
val initial : t

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

val find_opt : t -> string -> Range_el_opt.t
val add : t -> string -> Range_el.t -> unit
val replace : t -> string -> Range_el.t -> unit

type summary
val (<=) : lhs:t -> rhs:t -> bool
