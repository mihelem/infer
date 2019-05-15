(* Copyright (c) 2019-present 5Kids *)

open! IStd

include AbstractDomain.S	(* Why? *)

val initial : t

val got_NaR : t -> bool

type summary = t