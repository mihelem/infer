(*  TODO : bisbarello, write your SIL printer here ? ^_^ **)
(*  UPDATE : starting for you  <:(  **)

open! IStd
module F = Format

module Domain =
	type t = unit

	let ( <= ) ~lhs:_ ~rhs:_ = assert false

	let join _a _b = assert false

	let widen ~prev:_ ~next:_ ~num_iters:_ = assert false

	let pp fmt () = F.fprintf fmt "SIL Printer: status is empty!"

	let initial = ()

	type summary = t
end

module TransferFunctions (CFG : ProcCfg.S) = struct
  module CFG = CFG
  module Domain = Domain

  type extras = unit

  (** Take an abstract state and instruction, produce a new abstract state *)
  let exec_instr (astate : ResourceLeakDomain.t) {ProcData.pdesc= _; tenv= _} _ instr =
  	let pe=Pp.text in
  		Logging.d_printfln_escaped "SILPrinter: %a@\n" (Sil.pp_instr ~print_types:true pe) instr

  	(*
    match instr with
    | Sil.Load (lhs_id, rhs_exp, typ, loc) 
    	-> Logging.d_printfln_escaped "SILPrinter: Load (%a,%a,%a\n" Typ.Procname.pp
          callee_pname ;
    | Sil.Store (lhs_exp, typ, rhs_exp, loc)->
    | Sil.Prune (exp, loc, go, kind) ->
    | Sil.Call ((ret_id, ret_typ), e_fun, arg_ts, loc, call_flags) ->
    | Sil.Metadata meta_instr -> **)

  let pp_session_name _node fmt = F.pp_print_string fmt "SIL Printer"
end

module CFG = ProcCfg.(OneInstrPerNode (Normal))

module Analyzer = AbstractInterpreter.MakeWTO (TransferFunctions (CFG))

(** Report an error when we have acquired more resources than we have released *)
let report _post _summary (_proc_data : unit ProcData.t) = ()

(* Callback for invoking the checker from the outside--registered in RegisterCheckers *)
let checker {Callbacks.summary; proc_desc; tenv} : Summary.t =
  let proc_data = ProcData.make proc_desc tenv () in
  match Analyzer.compute_post proc_data ~initial:Domain.initial with
  | Some post ->
      report post summary proc_data
  | None ->
      L.(die InternalError)
        "Analyzer failed to compute post for %a" Typ.Procname.pp
        (Procdesc.get_proc_name proc_data.pdesc)
