(**  TODO : bisbarello, write your HIL printer here ? ^_^ **)
(**  UPDATE : starting for you  <:(  **)

open! IStd
module F = Format

module EmptyDomain = struct
	type t = unit

	let ( <= ) ~lhs:_ ~rhs:_ = false

	let join _a _b = _a

	let widen ~prev ~next:_ ~num_iters:_ = prev

	let pp fmt () = F.fprintf fmt "HIL Printer: status is empty!"

	let initial = ()

	type summary = t
end

module TransferFunctions (CFG : ProcCfg.S) = struct
  module CFG = CFG
  module Domain = EmptyDomain

  type extras = unit

  (** Take an abstract state and instruction, produce a new abstract state *)
  let exec_instr _ _ _ (instr : HilInstr.t) =
  	Logging.progress "HILPrinter: %a@\n" HilInstr.pp instr

  	(*
    match instr with
    | Sil.Load (lhs_id, rhs_exp, typ, loc) 
    	-> Logging.d_printfln_escaped "SILPrinter: Load (%a,%a,%a\n" Typ.Procname.pp
          callee_pname ;
    | Sil.Store (lhs_exp, typ, rhs_exp, loc)->
    | Sil.Prune (exp, loc, go, kind) ->
    | Sil.Call ((ret_id, ret_typ), e_fun, arg_ts, loc, call_flags) ->
    | Sil.Metadata meta_instr -> **)

  let pp_session_name _node fmt = F.pp_print_string fmt "HIL Printer"
end

module CFG = ProcCfg.OneInstrPerNode (ProcCfg.Normal)

module Analyzer = LowerHil.MakeAbstractInterpreter (TransferFunctions (CFG))

(* Callback for invoking the checker from the outside--registered in RegisterCheckers *)
let checker (args:Callbacks.proc_callback_args) : Summary.t =
  match Analyzer.compute_post (ProcData.make args.proc_desc args.tenv ()) ~initial:EmptyDomain.initial with
  | None | Some _ -> args.summary
