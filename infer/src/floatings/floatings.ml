(* Copyright (c) 2019-present 5Kids *)

open! IStd
module F = Format
module L = Logging

module Payload = SummaryPayload.Make (struct
	type t = FloatingDomain.t

	let update_payloads resources_payload (payloads : Payloads.t) =
		{payloads with }

	let of_payloads {Payloads.} = 
end)

module TransferFunctions (CFG : ProcCfg.S) = struct
	module CFG = CFG
	module Domain = FloatingDomain

	type extras = 

	let exec_instr (astate : FoatingDomain.t) {ProcData.pdesc= _; tenv= _} _
		(instr : HilInstr.t) = 
		(* /IR/HilInstr.ml[i] *)
		match instr with
		| Assign (access_expr, AccessExpression rhs_access_expr, _loc) ->
        ResourceLeakDomain.assign
          (HilExp.AccessExpression.to_access_path access_expr)
          (HilExp.AccessExpression.to_access_path rhs_access_expr)
          astate

	let pp_session_name _node fmt = F.pp_print_string fmt "Floating checker"
end

module CFG = ProcCfg.Normal (* Exceptional *)

module Analyzer = LowerHil.MakeAbstractInterpreter (TransferFunctions (CFG))

(* let report_if_NaR = *)

(* Register in RegisterCheckers *)
let checker {Callbacks.summary; proc_desc; tenv} : Summary.t =
	let proc_data = ProcData.make proc_desc tenv () in
	match Analyzer.compute_post proc_data ~initial:FloatingDomain.initial with
	| Some post ->
		report_if_NaR post summary proc_data ;
		Payload.update_summary post summary
	| None ->
		L.(die InternalError)
			"Analyzer failed to compute post for %a" Typ.Procname.pp
			(Procdesc.get_proc_name proc_data.pdesc)