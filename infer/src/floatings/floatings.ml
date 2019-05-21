(* Copyright (c) 2019-present 5Kids *)

(** functor that makes it easy to write a basic abstract interpretation checker by lifting
    a type, comparison function, reporting function, and exec function into an analyzer *)

module type Spec = sig
  (** what state do you want to propagate? *)
  type t

  val initial : t
  (** implement the state the analysis should start from here *)



  val report : t -> Location.t -> Typ.Procname.t -> unit
  (** log errors here.
      input is a state, location where the state occurs in the source, and the current procedure.
  *)

  val compare : t -> t -> int
end

module type S = sig
  val checker : Callbacks.proc_callback_t
  (** add YourChecker.checker to registerCallbacks.ml to run your checker *)
end

module Make (Spec : Spec) : S = struct
  (* powerset domain over Spec.t *)
  module Domain = struct
    include AbstractDomain.FiniteSet (struct
      type t = Spec.t

      let compare = Spec.compare

      let pp _ _ = ()
    end)

    let widen ~prev ~next ~num_iters =
      let iters_befor_timeout = 1000 in
      (* failsafe for accidental non-finite height domains *)
      if num_iters >= iters_befor_timeout then
        L.(die InternalError)
          "Stopping analysis after 1000 iterations without convergence. Make sure your domain is \
           finite height."
      else widen ~prev ~next ~num_iters
  end

  module TransferFunctions (CFG : ProcCfg.S) = struct
    module CFG = CFG
    module Domain = Domain

    type extras = ProcData.no_extras

    let exec_instr astate_set proc_data node instr =
      let node_kind = CFG.Node.kind node in
      let pname = Procdesc.get_proc_name proc_data.ProcData.pdesc in
      Domain.fold
        (fun astate acc ->
          Domain.add (Spec.exec_instr astate instr node_kind pname proc_data.ProcData.tenv) acc )
        astate_set Domain.empty


    let pp_session_name _node fmt = F.pp_print_string fmt "simple checker"
  end

  module Analyzer = AbstractInterpreter.MakeRPO (TransferFunctions (ProcCfg.Exceptional))

  let checker {Callbacks.proc_desc; tenv; summary} : Summary.t =
    let proc_name = Procdesc.get_proc_name proc_desc in
    let nodes = Procdesc.get_nodes proc_desc in
    let do_reporting node_id state =
      let astate_set = state.AbstractInterpreter.State.post in
      if not (Domain.is_empty astate_set) then
        (* should never fail since keys in the invariant map should always be real node id's *)
        let node =
          List.find_exn
            ~f:(fun node -> Procdesc.Node.equal_id node_id (Procdesc.Node.get_id node))
            nodes
        in
        Domain.iter
          (fun astate -> Spec.report astate (ProcCfg.Exceptional.Node.loc node) proc_name)
          astate_set
    in
    let inv_map =
      Analyzer.exec_pdesc (ProcData.make_default proc_desc tenv) ~initial:Domain.empty
    in
    Analyzer.InvariantMap.iter do_reporting inv_map ;
    summary
end

(* END **)

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

	type extras = ProcData.no_extras

	(* val exec_instr : t -> Sil.instr -> Procdesc.Node.nodekind -> Typ.Procname.t -> Tenv.t -> t
	   input is the previous state, current instruction, current node kind, current procedure and
      type environment.
	**)
	(* Domain.t -> extras ProcData.t -> CFG.Node.t -> instr -> Domain.t
	astate _ _ instr
	type 'a t = {pdesc: Procdesc.t; tenv: Tenv.t; extras: 'a}  **)
	let exec_instr (astate : FoatingDomain.t) {ProcData.pdesc= _; tenv= _} node instr = 
		match instr with
		| Sil.Load
		| Sil.Store

	let pp_session_name _node fmt = F.pp_print_string fmt "Floatings checker"
end
(* Naive useless approach, just to check the framework interface! **)
module CFG = ProcCfg.(OneInstrPerNode (Normal))

module Analyzer = AbstractInterpreter.MakeWTO (TransferFunctions (CFG))


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


(* module CFG = ProcCfg.Normal **)
(*
module Analyzer = LowerHil.MakeAbstractInterpreter (TransferFunctions (CFG))
module CheckerAnalyzer = AbstractInterpreter.MakeRPO (TransferFunctions (CheckerMode) (CFG))
module CapturedByRefAnalyzer =
  AbstractInterpreter.MakeRPO (CapturedByRefTransferFunctions (ProcCfg.Exceptional))
**)
		(* (instr : HilInstr.t) = *)
		(* /IR/HilInstr.ml[i] *)
		(* match instr with
		| Assign (access_expr, AccessExpression rhs_access_expr, _loc) ->
        ResourceLeakDomain.assign
          (HilExp.AccessExpression.to_access_path access_expr)
          (HilExp.AccessExpression.to_access_path rhs_access_expr)
          astate *)