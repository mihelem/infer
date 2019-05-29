(* Copyright (c) 2019-present 5Kids *)

open! IStd
module F = Format
module L = Logging
module Hashtbl = Caml.Hashtbl

(**
module Payload = SummaryPayload.Make (struct
  type t = FloatingDomain.summary

  let update_payloads resources_payload (payloads : Payloads.t) =
    {payloads with }

  let of_payloads {Payloads.} = 
end) 
module Payload = SummaryPayload.Make (struct
  type t = ResourceLeakDomain.summary

  let update_payloads resources_payload (payloads : Payloads.t) =
    {payloads with lab_resource_leaks= Some resources_payload}


  let of_payloads {Payloads.lab_resource_leaks} = lab_resource_leaks
end)
*)

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
  let rec apply_exp (astate : Domain.t) (e : Exp.t) : Domain.Range_el_opt.t =
    match e with
    | Exp.Var id -> 
      let id_string = Ident.to_string id in
      (match (Domain.find_opt astate id_string) with
      | None -> Domain.add astate id_string Domain.all_R; Some Domain.all_R
      | Some rng -> Some rng)
    | Exp.Const c -> (match c with
      | Const.Cfloat fl -> Some (Domain.Range_el.Range (fl,fl))
      | _ -> None)
    | BinOp (op, e1, e2) -> (match (op : Binop.t) with
      | PlusA _ -> Domain.Range_el_opt.plus (apply_exp astate e1) (apply_exp astate e2)
      | MinusA _ -> Domain.Range_el_opt.minus (apply_exp astate e1) (apply_exp astate e2)
      | Mult _
      | Div
      | _ -> apply_exp astate e1 ) (** TODO *)
    | _ -> None
  
  let exec_instr (astate : Domain.t) (extr : extras ProcData.t) (node : CFG.Node.t) instr = 
    match (instr : Sil.instr) with
    | Sil.Load (id, e, t, loc) -> 
      (match (apply_exp astate e) with
      | Some rng -> Domain.replace astate (Ident.to_string id) rng; astate(* Ident.to_string id *)
      | None -> astate)
    | _ -> astate
    (** | Sil.Store (e1, t, e2, loc)
    | Sil.Prune (cond_e, loc, true_branch, kind)
    | Sil.Call ((id, id_t), e, arg_ts, loc, cf)
    | Sil.Metadata metadata -> astate *)
(**
      match instr with
      | Load (id, e, t, loc) ->
          F.fprintf f "LOAD %a=*%a:%a [%a]" 
            Ident.pp id 
            (pp_exp_printenv ~print_types pe) e 
            (pp_typ pe0) t
            Location.pp loc
      | Store (e1, t, e2, loc) ->
          F.fprintf f "STORE *%a:%a=%a [%a]"
            (pp_exp_printenv ~print_types pe) e1
            (pp_typ pe0) t
            (pp_exp_printenv ~print_types pe) e2 
            Location.pp loc
      | Prune (cond, loc, true_branch, _) ->
          F.fprintf f "PRUNE(%a, %b); [%a]" 
            (pp_exp_printenv ~print_types pe) cond 
            true_branch
            Location.pp loc
      | Call ((id, _), e, arg_ts, loc, cf) ->
          F.fprintf f "CALL " ;
          F.fprintf f "%a=" Ident.pp id ;
          F.fprintf f "%a(%a)%a [%a]" 
            (pp_exp_printenv ~print_types pe) e
            (Pp.comma_seq (pp_exp_typ pe)) arg_ts 
            CallFlags.pp cf 
            Location.pp loc
      | Metadata metadata ->
          pp_instr_metadata pe0 f metadata )

let rec pp_ pe pp_t f e =
  let pp_exp = pp_ pe pp_t in
  let print_binop_stm_output e1 op e2 =
    match (op : Binop.t) with
    | Eq | Ne | PlusA _ | Mult _ ->
        F.fprintf f "(%a %s %a)" pp_exp e2 (Binop.str pe op) pp_exp e1
    | Lt ->
        F.fprintf f "(%a %s %a)" pp_exp e2 (Binop.str pe Gt) pp_exp e1
    | Gt ->
        F.fprintf f "(%a %s %a)" pp_exp e2 (Binop.str pe Lt) pp_exp e1
    | Le ->
        F.fprintf f "(%a %s %a)" pp_exp e2 (Binop.str pe Ge) pp_exp e1
    | Ge ->
        F.fprintf f "(%a %s %a)" pp_exp e2 (Binop.str pe Le) pp_exp e1
    | _ ->
        F.fprintf f "(%a %s %a)" pp_exp e1 (Binop.str pe op) pp_exp e2
  in
  match (e : t) with
  | Var id ->
      Ident.pp f id
  | Const c ->
      (Const.pp pe) f c
  | Cast (typ, e) ->
      F.fprintf f "(%a)%a" pp_t typ pp_exp e
  | UnOp (op, e, _) ->
      F.fprintf f "%s%a" (Unop.to_string op) pp_exp e
  | BinOp (op, Const c, e2) when Config.smt_output ->
      print_binop_stm_output (Const c) op e2
  | BinOp (op, e1, e2) ->
      F.fprintf f "(%a %s %a)" pp_exp e1 (Binop.str pe op) pp_exp e2
  | Exn e ->
      F.fprintf f "EXN %a" pp_exp e
  | Closure {name; captured_vars} ->
      if List.is_empty captured_vars then F.fprintf f "(%a)" pp_exp (Const (Cfun name))
      else
        F.fprintf f "(%a,%a)" pp_exp (Const (Cfun name))
          (Pp.comma_seq (pp_captured_var pe pp_t))
          captured_vars
  | Lvar pv ->
      Pvar.pp pe f pv
  | Lfield (e, fld, _) ->
      F.fprintf f "%a.%a" pp_exp e Typ.Fieldname.pp fld
  | Lindex (e1, e2) ->
      F.fprintf f "%a[%a]" pp_exp e1 pp_exp e2
  | Sizeof {typ; nbytes; dynamic_length; subtype} ->
      let pp_len f l = Option.iter ~f:(F.fprintf f "[%a]" pp_exp) l in
      let pp_size f size = Option.iter ~f:(Int.pp f) size in
      let pp_if b pp label f v = if b then F.fprintf f ";%s=%a" label pp v in
      let pp_if_some pp_opt label f opt = pp_if (Option.is_some opt) pp_opt label f opt in
      let subt_s = F.asprintf "%a" Subtype.pp subtype in
      F.fprintf f "sizeof(t=%a%a%a%a)" pp_t typ (pp_if_some pp_size "nbytes") nbytes
        (pp_if_some pp_len "len") dynamic_length
        (pp_if (not (String.equal "" subt_s)) Subtype.pp "sub_t")
        subtype
*)

  let pp_session_name _node fmt = F.pp_print_string fmt "Floatings checker"
end
(* Just to check the framework interface! **)
module CFG = ProcCfg.OneInstrPerNode (ProcCfg.Normal)

module Analyzer = AbstractInterpreter.MakeWTO (TransferFunctions (CFG))

(* let report_if_NaR = *)

(* Register in RegisterCheckers *)
let checker (args:Callbacks.proc_callback_args) : Summary.t =
  match 
    Analyzer.compute_post 
      (ProcData.make_default args.proc_desc args.tenv) 
      ~initial:FloatingDomain.initial with
  | None | Some _ -> args.summary


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