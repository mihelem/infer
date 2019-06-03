(*      InferNaL - Not a Linter     *)
(* Copyright (c) 2019-present 5Kids *)

open! IStd
module F = Format
module L = Logging

(** OPALT's job *)
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

  let print_instr (instr : Sil.instr) : Sil.instr =
    L.progress " %a \t--> " (Sil.pp_instr ~print_types:true Pp.text) instr;
    instr

  let print_range (rng : Domain.Range_el_opt.t) : Domain.Range_el_opt.t =
    (match rng with
    | Some (Domain.Range_el.Range (l,u)) -> L.progress " [%f,%f]" l u
    | Some (Domain.Range_el.Bottom) -> L.progress " []"
    | None -> L.progress " None");
    rng

  let rec apply_exp (astate : Domain.t) (e : Exp.t) : Domain.Range_el_opt.t =
  (**  let (ranges, aliases) = (Domain.get_ranges astate, Domain.get_aliases astate) in *)
    match e with
    | Exp.Var id -> 
      let id_string = Ident.to_string id in
      (match (Domain.find_opt astate id_string) with
      | None -> Domain.add astate id_string Domain.all_R; Some Domain.all_R
      | Some rng -> Some rng)
    | Exp.Const c -> (match c with
      | Const.Cfloat fl -> Some (Domain.Range_el.Range (fl,fl))
      | _ -> None)
    | Exp.Lvar pvar -> let pvar_string = Pvar.to_string pvar in
      (match (Domain.find_opt astate pvar_string) with
      | None -> L.progress "?!? Pvar not found in table!! ?!?";
          Domain.add astate pvar_string Domain.all_R; 
          Some Domain.all_R
      | Some rng -> Some rng)
    | Exp.BinOp (op, e1, e2) -> (match (op : Binop.t) with
      | PlusA _ -> Domain.Range_el_opt.plus (apply_exp astate e1) (apply_exp astate e2)
      | MinusA _ -> Domain.Range_el_opt.minus (apply_exp astate e1) (apply_exp astate e2)
      | Mult _ -> Domain.Range_el_opt.mult (apply_exp astate e1) (apply_exp astate e2)
      | Div -> Domain.Range_el_opt.div (apply_exp astate e1) (apply_exp astate e2)
      | _ -> apply_exp astate e1 ) (** TODO *)
    | _ -> None


(** Logical
      Binop: LAnd, LOr 
      Unop: LNot
    Arithmetic
      Binop: PlusA _, MinusA _, Mult _, Div
      Unop: Neg
    Comparison
      Binop: Le, Lt, Ge, Gt, Eq, Ne
*)
  module Constrain = struct
  
  (** Logical Normalization *)
    let n_bop (op : Binop.t) : Binop.t =
      let open Binop in
      match op with
      | LAnd -> LOr
      | LOr -> LAnd
      | Lt -> Ge
      | Le -> Gt
      | Gt -> Le
      | Ge -> Lt
      | Eq -> Ne
      | Ne -> Eq
      | _ -> op

    let rec p_form ?(ng=false) (e : Exp.t) : Exp.t =
      match (e, ng) with
      | (Exp.UnOp (Unop.LNot, en, _), ng) -> p_form en ~ng:(not ng)
      | (Exp.BinOp (op, e1, e2), false) -> Exp.BinOp (op, p_form e1, p_form e2)
      | (Exp.BinOp (op, e1, e2), true) -> Exp.BinOp (n_bop op, p_form e1 ~ng:ng, p_form e2 ~ng:ng)
      | _ -> e
    
  (** Arithmetic Normalization *)    
  (** Sound iff in SSA form, so each identifier is appearing once *)      
    let c_bop (op : Binop.t) : Binop.t =
      let open Binop in
      match op with
      | Lt -> Gt
      | Le -> Ge
      | Gt -> Lt 
      | Ge -> Le
      | _ -> op

    let is_c (op : Binop.t) : bool =
      let open Binop in
      match op with
      | Lt | Le | Ge | Gt | Div | MinusA _ -> false
      | _ -> true     (** true means also not interested in the property *)

    let do_binopt (op : Binop.t) (e1 : Exp.t) (e2 : Exp.t option) : Exp.t =
      match e2 with
      | None -> e1
      | Some e2' -> Exp.BinOp (op, e1, e2')

  (** (e1 aop e2) cop e  --> ...  *)
    let simpl_bin_lhs (cop : Binop.t) (aop : Binop.t) (e1 : Exp.t) (e2 : Exp.t) (e : Exp.t) : Exp.t option =
      let open Float in
      let f_zero = Exp.Const (Const.Cfloat 0.) in
      let f_nzero = Exp.Const (Const.Cfloat (-0.)) in
      match aop with
      | Binop.PlusA None -> Some 
        (Exp.BinOp (Binop.LAnd,
          Exp.BinOp (cop, e1,
            Exp.BinOp (Binop.MinusA None, e, e2)),
          Exp.BinOp (cop, e2,
            Exp.BinOp (Binop.MinusA None, e, e1))))
      | Binop.MinusA None -> Some
        (Exp.BinOp (Binop.LAnd,
          Exp.BinOp (cop, e1,
            Exp.BinOp (Binop.PlusA None, e, e2)),
          Exp.BinOp (c_bop cop, e2,
            Exp.BinOp (Binop.MinusA None, e1, e2))))
      | Binop.Mult None ->
        let e' e1 e2 =
          Exp.BinOp (Binop.LOr,
            Exp.BinOp (Binop.LAnd,
              Exp.BinOp (cop, e1, 
                Exp.BinOp (Binop.Div, e, e2)),
              Exp.BinOp (Binop.Ge, e2, f_zero)),
            Exp.BinOp (Binop.LAnd,
              Exp.BinOp (c_bop cop, e1, 
                Exp.BinOp (Binop.Div, e, e2)),
              Exp.BinOp (Binop.Le, e2, f_nzero ))) in Some
        (Exp.BinOp (Binop.LAnd, 
          e' e1 e2,
          e' e2 e1))
      | Binop.Div -> Some
        (Exp.BinOp (Binop.LAnd,
          Exp.BinOp (Binop.LOr,
            Exp.BinOp (Binop.LAnd,
              Exp.BinOp (cop, e1, 
                Exp.BinOp (Binop.Mult None, e, e2)),
              Exp.BinOp (Binop.Ge, e2, f_zero)),
            Exp.BinOp (Binop.LAnd,
              Exp.BinOp (c_bop cop, e1, 
                Exp.BinOp (Binop.Mult None, e, e2)),
              Exp.BinOp (Binop.Le, e2, f_nzero))),
          Exp.BinOp (Binop.LOr,
            Exp.BinOp (Binop.LAnd,
              Exp.BinOp (c_bop cop, e2, 
                Exp.BinOp (Binop.Div, e1, e)),
              Exp.BinOp (Binop.LOr,
                Exp.BinOp (Binop.LAnd,
                  Exp.BinOp (Binop.Ge, e, f_zero),
                  Exp.BinOp (Binop.Ge, e2, f_zero)),
                Exp.BinOp (Binop.LAnd,
                  Exp.BinOp (Binop.Le, e, f_nzero),
                  Exp.BinOp (Binop.Le, e2, f_nzero)))),
            Exp.BinOp (Binop.LAnd,
              Exp.BinOp (cop, e2, 
                Exp.BinOp (Binop.Div, e1, e)),
              Exp.BinOp (Binop.LOr,
                Exp.BinOp (Binop.LAnd,
                  Exp.BinOp (Binop.Ge, e, f_zero),
                  Exp.BinOp (Binop.Le, e2, f_nzero)),
                Exp.BinOp (Binop.LAnd,
                  Exp.BinOp (Binop.Le, e, f_nzero),
                  Exp.BinOp (Binop.Ge, e2, f_zero)))))))
      | _ -> None                

    let rec simpl_lhs (cop : Binop.t) (e1 : Exp.t) (e2 : Exp.t) : Exp.t option =
      match e1 with
      | Exp.UnOp (Unop.Neg, e1', tt) -> 
        simpl_lhs (c_bop cop) e1' (Exp.UnOp (Unop.Neg, e2, tt))
      | Exp.BinOp (bop, e1', e2') -> 
        simpl_bin_lhs cop bop e1' e2' e2
      | Exp.Var _ | Exp.Lvar _ | Exp.Const _ -> Some (Exp.BinOp (cop, e1, e2))
      | _ -> None       (** None identifying formats which we do not recognize, e.g. ((a<b)+c<7.) *)

  (** To be applied to positive form: after p_form *)
    let rec catch_cmp (e_o : Exp.t option) : Exp.t option =
      match e_o with
      | None -> None
      | Some e ->
        (match e with
        | Exp.BinOp (op, e1, e2) ->
          (let open Binop in
          match op with
          | Lt | Le | Gt | Ge | Eq | Ne ->
            (match e1 with
            | Exp.Var _ | Exp.Lvar _ | Exp.Const _ ->
              Some e
            | _ ->
              catch_cmp (simpl_lhs op e1 e2))
          | LAnd | LOr -> 
            (match (catch_cmp (Some e1), catch_cmp (Some e2)) with
            | (Some e1', Some e2') -> Some (Exp.BinOp (op, e1', e2'))
            | (None, Some e') | (Some e', None) -> Some e'
            | (None, None) -> None)
          | _ -> None)
        | _ -> None)

    let rec symmetrize (e : Exp.t) : Exp.t =
      match e with
      | Exp.BinOp (op, e1, e2) ->
        (let open Binop in
        match op with
        | Le | Lt | Ge | Gt | Eq | Ne ->
          Exp.BinOp (LAnd, e, Exp.BinOp (c_bop op, e2, e1))
        | LAnd | LOr -> Exp.BinOp (op, symmetrize e1, symmetrize e2)
        | _ -> e)               
      | Exp.UnOp (op, e', tt) -> 
        (match op with
        | Unop.LNot -> Exp.UnOp (op, symmetrize e', tt)
        | _ -> e)
      | _ -> e        (** By now I stay away from closures, casts, etc... *)

    let normalize (e : Exp.t) : Exp.t option =
      let ep = p_form e in
      let es = symmetrize ep in
      catch_cmp (Some es)

(** Sil.Prune (cond_e, loc, true_branch, kind) *)
    let rec to_ranges (in_d : Domain.t) (e : Exp.t) : Domain.t =
      match e with
      | Exp.BinOp (Binop.LAnd, e1, e2) -> 
        let in_d' = Domain.copy in_d in
        let in_d'' = Domain.constrain in_d' (to_ranges in_d e1) in
        to_ranges in_d'' e2
      | Exp.BinOp (Binop.LOr, e1, e2) -> Domain.merge (to_ranges in_d e1) (to_ranges in_d e2)
      | Exp.BinOp (Binop.Le, e1, e2) 
      | Exp.BinOp (Binop.Lt, e1, e2) ->
        let rng = Domain.Range_el_opt.open_left (apply_exp in_d e2) in
        Domain.id2t in_d e1 rng
      | Exp.BinOp (Binop.Ge, e1, e2)
      | Exp.BinOp (Binop.Gt, e1, e2) ->
        let rng = Domain.Range_el_opt.open_right (apply_exp in_d e2) in
        Domain.id2t in_d e1 rng
      | Exp.BinOp (Binop.Eq, e1, e2) ->
        let rng = apply_exp in_d e2 in
        Domain.id2t in_d e1 rng
      | Exp.BinOp (Binop.Ne, e1, e2) ->
        Domain.id2t in_d e1 (Some Domain.all_R)
      | _ -> Domain.make_empty ~n:0 ()

    let apply (in_d : Domain.t) (e : Exp.t) : Domain.t =
      let e_o = normalize e in
      match e_o with
      | None -> Domain.copy in_d
      | Some e' ->
        L.progress "%a => " (Sil.pp_exp_printenv ~print_types:true Pp.text) e';
        (* Domain.constrain (Domain.copy in_d) (Domain.print (to_ranges in_d e')) *)
        let e'' = Domain.print (to_ranges in_d e') in
        if Domain.(in_d <= e'') then Domain.constrain in_d e''
        else Domain.constrain (Domain.copy in_d) e''  (** TODO: not here... where to copy?! HELP! *)
  end
  
  (* Domain.t -> extras ProcData.t -> CFG.Node.t -> instr -> Domain.t
  type 'a t = {pdesc: Procdesc.t; tenv: Tenv.t; extras: 'a}  **)
  let exec_instr (astate : Domain.t) (extr : extras ProcData.t) (node : CFG.Node.t) (instr : Sil.instr) = 
    let state_ref = ref astate in
    let state_ref_ref = ref state_ref in
    ((match print_instr instr with
    | Sil.Load (id, e, t, loc) -> 
      (match print_range (apply_exp astate e) with
      | Some rng -> Domain.replace astate (Ident.to_string id) rng
      | None -> () );
      (match e with
      | Exp.Lvar pvar -> Domain.alias_replace astate (Ident.to_string id) (Pvar.to_string pvar);
        L.progress " :: %s alias of %s  " (Ident.to_string id) (Pvar.to_string pvar)
      | _ -> () )
    | Sil.Store (e1, t, e2, loc) ->
      (match e1 with
      | Exp.Lvar pvar -> 
        (match print_range (apply_exp astate e2) with
        | Some rng -> Domain.replace astate (Pvar.to_string pvar) rng
        | None -> ())
      | _ -> ())
    (** Prune: basic form, o.w. can use many Hashtbl then merge/constrain for each boolean op *)
    | Sil.Prune (cond_e, loc, true_branch, kind) -> 
    (**  L.progress " \n    IN :::: "; Domain.print_only (!(!state_ref_ref)); L.progress "\n"; *)
      state_ref_ref := ref (Constrain.apply astate cond_e); 
    (**  L.progress " \n   OUT :::: "; Domain.print_only (!(!state_ref_ref)) *)
    | Sil.Call _ -> ()  (** This is OPALT's job ^_^ *)
    | Metadata metadata -> state_ref_ref := ref (Domain.copy astate); ());
    L.progress "\n";
    !(!state_ref_ref))

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
    (** 
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