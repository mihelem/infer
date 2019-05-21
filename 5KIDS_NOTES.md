# Useful Info for 5Kids 

**Add SCHEMES of what you find technically useful to this file**

**CFG**: [global Control Flow Graph](infer/src/IR/Cfg.ml) :: nodes=[SIL](infer/src/IR/Sil.ml) instructions

**[procdesc](infer/src/IR/Procdesc.ml)**:  :: [CFG of procedure](infer/src/absint/ProcCfg.ml) + [signature + annotations ... ](infer/src/absint/ProcData.ml)  __ procname may correspond to multiple procdesc's after resolution !!! (ProcData: container with proc description + extras: computed before analysis begin, accessible from transfer functions; e.g. save info from [prior analysis](infer/src/backend/preanal.ml)

**[Expressions](infer/src/IR/Exp.ml)** :: literals, program variables [Pvar](infer/src/IR/Pvar.ml), temp variables [Ident](infer/src/IR/Ident.ml), [info in type environment](infer/src/IR/Tenv.ml) 

**[Instructions](infer/src/IR/Instrs.ml)**:  :: Load, Store, Prune/assume, Call

[Typ](sledge/src/llair/typ.ml)


The Type for Program Variables is defined by the following struct:

```OCaml
(** Pvar.ml *)
(** Names for program variables. *)
type t = {pv_hash: int; pv_name: Mangled.t; pv_kind: pvar_kind} [@@deriving compare]
```

where 
```OCaml
(** Kind of global variables *)
type pvar_kind =
  | Local_var of Typ.Procname.t  (** local variable belonging to a function *)
  | Callee_var of Typ.Procname.t  (** local variable belonging to a callee *)
  | Abduced_retvar of Typ.Procname.t * Location.t
      (** synthetic variable to represent return value *)
  | Abduced_ref_param of Typ.Procname.t * int * Location.t
      (** synthetic variable to represent param passed by reference *)
  | Global_var of
      { translation_unit: translation_unit
      ; is_constexpr: bool (* is it compile constant? *)
      ; is_ice: bool (* is it integral constant expression? *)
      ; is_pod: bool
      ; is_static_local: bool
      ; is_static_global: bool }  (** global variable *)
  | Seed_var  (** variable used to store the initial value of formal parameters *)
[@@deriving compare]
```

where, in __Typ.ml__, in module Procname, we have the definition
```OCaml
  (** Type of procedure names. *)
  type t =
    | Java of Java.t
    | C of C.t
    | Linters_dummy_method
    | Block of Block.t
    | ObjC_Cpp of ObjC_Cpp.t
    | WithBlockParameters of t * Block.block_name list
  [@@deriving compare]
 ```

 ### How to call the checker

 In registerCheckers.ml you find 

 ```OCaml
 type callback_fun =
  | Procedure of Callbacks.proc_callback_t
  | DynamicDispatch of Callbacks.proc_callback_t
  | Cluster of Callbacks.cluster_callback_t

type callback = callback_fun * Language.t

type checker = {name: string; active: bool; callbacks: callback list}
```

and in callbacks.ml you find

```OCaml
type proc_callback_args =
  { get_procs_in_file: Typ.Procname.t -> Typ.Procname.t list
  ; tenv: Tenv.t
  ; integer_type_widths: Typ.IntegerWidths.t
  ; summary: Summary.t
  ; proc_desc: Procdesc.t
  ; exe_env: Exe_env.t }

type proc_callback_t = proc_callback_args -> Summary.t
```

and in Summary.ml you find

```OCaml
type t =
  { payloads: Payloads.t
  ; sessions: int ref
  ; stats: Stats.t
  ; status: Status.t
  ; proc_desc: Procdesc.t
  ; err_log: Errlog.t }
```

so, forgetting about the differences between Procedure, DynamicDispatch, Cluster, to describe a callback we need a specification of the programming language, preceded by a function from the current __context__ to the final Summary, which should be the result of applying the checker to a single procedure. At least, maybe?!?
Let's see an example from registerCheckers.ml:
```OCaml
type checker = {name: string; active: bool; callbacks: callback list}

let all_checkers =
	[
	(** ... *)
	{ name= "liveness"
    ; active= Config.liveness
    ; callbacks= [(Procedure Liveness.checker, Language.Clang)] }
    (** ... *)
    ]
```

So in Config.ml we determine if the checker is active, languages are choosen from the ones in Language.ml, and if we go back to our dear liveness.ml we now know that the last defined function, check, has type `proc_callback_args -> Summary.t`, so let's go back to liveness.ml:

```OCaml
let checker {Callbacks.tenv; summary; proc_desc} : Summary.t =
```

so, to begin with, many infos are not used by liveness checker. Then,

```OCaml
let proc_data = ProcData.make_default proc_desc tenv in
```
in [ProcData.ml](infer/src/absint/ProcData.ml) we find the corresponding 

```OCaml
let empty_extras = () 
let make pdesc tenv extras = {pdesc; tenv; extras}
let make_default pdesc tenv = make pdesc tenv empty_extras
```

so `proc_data = {proc_desc;tenv;()}`; then, next line:

```OCaml
  let captured_by_ref_invariant_map = get_captured_by_ref_invariant_map proc_desc proc_data in
```

where 

```OCaml
module CapturedByRefTransferFunctions (CFG : ProcCfg.S) = struct
  module CFG = CFG
  module Domain = VarSet

  type extras = ProcData.no_extras

  let exec_instr astate _ _ instr =
    List.fold (Sil.exps_of_instr instr)
      ~f:(fun acc exp ->
        Exp.fold_captured exp
          ~f:(fun acc exp ->
            match Exp.ignore_cast exp with
            | Exp.Lvar pvar ->
                (* captured by reference, add *)
                Domain.add (Var.of_pvar pvar) acc
            | _ ->
                (* captured by value or init-capture, skip *)
                acc )
          acc )
      ~init:astate


  let pp_session_name _node fmt = F.pp_print_string fmt "captured by ref"
end

module CapturedByRefAnalyzer =
  AbstractInterpreter.MakeRPO (CapturedByRefTransferFunctions (ProcCfg.Exceptional))

let get_captured_by_ref_invariant_map proc_desc proc_data =
  let cfg = ProcCfg.Exceptional.from_pdesc proc_desc in
  CapturedByRefAnalyzer.exec_cfg cfg proc_data ~initial:VarSet.empty
```

so what is `captured_by_ref_invariant_map`? First you build your `cfg` from your proces description by `ProcCfg.Exceptional.from_pdesc`, then you apply to it the `CapturedByRefAnalyzer` by `CapturedByRefAnalyzer.exec_cfg cfg proc_data ~initial:VarSet.empty`. Actually, `CapturedByRefAnalyzer` is built by the framework `AbstractInterpreter` given the specification written in the (parametric with as parameter a Process CFG) module `CapturedByRefTransferFunctions`


Looking at `CapturedByRefTransferFunctions.exec_instr` you see in particular how they extract from `instr` the Sil expressions `(Sil.exps_of_instr instr)` and then how they deal with the expressions themselves, e.g. `Exp.fold_captured`, `Exp.ignore_cast`... ). So now we know how to extract expressions from instructions, let's have a look at [Exp.ml](infer/src/IR/Exp.ml)
