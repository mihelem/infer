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
__@bisbarello: as you were saying, with `let rec pp_ pe pp_t f e =` + all the rest we now should be able to print everything__

But first, let's get a look at `AbstractInterpreter.ml`; first of all, about fixpoint calculation of recursive calls, we set the global widening threshold in `Config.ml`, by `let max_widens = 10000`. Well... 10000 seems fine.
Then, what is the `Status` in `AbstractInterpreter.ml`?

```OCaml
module State = struct
  type 'a t = {pre: 'a; post: 'a; visit_count: VisitCount.t}

  let pre {pre} = pre

  let post {post} = post
end
```

mmh, `pre`, `post`... it should remind you about biabduction. 

What about the ordering in which we analyse the global CFG, so the procedures?

```OCaml
module MakeRPO (T : TransferFunctions.SIL) =
  MakeWithScheduler (Scheduler.ReversePostorder (T.CFG)) (T)
module MakeWTO (T : TransferFunctions.SIL) = MakeUsingWTO (T)
```

WTO is Weak Topological Ordering. In a compositional setting, both choices are meaningful. But suppose we want to break modularity/compositionality, as we were discussing, just to do it and ... nothing more. Then, we'd better go to `Scheduler.ml`, just to discover that there is, by now, only a Reverse Post Order Scheduler; so, here is where we should put our hands in case we really wanted to change scheduling.

`module AbstractInterpreterCommon (TransferFunctions : TransferFunctions.SIL)`

In TransferFunctions.ml we find 

```OCaml
module type S = sig
  module CFG : ProcCfg.S

  module Domain : AbstractDomain.S

  type extras

  type instr

  val exec_instr : Domain.t -> extras ProcData.t -> CFG.Node.t -> instr -> Domain.t

  val pp_session_name : CFG.Node.t -> Format.formatter -> unit
end

module type SIL = sig
  include S with type instr := Sil.instr
end
```

Recall `let exec_instr astate _ _ instr = ` in liveness.ml: here we have its signature; for instr, we may choose between SIL or HIL, for HIL: 
```OCaml
module type HIL = sig
  include S with type instr := HilInstr.t
end
```

Now we have an almost complete picture of our transfer functions... why we define them, and how we have to do it.

What about **nodes**? In ProcCfg.ml we find
```OCaml
module type Node = sig
  type t

  type id

  val kind : t -> Procdesc.Node.nodekind

  val id : t -> id

  val hash : t -> int

  val loc : t -> Location.t

  val underlying_node : t -> Procdesc.Node.t

  val of_underlying_node : Procdesc.Node.t -> t

  val compare_id : id -> id -> int

  val pp_id : F.formatter -> id -> unit

  module IdMap : PrettyPrintable.PPMap with type key = id

  module IdSet : PrettyPrintable.PPSet with type elt = id
end
```
So you see that the underlying definitions are in Procdesc.ml; actually, there we find the module Node
```OCaml
module NodeKey = struct
  type t = Caml.Digest.t

  let to_string = Caml.Digest.to_hex

  let compute node ~simple_key ~succs ~preds =
    let v =
      (simple_key node, List.rev_map ~f:simple_key succs, List.rev_map ~f:simple_key preds)
    in
    Utils.better_hash v


  let of_frontend_node_key = Utils.better_hash
end

module Node = struct
  type id = int [@@deriving compare]

  let equal_id = [%compare.equal: id]

  type stmt_nodekind =
    | AssertionFailure
    | BetweenJoinAndExit
    | BinaryConditionalStmtInit
    | BinaryOperatorStmt of string
    | Call of string
    | CallObjCNew
    | ClassCastException
    | ConditionalStmtBranch
    | ConstructorInit
    | CXXDynamicCast
    | CXXNewExpr
    | CXXStdInitializerListExpr
    | CXXTypeidExpr
    | DeclStmt
    | DefineBody
    | Destruction
    | ExceptionHandler
    | ExceptionsSink
    | FallbackNode
    | FinallyBranch
    | GCCAsmStmt
    | GenericSelectionExpr
    | IfStmtBranch
    | InitializeDynamicArrayLength
    | InitListExp
    | MessageCall of string
    | MethodBody
    | MonitorEnter
    | MonitorExit
    | ObjCCPPThrow
    | OutOfBound
    | ReturnStmt
    | Skip of string
    | SwitchStmt
    | ThisNotNull
    | Throw
    | ThrowNPE
    | UnaryOperator
  [@@deriving compare]

  type prune_node_kind =
    | PruneNodeKind_ExceptionHandler
    | PruneNodeKind_FalseBranch
    | PruneNodeKind_InBound
    | PruneNodeKind_IsInstance
    | PruneNodeKind_MethodBody
    | PruneNodeKind_NotNull
    | PruneNodeKind_TrueBranch
  [@@deriving compare]

  type nodekind =
    | Start_node
    | Exit_node
    | Stmt_node of stmt_nodekind
    | Join_node
    | Prune_node of bool * Sil.if_kind * prune_node_kind
        (** (true/false branch, if_kind, comment) *)
    | Skip_node of string
  [@@deriving compare]

  let equal_nodekind = [%compare.equal: nodekind]

  (** a node *)
  type t =
    { id: id  (** unique id of the node *)
    ; mutable dist_exit: int option  (** distance to the exit node *)
    ; mutable wto_index: int
    ; mutable exn: t list  (** exception nodes in the cfg *)
    ; mutable instrs: Instrs.not_reversed_t  (** instructions for symbolic execution *)
    ; kind: nodekind  (** kind of node *)
    ; loc: Location.t  (** location in the source code *)
    ; mutable preds: t list  (** predecessor nodes in the cfg *)
    ; pname: Typ.Procname.t  (** name of the procedure the node belongs to *)
    ; mutable succs: t list  (** successor nodes in the cfg *) }

  let exn_handler_kind = Stmt_node ExceptionHandler

  let exn_sink_kind = Stmt_node ExceptionsSink

  let throw_kind = Stmt_node Throw

  let dummy pname =
    { id= 0
    ; dist_exit= None
    ; wto_index= Int.max_value
    ; instrs= Instrs.empty
    ; kind= Skip_node "dummy"
    ; loc= Location.dummy
    ; pname
    ; succs= []
    ; preds= []
    ; exn= [] }


  let compare node1 node2 = Int.compare node1.id node2.id

  let hash node = Hashtbl.hash node.id

  let equal = [%compare.equal: t]

  (** Get the unique id of the node *)
  let get_id node = node.id

  let get_succs node = node.succs

  type node = t

  let pp_id f id = F.pp_print_int f id

  let pp f node = pp_id f (get_id node)

  module NodeSet = Caml.Set.Make (struct
    type t = node

    let compare = compare
  end)

  module IdMap = PrettyPrintable.MakePPMap (struct
    type t = id

    let compare = compare_id

    let pp = pp_id
  end)

  let get_exn node = node.exn

  (** Get the name of the procedure the node belongs to *)
  let get_proc_name node = node.pname

  (** Get the predecessors of the node *)
  let get_preds node = node.preds

  (** Get siblings *)
  let get_siblings node =
    get_preds node
    |> ISequence.gen_sequence_list ~f:(fun parent ->
           get_succs parent |> Sequence.of_list
           |> Sequence.filter ~f:(fun n -> not (equal node n))
           |> Sequence.Generator.of_sequence )
    |> Sequence.Generator.run


  (** Get the node kind *)
  let get_kind node = node.kind

  (** Get the instructions to be executed *)
  let get_instrs node = node.instrs

  (** Get the location of the node *)
  let get_loc n = n.loc

  (** Get the source location of the last instruction in the node *)
  let get_last_loc n =
    n |> get_instrs |> Instrs.last |> Option.value_map ~f:Sil.location_of_instr ~default:n.loc


  let find_in_node_or_preds =
    let rec find ~f visited nodes =
      match nodes with
      | node :: nodes when not (NodeSet.mem node visited) -> (
          let instrs = get_instrs node in
          match Instrs.find_map ~f:(f node) instrs with
          | Some res ->
              Some res
          | None ->
              let nodes = get_preds node |> List.rev_append nodes in
              let visited = NodeSet.add node visited in
              find ~f visited nodes )
      | _ :: nodes ->
          find ~f visited nodes
      | _ ->
          None
    in
    fun start_node ~f -> find ~f NodeSet.empty [start_node]


  let get_distance_to_exit node = node.dist_exit

  let get_wto_index node = node.wto_index

  (** Append the instructions to the list of instructions to execute *)
  let append_instrs node instrs =
    if instrs <> [] then node.instrs <- Instrs.append_list node.instrs instrs


  (** Map and replace the instructions to be executed *)
  let replace_instrs node ~f =
    let instrs' = Instrs.map_changed ~equal:phys_equal node.instrs ~f:(f node) in
    if phys_equal instrs' node.instrs then false
    else (
      node.instrs <- instrs' ;
      true )


  (* Skipping pretty printing... **)

  (** simple key for a node: just look at the instructions *)
  let simple_key node =
    let add_instr instr =
      match instr with
      | Sil.Load _ ->
          Some 1
      | Sil.Store _ ->
          Some 2
      | Sil.Prune _ ->
          Some 3
      | Sil.Call _ ->
          Some 4
      | Sil.Metadata _ ->
          None
    in
    get_instrs node
    |> IContainer.rev_filter_map_to_list ~fold:Instrs.fold ~f:add_instr
    |> Utils.better_hash


  (** key for a node: look at the current node, successors and predecessors *)
  let compute_key node =
    let succs = get_succs node in
    let preds = get_preds node in
    NodeKey.compute node ~simple_key ~succs ~preds
end
```