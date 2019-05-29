## Playing with OCaml

### Tips to Go Faster
Exec `make devsetup` in Infer's root folder to install nice utilities (Merlin, utop...). After the first build, just remake OCaml sources by `make -j -C infer/src byte`

### Reverse Engineering SIL Printer
Let's do it. Recall 
```OCaml
  (** Take an abstract state and instruction, produce a new abstract state *)
  let exec_instr _ _ _ instr =
    let pe=Pp.text in
      Logging.progress "SILPrinter: %a@\n" (Sil.pp_instr ~print_types:true pe) instr
```
We go to `Sil.ml` and `Sil.mli` to check for `pp.instr`:
```OCaml
val pp_instr : print_types:bool -> Pp.env -> F.formatter -> instr -> unit
let pp_instr ~print_types pe0 f instr =
  let pp_typ = if print_types then Typ.pp_full else Typ.pp in
  color_wrapper pe0 f instr ~f:(fun pe f instr ->
      match instr with
      | Load (id, e, t, loc) ->
          F.fprintf f "%a=*%a:%a [%a]" Ident.pp id (pp_exp_printenv ~print_types pe) e (pp_typ pe0)
            t Location.pp loc
      | Store (e1, t, e2, loc) ->
          F.fprintf f "*%a:%a=%a [%a]" (pp_exp_printenv ~print_types pe) e1 (pp_typ pe0) t
            (pp_exp_printenv ~print_types pe) e2 Location.pp loc
      | Prune (cond, loc, true_branch, _) ->
          F.fprintf f "PRUNE(%a, %b); [%a]" (pp_exp_printenv ~print_types pe) cond true_branch
            Location.pp loc
      | Call ((id, _), e, arg_ts, loc, cf) ->
          F.fprintf f "%a=" Ident.pp id ;
          F.fprintf f "%a(%a)%a [%a]" (pp_exp_printenv ~print_types pe) e
            (Pp.comma_seq (pp_exp_typ pe))
            arg_ts CallFlags.pp cf Location.pp loc
      | Metadata metadata ->
          pp_instr_metadata pe0 f metadata )
```

We can begin the analysis from the first matched instruction, `Load`:
```OCaml
Load (id, e, t, loc) ->
  F.fprintf f "%a=*%a:%a [%a]" Ident.pp id (pp_exp_printenv ~print_types pe) e (pp_typ pe0) t Location.pp loc
```
where in `Ident.mli`:
```OCaml
val pp : Format.formatter -> t -> unit
let pp f id =
  if has_kind id KNone then F.pp_print_char f '_'
  else
    let base_name = name_to_string id.name in
    let prefix = if has_kind id KFootprint then "@" else if has_kind id KNormal then "" else "_" in
    F.fprintf f "%s%s$%d" prefix base_name id.stamp
```

We could go to see how `name_to_string` is implemented; we would find out that it is the function `to_string` defined in the module `Name`:
```OCaml
module Name = struct
  type t = Primed | Normal | Footprint | Spec | FromString of string [@@deriving compare]
  let primed = "t"
  let normal = "n"
  let footprint = "f"
  let spec = "val"
  let from_string s = FromString s
  let to_string = function
    | Primed ->
        primed
    | Normal ->
        normal
    | Footprint ->
        footprint
    | Spec ->
        spec
    | FromString s ->
        s
end
type name = Name.t [@@deriving compare]
type kind =
  | KNone
      (** special kind of "null ident" (basically, a more compact way of implementing an ident option).
      useful for situations when an instruction requires an id, but no one should read the result. *)
  | KFootprint
  | KNormal
  | KPrimed
[@@deriving compare]

type t = {kind: kind; name: Name.t; stamp: int} [@@deriving compare]
```

Actually I'd better tell you that pretty printing is built upon OCaml pretty printing module `Format`, you can get an intro [here](http://caml.inria.fr/resources/doc/guides/format.en.html); that's the reason for all such `@` in strings!

`Format.asprintf`:

```OCaml
(** Pretty print an identifier. *)
let pp f id =
  if has_kind id KNone then F.pp_print_char f '_'
  else
    let base_name = name_to_string id.name in
    let prefix = if has_kind id KFootprint then "@" else if has_kind id KNormal then "" else "_" in
    F.fprintf f "%s%s$%d" prefix base_name id.stamp


(** Convert an identifier to a string. *)
let to_string id = F.asprintf "%a" pp id    (** Interesting... pp : Format.formatter -> t -> unit ... *)
```

Let's come back to our SIL Printer; with a bit of formatting, arguments are much clearer:
```OCaml
let pp_instr ~print_types pe0 f instr =
  let pp_typ = if print_types then Typ.pp_full else Typ.pp in
  color_wrapper pe0 f instr ~f:(fun pe f instr ->
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
```

Now we know how to get the string for the indentifier, e.g. for `id` by the function `to_string` that I showed you before. We can now proceed with `pp_exp_printenv`, because this is what we need to extract the arithmetic operations:

```OCaml
val pp_exp_printenv : ?print_types:bool -> Pp.env -> F.formatter -> Exp.t -> unit
let pp_exp_printenv ?(print_types = false) =
  color_wrapper ~f:(fun pe f e0 ->
      let e =
        match pe.Pp.obj_sub with  (** Is there a pending substitution in Pp environment? *)
        | Some sub ->
            (* apply object substitution to expression *) Obj.obj (sub (Obj.repr e0))
        | None ->
            e0
      in
      if not (Exp.equal e0 e) then
        match e with 
        | Exp.Lvar pvar -> Pvar.pp_value f pvar 
        | _ -> assert false
      else Exp.pp_printenv ~print_types pe f e )
```

in `Pp.mli` we find
```OCaml
(** Print environment threaded through all the printing functions *)
type env =
  { opt: simple_kind  (** Current option for simple printing *)
  ; kind: print_kind  (** Current kind of printing *)
  ; break_lines: bool
        (** whether to let Format add its own line breaks or not (false by default) *)
  ; cmap_norm: colormap  (** Current colormap for the normal part *)
  ; cmap_foot: colormap  (** Current colormap for the footprint part *)
  ; color: color  (** Current color *)
  ; obj_sub: (Obj.t -> Obj.t) option  (** generic object substitution *) }
```

Mmh, what is `Obj`? There is an interesting reading [here](https://v1.realworldocaml.org/v1/en/html/memory-representation-of-values.html), where they explain the actual memory layout of OCaml, and what is `Obj` module about. 
That said, we focus on 
```OCaml
      if not (Exp.equal e0 e) then
        match e with 
        | Exp.Lvar pvar -> Pvar.pp_value f pvar 
        | _ -> assert false
      else Exp.pp_printenv ~print_types pe f e )
```
in particular, recall type t in `Exp.ml`
```OCaml
(** Program expressions. *)
and t =
  | Var of ident_  (** Pure variable: it is not an lvalue *)
  | UnOp of Unop.t * t * Typ.t option  (** Unary operator with type of the result if known *)
  | BinOp of Binop.t * t * t  (** Binary operator *)
  | Exn of t  (** Exception *)
  | Closure of closure  (** Anonymous function *)
  | Const of Const.t  (** Constants *)
  | Cast of Typ.t * t  (** Type cast *)
  | Lvar of Pvar.t  (** The address of a program variable *)
  | Lfield of t * Typ.Fieldname.t * Typ.t
      (** A field offset, the type is the surrounding struct type *)
  | Lindex of t * t  (** An array index offset: [exp1\[exp2\]] *)
  | Sizeof of sizeof_data
[@@deriving compare]
```
We see that `Exp.Lvar pvar` would be an address of a program variable, which in our `SILPrinter` is just `*&variable_name`. Let's check it, looking at `Pvar.pp_value`:
```OCaml
let pp_ f pv =
  let name = pv.pv_name in
  match pv.pv_kind with
  | Local_var _ ->
      Mangled.pp f name
  | Callee_var _ ->
      F.fprintf f "%a|callee" Mangled.pp name
  | Abduced_retvar _ ->
      F.fprintf f "%a|abducedRetvar" Mangled.pp name
  | Abduced_ref_param (_, index, _) ->
      F.fprintf f "%a|abducedRefParam%d" Mangled.pp name index
  | Global_var {translation_unit; is_constexpr; is_ice; is_pod} ->
      F.fprintf f "#GB<%a%s%s%s>$%a" pp_translation_unit translation_unit
        (if is_constexpr then "|const" else "")
        (if is_ice then "|ice" else "")
        (if not is_pod then "|!pod" else "")
        Mangled.pp name
  | Seed_var ->
      F.fprintf f "old_%a" Mangled.pp name


(** Pretty print a pvar which denotes a value, not an address *)
let pp_value f pv = pp_ f pv
```
and adding to that, we have in `Pvar.ml`
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

(** Names for program variables. *)
type t = {pv_hash: int; pv_name: Mangled.t; pv_kind: pvar_kind} [@@deriving compare]
```

Now, we can turn our attention to the effective expression printer `Expr.pp_printenv`, which will navigate through binary operations etc :
```OCaml
let pp_printenv ~print_types pe f e =
  let pp_typ = if print_types then Typ.pp_full else Typ.pp in
  pp_ pe (pp_typ pe) f e
```

where the actual printer is:
```OCaml
(** Pretty print an expression. *)
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
```
