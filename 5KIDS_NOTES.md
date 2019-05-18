# Useful Info for 5Kids 

**Add SCHEMES of what you find technically useful to this file**

**CFG**: [global Control Flow Graph](infer/src/IR/Cfg.ml) :: nodes=[SIL](infer/src/IR/Sil.ml) instructions

**[procdesc](infer/src/IR/Procdesc.ml)**:  :: [CFG of procedure](infer/src/absint/ProcCfg.ml) + [signature + annotations ... ](infer/src/absint/ProcData.ml)  __ procname may correspond to multiple procdesc's after resolution !!! (ProcData: container with proc description + extras: computed before analysis begin, accessible from transfer functions; e.g. save info from [prior analysis](infer/src/backend/preanal.ml)

**[Expressions](infer/src/IR/Exp.ml)** :: literals, program variables [Pvar](infer/src/IR/Pvar.ml), temp variables [Ident](infer/src/IR/Ident.ml), [info in type environment](infer/src/IR/Tenv.ml) 

**[Instructions](infer/src/IR/Instrs.ml)**:  :: Load, Store, Prune/assume, Call

[Typ](sledge/src/llair/typ.ml)
