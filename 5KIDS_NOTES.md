# Useful Info for 5Kids 

**Add SCHEMES of what you find technically useful to this file**

**CFG**: [global Control Flow Graph](Infer/src/IR/Cfg.ml) :: nodes=[SIL](Infer/src/IR/Sil.ml) instructions

**[procdesc](Infer/src/IR/Procdesc.ml)**:  :: [CFG of procedure](Infer/src/absint/ProcCfg.ml) + [signature + annotations ... ](Infer/src/absint/ProcData.ml)  __ procname may correspond to multiple procdesc's after resolution !!! (ProcData: container with proc description + extras: computed before analysis begin, accessible from transfer functions; e.g. save info from [prior analysis](Infer/src/backend/preanal.ml)

**[Expressions](Infer/src/IR/Exp.ml)** :: literals, program variables [Pvar](Infer/src/IR/Pvar.ml), temp variables [Ident](Infer/src/IR/Ident.ml), [info in type environment](Infer/src/IR/Tenv.ml) 

**[Instructions](Infer/src/IR/Instrs.ml)**:  :: Load, Store, Prune/assume, Call

[Typ](sledge/src/llair/typ.ml)
