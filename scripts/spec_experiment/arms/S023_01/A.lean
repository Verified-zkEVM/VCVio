lemma replayPathResult_mem_support_replayFirstRun
    (main : OracleComp spec α) (path : PFunctor.FreeM.Path main)
    (hpath : path ∈ support (replayFirstPath main)) :
    replayPathResult main path ∈ support (replayFirstRun main) :=
  map_replayPathResult_replayFirstPath main ▸ (support_map _ _).ge ⟨_, hpath, rfl⟩
