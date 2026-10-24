lemma chainInCache_of_mem_support_verifyOpening [DecidableEq Query] [DecidableEq Y]
    (model : NodeQueryModel Query Address Y) {s : Skeleton}
    (addressKey : SkeletonInternalIndex s → Address) (idx : SkeletonLeafIndex s)
    (leaf root : Y) (proof : List.Vector Y idx.depth)
    (cache₀ cache₁ : (Query →ₒ Y).QueryCache)
    (hmem : (true, cache₁) ∈ support
      ((simulateQ (Query →ₒ Y).cachingOracle
        (verifyOpening model addressKey idx leaf root proof)).run cache₀)) :
    ChainInCache model addressKey cache₁ leaf root idx proof := by
  simp only [verifyOpening, bind_pure_comp, simulateQ_map, StateT.run_map, support_map,
    Set.mem_image, Prod.ext_iff, beq_iff_eq] at hmem
  obtain ⟨_, h, rfl, rfl⟩ := hmem
  exact chainInCache_of_mem_support_getPutativeRoot model addressKey idx leaf proof _ _ _ h
