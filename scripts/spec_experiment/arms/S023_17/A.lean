lemma embedTrapIdxSigImpl_fresh_idx_cache_eq_general (pk : PK) (sk : SK) (j : ℕ) (y : Range) :
    ∀ {β : Type}
      (oa : OracleComp ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain))) β)
      (s : (((Salt × M →ₒ Range).QueryCache × ℕ) × ((Salt × M) → Option ℕ)) × Finset M),
      (∀ k, s.1.2 k = some j → k.2 ∉ s.2 → s.1.1.1 k = some y) →
      ∀ z ∈ support ((simulateQ (embedTrapIdxSigImpl psf M Salt pk sk j y) oa).run s),
        ∀ k, z.2.1.2 k = some j → k.2 ∉ z.2.2 → z.2.1.1.1 k = some y := by
  refine fun oa => OracleComp.simulateQ_run_preservesInv _ _ ?_ oa
  rintro ((n | mc) | msg) s hs ⟨v, s'⟩ hz k hidx hfresh
  · rw [embedTrapIdxSigImpl_run_inl_inl] at hz
    obtain ⟨_, -, ⟨⟩⟩ := (support_map _ _).le hz; exact hs k hidx hfresh
  · rw [embedTrapIdxSigImpl_run_inl_inr] at hz
    rcases hq : s.1.1.1 mc with _ | w <;> simp only [hq, support_map, support_pure, Set.mem_image,
      Set.mem_singleton_iff] at hz <;> grind
  · rw [embedTrapIdxSigImpl_run_inr] at hz
    simp only [support_bind, support_map, Set.mem_iUnion, Set.mem_image] at hz; grind
