lemma evalDistEq_run_progGameRunImplCombinedTrap_eq {β : Type}
    (domainSample : PK → ProbComp Domain) (pk : PK) (sk : SK)
    (hreg : (do let s ← domainSample pk; pure (psf.eval pk s, s) : ProbComp (Range × Domain)) =ᵈ
      (do let c ← ($ᵗ Range); let s ← psf.trapdoorSample pk sk c; pure (c, s)
            : ProbComp (Range × Domain)))
    (oa : OracleComp ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain))) β)
    (s : (((Salt × M →ₒ Range).QueryCache × Finset M) × Bool) × ((Salt × M) → Option Domain)) :
    ((simulateQ (progGameRunImplCombined psf M Salt domainSample pk) oa).run s) =ᵈ
      ((simulateQ (progGameRunImplCombinedTrap psf M Salt pk sk) oa).run s) :=
  evalDistEq_simulateQ_run _ _ (evalDistEq_progGameRunImplCombined_step_eq_trap _ _ _ _ _ _ hreg) ..
