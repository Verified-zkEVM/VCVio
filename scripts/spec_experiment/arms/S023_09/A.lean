-- imports: VCVio.ProgramLogic.Tactics.Handler
lemma embedTrapFreshIdxImpl_run_inr (pk : PK) (sk : SK) (msg : M)
    (s : ((Salt × M →ₒ Range).QueryCache × ℕ) × ((Salt × M) → Option ℕ)) :
    ((embedTrapFreshIdxImpl psf M Salt pk sk (.inr msg)).run s :
        ProbComp ((Salt × Domain) ×
          (((Salt × M →ₒ Range).QueryCache × ℕ) × ((Salt × M) → Option ℕ)))) =
      (($ᵗ Salt : ProbComp Salt) >>= fun r =>
        ($ᵗ Range : ProbComp Range) >>= fun c =>
          (fun x : Domain =>
            ((r, x), ((s.1.1.cacheQuery (r, msg) c, s.1.2 + 1),
              fun t' => if t' = (r, msg) then some s.1.2 else s.2 t')) :
              Domain → (Salt × Domain) ×
                (((Salt × M →ₒ Range).QueryCache × ℕ) × ((Salt × M) → Option ℕ)))
            <$> (psf.trapdoorSample pk sk c : ProbComp Domain)) := by
  simp only [embedTrapFreshIdxImpl, QueryImpl.add_apply_inr, handler_nf]; simp
