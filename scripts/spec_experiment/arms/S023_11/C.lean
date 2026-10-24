-- imports: VCVio.ProgramLogic.Library VCVio.ProgramLogic.Library.Derive
theorem gpv_measureTVDist_orig_verify_le_collisionBound [Nonempty Salt]
    {γ : Type} [MeasurableSpace (γ × (Salt × M →ₒ Range).QueryCache × Bool)]
    (pk : PK) (sk : SK)
    (adv : SignatureAlg.UnforgeableAdversary
      (GPVHashAndSign (m := OracleComp (unifSpec + (Salt × M →ₒ Range))) psf hr M Salt))
    (domainSample : PK → ProbComp Domain)
    (kont : M × (Salt × Domain) →
      OracleComp ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain))) γ)
    (qSign qHash : ℕ)
    (hQ : signHashQueryBound
      (S' := Salt × Domain) (α := M × (Salt × Domain))
      (oa := adv.main pk) (qSign := qSign) (qHash := qHash))
    (hkont : ∀ x, (kont x).IsQueryBoundP (· matches .inr _) 0)
    (hreg : (do let s ← domainSample pk; pure (psf.eval pk s, s) : ProbComp (Range × Domain)) =ᵈ
      (do let c ← ($ᵗ Range); let s ← psf.trapdoorSample pk sk c; pure (c, s)
            : ProbComp (Range × Domain))) :
    measureTVDist ((simulateQ (gpvRealImplFlag psf hr M Salt pk sk) (adv.main pk >>= kont)).run
          ((∅ : (Salt × M →ₒ Range).QueryCache), false))
        ((simulateQ (progGameRunImplNoRecFlag psf M Salt domainSample pk)
            (adv.main pk >>= kont)).run
          ((∅ : (Salt × M →ₒ Range).QueryCache), false))
      ≤ (collisionBound Salt qSign qHash).toReal :=
  (measureTVDist_eq_toReal_measureETVDist _ _).trans_le <| (toReal_mono (prEvent_ne_top _) <|
    (measureETVDist_simulateQ_run_le_prEvent_bad _ _ _ (gpvImplFlag_h_agree _ _ _ _ _ _ _ hreg)
    (gpvRealImplFlag_bad_mono _ _ _ _ _ _) (progGameRunImplNoRecFlag_bad_mono _ _ _ _ _) _ _).trans
    <| prEvent_flag_bind_no_sign_le _ _ _ _ _ _ _ _ _ _ hkont).trans <|
    gpv_orig_flag_le_collisionBound _ _ _ _ _ _ adv _ _ hQ
