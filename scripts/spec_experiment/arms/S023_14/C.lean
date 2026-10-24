-- imports: VCVio.ProgramLogic.Library VCVio.ProgramLogic.Library.Derive VCVio.ProgramLogic.Library.T3.GPVHashAndSign.TrapCount
lemma progGameRunImplCombinedTrapCount_table_defer (pk : PK) (sk : SK)
    (k₀ : Salt × M) (sStar : Domain)
    {β : Type} (oa : OracleComp ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain))) β)
    (G : β →
      (((Salt × M →ₒ Range).QueryCache × ℕ) × ((Salt × M) → Option ℕ)) × Finset M → ℝ≥0∞)
    (hGfresh : ∀ b w, k₀.2 ∈ w.2 → G b w = 0) :
    ∀ (s : ((((Salt × M →ₒ Range).QueryCache × Finset M) × Bool) × ((Salt × M) → Option Domain)) ×
        (((Salt × M) → Option ℕ) × ℕ)),
      (s.1.2 k₀ ≠ none → s.1.1.1.1 k₀ ≠ none) →
      (∑' z, Pr{let x ← (simulateQ (progGameRunImplCombinedTrapCount psf M Salt pk sk) oa).run s}[
          x = z] *
          (G z.1 ((((z.2.1.1.1.1, z.2.2.2), z.2.2.1), z.2.1.1.1.2)) *
            (if z.2.1.2 k₀ = some sStar then 1 else 0))) =
        ∑' z, Pr{let x ← (simulateQ (progGameRunImplCombinedTrapCount psf M Salt pk sk) oa).run s}[
            x = z] *
          (G z.1 ((((z.2.1.1.1.1, z.2.2.2), z.2.2.1), z.2.1.1.1.2)) *
            (match s.1.1.1.1 k₀ with
              | some _ => (if s.1.2 k₀ = some sStar then 1 else 0)
              | none =>
                  match z.2.1.1.1.1 k₀ with
                  | some v => Pr{let x ← psf.trapdoorSample pk sk v}[x = sStar]
                  | none => 0)) := by
  have hsupp {α : Type} (oa : ProbComp α) {f g : α → ℝ≥0∞} (h : ∀ z ∈ support oa, f z = g z) :
      ∑' z, Pr{let y ← oa}[y = z] * f z = ∑' z, Pr{let y ← oa}[y = z] * g z :=
    tsum_congr fun z => by
      by_cases hz : z ∈ support oa
      · rw [h z hz]
      · simp [prEvent_eq_zero_of_not_mem_support _ hz]
  have forged (ob : OracleComp ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain))) β)
      (v : Range) (σ : Domain → ((((Salt × M →ₒ Range).QueryCache × Finset M) × Bool) ×
        ((Salt × M) → Option Domain)) × (((Salt × M) → Option ℕ) × ℕ))
      (hc : ∀ x, (σ x).1.1.1.1 k₀ = some v) (ht : ∀ x, (σ x).1.2 k₀ = some x)
      (hσ : ∀ x, (σ x).1.1 = (σ sStar).1.1 ∧ (σ x).2 = (σ sStar).2) :
      ∑' x, Pr{let y ← psf.trapdoorSample pk sk v}[y = x] *
    ∑' z, Pr{let y ← (simulateQ (progGameRunImplCombinedTrapCount psf M Salt pk sk) ob).run (σ x)}[
          y = z] * (G z.1 ((((z.2.1.1.1.1, z.2.2.2), z.2.2.1), z.2.1.1.1.2)) *
          if z.2.1.2 k₀ = some sStar then 1 else 0) =
      ∑' x, Pr{let y ← psf.trapdoorSample pk sk v}[y = x] *
    ∑' z, Pr{let y ← (simulateQ (progGameRunImplCombinedTrapCount psf M Salt pk sk) ob).run (σ x)}[
          y = z] * (G z.1 ((((z.2.1.1.1.1, z.2.2.2), z.2.2.1), z.2.1.1.1.2)) *
          match z.2.1.1.1.1 k₀ with
          | some w => Pr{let x ← psf.trapdoorSample pk sk w}[x = sStar]
          | none => 0) := by
    have hQ x := progGameRunImplCombinedTrapCount_table_indep psf M Salt pk sk ob G (σ x) (σ sStar)
      (hσ x).1 (hσ x).2
    refine Eq.trans ?_ (tsum_congr fun x => congrArg _ (hsupp _
      (g := fun z => G z.1 ((((z.2.1.1.1.1, z.2.2.2), z.2.2.1), z.2.1.1.1.2)) *
        Pr{let x ← psf.trapdoorSample pk sk v}[x = sStar]) fun z hz => ?_)).symm
    · simp only [progGameRunImplCombinedTrapCount_table_frozen_eq psf M Salt pk sk k₀ sStar ob G
        hGfresh, hc, ht, ne_eq, reduceCtorEq, not_false_eq_true]
      simp [← mul_assoc, ENNReal.tsum_mul_right, hQ, OracleComp.tsum_prEvent_eq_one]
      exact mul_comm _ _
    · by_cases hf : k₀.2 ∈ z.2.1.1.1.2 <;> simp [hf, hGfresh z.1 (_, _), hc,
        progGameRunImplCombinedTrapCount_frozen psf M Salt pk sk k₀ ob _ (by simp [hc]) z hz]
  intro s htc
  induction oa using OracleComp.inductionOn generalizing s with
  | pure a =>
      simp only [simulateQ_pure, StateT.run_pure, OracleComp.tsum_prEvent_pure_mul]
      clear hsupp forged
      rcases hc : s.1.1.1.1 k₀ with _ | v <;> simp_all
  | query_bind t mx ih =>
      rcases hcs : s.1.1.1.1 k₀ with _ | v₀
      · have htbls : s.1.2 k₀ = none := by simpa [hcs] using htc
        simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
          OracleQuery.cont_query, id_map, StateT.run_bind]
        rcases t with (n | mc) | msg
        · simp only [progGameRunImplCombinedTrapCount_run_inl_inl, bind_assoc, pure_bind,
            OracleComp.tsum_prEvent_bind_mul]
          exact tsum_congr fun v => congrArg _ ((ih v s htc).trans (by rw [hcs]))
        · rw [progGameRunImplCombinedTrapCount_run_inl_inr]
          rcases hmcq : s.1.1.1.1 mc with _ | v
          · simp only [bind_assoc, pure_bind, OracleComp.tsum_prEvent_bind_mul]
            refine tsum_congr fun v => congrArg _ ?_
            obtain rfl | hmck := eq_or_ne mc k₀
            · exact forged (mx v) v _ (by simp) (by simp) fun _ => ⟨rfl, rfl⟩
            · refine tsum_congr fun x => congrArg _ ((ih v _ ?_).trans ?_) <;>
                simp [hcs, hmck.symm, htbls]
          · simp only [pure_bind]
            exact (ih v s htc).trans (by rw [hcs])
        · simp only [progGameRunImplCombinedTrapCount_run_inr, bind_assoc, pure_bind,
            OracleComp.tsum_prEvent_bind_mul]
          refine tsum_congr fun r => congrArg _ <| tsum_congr fun v => congrArg _ <|
            tsum_congr fun x => congrArg _ ?_
          by_cases hmsg : msg = k₀.2
          · refine hsupp _ fun z hz => ?_
            simp [hGfresh z.1 (_, _) (progGameRunImplCombinedTrapCount_signedSet_grows psf M Salt
              pk sk _ _ z hz (by simp [hmsg]))]
          · refine (ih (r, x) _ ?_).trans ?_ <;> simp [hcs, htbls, Prod.ext_iff, Ne.symm hmsg]
      · rw [progGameRunImplCombinedTrapCount_table_frozen_eq psf M Salt pk sk k₀ sStar _ G hGfresh s
          (by simp [hcs]), ← ENNReal.tsum_mul_left]
        exact tsum_congr fun z => by ring
