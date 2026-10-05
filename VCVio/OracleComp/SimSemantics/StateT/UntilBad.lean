/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module

public import VCVio.OracleComp.SimSemantics.StateT.PreservesInv
public import VCVio.OracleComp.SimSemantics.StateT.StateProjection
public import VCVio.EvalDist.ProbabilityBounds

/-!
# Identical until bad for `StateT σ ProbComp` handlers

The fundamental lemma of game playing for two stateful handlers
`impl₁ impl₂ : QueryImpl spec (StateT σ ProbComp)` and a state predicate `bad : σ → Prop`,
stated with the event notation `Pr{…}[…]` of the measure API.

`QueryImpl.AgreeUntilBad impl₁ impl₂ bad` asks only that, from a non-bad state, the two steps
put the same mass on every event whose post-state is non-bad. The handlers may disagree
arbitrarily on the step that raises the flag, and on every step taken from a bad state.
Pointwise agreement on non-bad states (`QueryImpl.AgreeUntilBad.of_run_eq`) is a special case,
and so is agreement except on steps that reach only bad states
(`QueryImpl.AgreeUntilBad.of_run_eq_or_bad`).

When the first handler preserves `bad` (`QueryImpl.PreservesInv`), a non-bad final state of its
run witnesses a history that was non-bad throughout, so an event conjoined with a non-bad final
state of the first run has at most the mass of the event in the second
(`QueryImpl.AgreeUntilBad.prEvent_simulateQ_run_and_not_bad_le`). Every other statement here
follows from this one. Since a `ProbComp` has total mass one, each one-sided bound needs only the
invariant of the run whose bad mass it charges; the equalities need both.

Agreement until `bad` survives extending the two handlers by the same passive auxiliary state
(`QueryImpl.AgreeUntilBad.extendState`), with `bad` read on the base state, and so does
preservation of `bad` (`QueryImpl.PreservesInv.extendState`, in
`VCVio/OracleComp/SimSemantics/StateT/PreservesInv.lean`); bookkeeping such as counters or logs
can therefore be added to both runs before applying the bounds.

Two handlers on different state spaces `σ₂` and `σ₁` are compared through a map `f : σ₂ → σ₁`.
If, from every non-bad state satisfying an invariant, each step of the second handler, read
through `f` and restricted to non-bad post-states, puts on every event at most the mass of the
first handler's step from the mapped state, then so do whole runs
(`QueryImpl.prEvent_simulateQ_run_map_and_not_bad_le`); passing to complements, an event of the
first run is at most the same event, read through `f`, or `bad`, in the second
(`QueryImpl.prEvent_simulateQ_run_le_map_or_bad`).

## Main statements

- `QueryImpl.AgreeUntilBad`: agreement of two handlers on non-bad post-states.
- `QueryImpl.AgreeUntilBad.prEvent_simulateQ_run_and_not_bad_le`: the one-sided core.
- `QueryImpl.AgreeUntilBad.prEvent_simulateQ_run_and_not_bad_eq`: equal mass off the bad event.
- `QueryImpl.AgreeUntilBad.prEvent_simulateQ_run_bad_eq`: equal bad mass.
- `QueryImpl.AgreeUntilBad.prEvent_simulateQ_run_le_add_bad_left` and
  `QueryImpl.AgreeUntilBad.prEvent_simulateQ_run_le_add_bad_right`: an event of the first run
  exceeds the same event of the second by at most the bad mass of the first, respectively the
  second, run.
- `QueryImpl.AgreeUntilBad.extendState`: agreement until `bad` under a shared passive extension.
- `QueryImpl.prEvent_simulateQ_run_map_and_not_bad_le` and
  `QueryImpl.prEvent_simulateQ_run_le_map_or_bad`: the comparison of two handlers on different
  state spaces, when each step of the second, read through a state map `f`, is dominated off
  `bad` by the step of the first from the mapped state.

The same idea, for handlers into `OracleComp spec` and with the output-marginal total-variation
distance, is `OracleComp.ProgramLogic.Relational.identical_until_bad_with_flag`
(`VCVio/ProgramLogic/Relational/SimulateQ/Basic.lean`); a state-separating-package form is in
`VCVio/StateSeparating/IdenticalUntilBad.lean`. Both are stated in the discrete `Pr[…]`
compatibility API.
-/

public section

open OracleComp MeasureTheory

namespace QueryImpl

variable {ι : Type} {spec : OracleSpec ι} {σ α : Type}

/-- Two stateful handlers agree until `bad`: from every non-bad state, each query step of `impl₁`
and of `impl₂` puts the same mass on every event conjoined with a non-bad post-state. -/
@[expose] def AgreeUntilBad (impl₁ impl₂ : QueryImpl spec (StateT σ ProbComp))
    (bad : σ → Prop) : Prop :=
  ∀ t s, ¬bad s → ∀ Q : spec.Range t × σ → Prop,
    Pr{let z ← (impl₁ t).run s}[Q z ∧ ¬bad z.2] = Pr{let z ← (impl₂ t).run s}[Q z ∧ ¬bad z.2]

namespace AgreeUntilBad

variable {impl₁ impl₂ : QueryImpl spec (StateT σ ProbComp)} {bad : σ → Prop}

/-- Agreement until `bad` is symmetric in the two handlers. -/
theorem symm (h : AgreeUntilBad impl₁ impl₂ bad) : AgreeUntilBad impl₂ impl₁ bad :=
  fun t s hs Q ↦ (h t s hs Q).symm

/-- Handlers agree until `bad` when, from every non-bad state, their steps either coincide or
both reach only bad post-states. -/
theorem of_run_eq_or_bad (h : ∀ t s, ¬bad s → (impl₁ t).run s = (impl₂ t).run s ∨
      ((∀ z ∈ support ((impl₁ t).run s), bad z.2) ∧ ∀ z ∈ support ((impl₂ t).run s), bad z.2)) :
    AgreeUntilBad impl₁ impl₂ bad := by
  intro t s hs Q
  rcases h t s hs with he | ⟨h₁, h₂⟩
  · rw [he]
  · rw [prEvent_eq_zero_of_forall_mem_support _ _ fun z hz hz' ↦ hz'.2 (h₁ z hz),
      prEvent_eq_zero_of_forall_mem_support _ _ fun z hz hz' ↦ hz'.2 (h₂ z hz)]

/-- Handlers whose steps coincide on every non-bad state agree until `bad`. -/
theorem of_run_eq (h : ∀ t s, ¬bad s → (impl₁ t).run s = (impl₂ t).run s) :
    AgreeUntilBad impl₁ impl₂ bad :=
  of_run_eq_or_bad fun t s hs ↦ .inl (h t s hs)

/-- Handlers that agree until `bad` still agree until `bad`, read on the base state, after both
are extended by the same passive auxiliary state. -/
theorem extendState {Q : Type} (h : AgreeUntilBad impl₁ impl₂ bad)
    (aux : (t : spec.Domain) → σ → spec.Range t → σ → Q → Q) :
    AgreeUntilBad (impl₁.extendState aux) (impl₂.extendState aux) fun st ↦ bad st.1 := by
  intro t st hst P
  simp only [QueryImpl.extendState_apply, bind_assoc, pure_bind]
  exact h t st.1 hst fun z ↦ P (z.1, (z.2, aux t st.1 z.1 z.2 st.2))

/-- If two handlers agree until `bad` and the first preserves `bad`, an event conjoined with a
non-bad final state of the first run has at most the mass of the event in the second run. -/
theorem prEvent_simulateQ_run_and_not_bad_le (h : AgreeUntilBad impl₁ impl₂ bad)
    (h₁ : PreservesInv impl₁ bad) (oa : OracleComp spec α) (s : σ) (P : α × σ → Prop) :
    Pr{let z ← (simulateQ impl₁ oa).run s}[P z ∧ ¬bad z.2] ≤
      Pr{let z ← (simulateQ impl₂ oa).run s}[P z] := by
  induction oa using OracleComp.inductionOn generalizing s with
  | pure x => exact prEvent_mono (pure (x, s) : ProbComp _) _ _ fun _ hz ↦ hz.1
  | query_bind t k ih =>
    by_cases hs : bad s
    · rw [prEvent_eq_zero_of_forall_mem_support _ _ fun z hz hz' ↦
          hz'.2 (simulateQ_run_preservesInv impl₁ bad h₁ _ s hs z hz)]
      exact zero_le
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
    let _ : MeasurableSpace (spec.Range t × σ) := ⊤
    rw [prEvent_bind_eq_lintegral_of_discrete, prEvent_bind_eq_lintegral_of_discrete]
    -- From a bad intermediate state the first continuation has no mass off `bad`, so the first
    -- integral only sees the step measure restricted to non-bad post-states, where the two agree.
    have hsupp : (fun z : spec.Range t × σ ↦
        Pr{let w ← (simulateQ impl₁ (k z.1)).run z.2}[P w ∧ ¬bad w.2]).support ⊆
          {z | ¬bad z.2} := fun z hz hb ↦
      hz (prEvent_eq_zero_of_forall_mem_support _ _ fun w hw hw' ↦
        hw'.2 (simulateQ_run_preservesInv impl₁ bad h₁ _ z.2 hb w hw))
    have hrestr : (𝒟[(impl₁ t).run s]).restrict {z | ¬bad z.2} =
        (𝒟[(impl₂ t).run s]).restrict {z | ¬bad z.2} := by
      ext A -
      rw [Measure.restrict_apply MeasurableSet.of_discrete,
        Measure.restrict_apply MeasurableSet.of_discrete]
      simpa only [prEvent_eq_evalDist_of_discrete, Set.inter_def, Set.mem_ofPred_eq] using
        h t s hs (· ∈ A)
    rw [← setLIntegral_eq_of_support_subset hsupp, hrestr]
    exact (lintegral_mono fun z : spec.Range t × σ ↦ ih z.1 z.2).trans
      (setLIntegral_le_lintegral _ _)

/-- **Identical until bad.** If two handlers agree until `bad` and both preserve `bad`, their
runs of any oracle computation put the same mass on every event conjoined with a non-bad final
state. -/
theorem prEvent_simulateQ_run_and_not_bad_eq (h : AgreeUntilBad impl₁ impl₂ bad)
    (h₁ : PreservesInv impl₁ bad) (h₂ : PreservesInv impl₂ bad)
    (oa : OracleComp spec α) (s : σ) (P : α × σ → Prop) :
    Pr{let z ← (simulateQ impl₁ oa).run s}[P z ∧ ¬bad z.2] =
      Pr{let z ← (simulateQ impl₂ oa).run s}[P z ∧ ¬bad z.2] :=
  le_antisymm
    ((prEvent_mono _ _ _ fun _ hz ↦ ⟨hz, hz.2⟩).trans
      (h.prEvent_simulateQ_run_and_not_bad_le h₁ oa s fun z ↦ P z ∧ ¬bad z.2))
    ((prEvent_mono _ _ _ fun _ hz ↦ ⟨hz, hz.2⟩).trans
      (h.symm.prEvent_simulateQ_run_and_not_bad_le h₂ oa s fun z ↦ P z ∧ ¬bad z.2))

/-- Handlers that agree until `bad` and both preserve it give the bad event the same mass. -/
theorem prEvent_simulateQ_run_bad_eq (h : AgreeUntilBad impl₁ impl₂ bad)
    (h₁ : PreservesInv impl₁ bad) (h₂ : PreservesInv impl₂ bad)
    (oa : OracleComp spec α) (s : σ) :
    Pr{let z ← (simulateQ impl₁ oa).run s}[bad z.2] =
      Pr{let z ← (simulateQ impl₂ oa).run s}[bad z.2] := by
  have hgood := h.prEvent_simulateQ_run_and_not_bad_eq h₁ h₂ oa s fun _ ↦ True
  simp only [true_and] at hgood
  have e₁ := prEvent_add_prEvent_not_eq_prEvent_true ((simulateQ impl₁ oa).run s)
    fun z ↦ bad z.2
  have e₂ := prEvent_add_prEvent_not_eq_prEvent_true ((simulateQ impl₂ oa).run s)
    fun z ↦ bad z.2
  rw [prEvent_true_eq_one, hgood] at e₁
  rw [prEvent_true_eq_one] at e₂
  exact (ENNReal.add_left_inj (ne_top_of_le_ne_top ENNReal.one_ne_top (prEvent_le_one _ _))).1
    (e₁.trans e₂.symm)

/-- If two handlers agree until `bad` and the first preserves `bad`, an event of the first run
exceeds the same event of the second run by at most the mass of `bad` in the first run. -/
theorem prEvent_simulateQ_run_le_add_bad_left (h : AgreeUntilBad impl₁ impl₂ bad)
    (h₁ : PreservesInv impl₁ bad) (oa : OracleComp spec α) (s : σ) (P : α × σ → Prop) :
    Pr{let z ← (simulateQ impl₁ oa).run s}[P z] ≤
      Pr{let z ← (simulateQ impl₂ oa).run s}[P z] +
        Pr{let z ← (simulateQ impl₁ oa).run s}[bad z.2] := by
  rw [add_comm]
  exact prEvent_le_prEvent_add_of_prEvent_and_not_le ((simulateQ impl₁ oa).run s)
    ((simulateQ impl₂ oa).run s) (fun z ↦ bad z.2) P P
    (h.prEvent_simulateQ_run_and_not_bad_le h₁ oa s P)

/-- If two handlers agree until `bad` and the second preserves `bad`, an event of the first run
exceeds the same event of the second run by at most the mass of `bad` in the second run. -/
theorem prEvent_simulateQ_run_le_add_bad_right (h : AgreeUntilBad impl₁ impl₂ bad)
    (h₂ : PreservesInv impl₂ bad) (oa : OracleComp spec α) (s : σ) (P : α × σ → Prop) :
    Pr{let z ← (simulateQ impl₁ oa).run s}[P z] ≤
      Pr{let z ← (simulateQ impl₂ oa).run s}[P z] +
        Pr{let z ← (simulateQ impl₂ oa).run s}[bad z.2] := by
  rw [add_comm]
  refine prEvent_le_prEvent_add_of_prEvent_not_and_not_le ((simulateQ impl₂ oa).run s)
    ((simulateQ impl₁ oa).run s) (fun z ↦ bad z.2) P P ?_
    (h.symm.prEvent_simulateQ_run_and_not_bad_le h₂ oa s fun z ↦ ¬P z)
  rw [prEvent_true_eq_one, prEvent_true_eq_one]

end AgreeUntilBad

/-! ## Projection onto a second handler until bad -/

section Projection

variable {σ₁ σ₂ : Type} {impl₁ : QueryImpl spec (StateT σ₁ ProbComp)}
  {impl₂ : QueryImpl spec (StateT σ₂ ProbComp)}

/-- **Projection until bad.** Let `impl₂` preserve a state invariant `inv` and a state predicate
`bad`. If, from every non-bad state satisfying `inv`, each step of `impl₂`, with its post-state
mapped through `f` and conjoined with a non-bad post-state, puts on every event at most the mass
of the step of `impl₁` from the mapped state, then the same holds for whole runs from a state
satisfying `inv`. -/
theorem prEvent_simulateQ_run_map_and_not_bad_le (f : σ₂ → σ₁) {inv bad : σ₂ → Prop}
    (hinv : PreservesInv impl₂ inv) (hbad : PreservesInv impl₂ bad)
    (h : ∀ t s, inv s → ¬bad s → ∀ Q : spec.Range t × σ₁ → Prop,
      Pr{let z ← (impl₂ t).run s}[Q (z.1, f z.2) ∧ ¬bad z.2] ≤
        Pr{let z ← (impl₁ t).run (f s)}[Q z])
    (oa : OracleComp spec α) (s : σ₂) (hs : inv s) (P : α × σ₁ → Prop) :
    Pr{let z ← (simulateQ impl₂ oa).run s}[P (z.1, f z.2) ∧ ¬bad z.2] ≤
      Pr{let z ← (simulateQ impl₁ oa).run (f s)}[P z] := by
  induction oa using OracleComp.inductionOn generalizing s with
  | pure x =>
    simp only [simulateQ_pure, StateT.run_pure]
    refine le_trans (le_of_eq ?_) (prEvent_mono (pure (x, f s) : ProbComp _)
      (fun z ↦ P z ∧ ¬bad s) P fun _ hz ↦ hz.1)
    simp only [pure_bind]
  | query_bind t k ih =>
    by_cases hb : bad s
    · rw [prEvent_eq_zero_of_forall_mem_support _ _ fun z hz hz' ↦
          hz'.2 (simulateQ_run_preservesInv impl₂ bad hbad _ s hb z hz)]
      exact zero_le
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
    let _ : MeasurableSpace (spec.Range t × σ₂) := ⊤
    let _ : MeasurableSpace (spec.Range t × σ₁) := ⊤
    rw [prEvent_bind_eq_lintegral_of_discrete, prEvent_bind_eq_lintegral_of_discrete]
    let g : spec.Range t × σ₁ → ENNReal := fun y ↦
      Pr{let w ← (simulateQ impl₁ (k y.1)).run y.2}[P w]
    have hsupp : (fun z : spec.Range t × σ₂ ↦
        Pr{let w ← (simulateQ impl₂ (k z.1)).run z.2}[P (w.1, f w.2) ∧ ¬bad w.2]).support ⊆
          {z | ¬bad z.2} := fun z hz hb ↦
      hz (prEvent_eq_zero_of_forall_mem_support _ _ fun w hw hw' ↦
        hw'.2 (simulateQ_run_preservesInv impl₂ bad hbad _ z.2 hb w hw))
    have hae : ∀ᵐ z ∂𝒟[(impl₂ t).run s], inv z.2 :=
      evalDist.ae_of_forall_mem_support _ _ MeasurableSet.of_discrete fun z hz ↦ hinv t s hs z hz
    have hμ : Measure.map (fun z : spec.Range t × σ₂ ↦ (z.1, f z.2))
        ((𝒟[(impl₂ t).run s]).restrict {z | ¬bad z.2}) ≤ 𝒟[(impl₁ t).run (f s)] := by
      refine Measure.le_iff.2 fun A _ ↦ ?_
      rw [Measure.map_apply Measurable.of_discrete MeasurableSet.of_discrete,
        Measure.restrict_apply MeasurableSet.of_discrete]
      have := h t s hs hb (· ∈ A)
      simpa only [prEvent_eq_evalDist_of_discrete, Set.inter_def, Set.mem_ofPred_eq,
        Set.mem_preimage, Set.ofPred_mem_eq] using this
    calc _ = ∫⁻ z in {z | ¬bad z.2}, Pr{let w ← (simulateQ impl₂ (k z.1)).run z.2}[
            P (w.1, f w.2) ∧ ¬bad w.2] ∂𝒟[(impl₂ t).run s] :=
          (setLIntegral_eq_of_support_subset hsupp).symm
      _ ≤ ∫⁻ z in {z | ¬bad z.2}, g (z.1, f z.2) ∂𝒟[(impl₂ t).run s] :=
          setLIntegral_mono_ae Measurable.of_discrete.aemeasurable
            (hae.mono fun z hz _ ↦ ih z.1 z.2 hz)
      _ = ∫⁻ y, g y ∂(Measure.map (fun z : spec.Range t × σ₂ ↦ (z.1, f z.2))
            ((𝒟[(impl₂ t).run s]).restrict {z | ¬bad z.2})) :=
          (lintegral_map Measurable.of_discrete Measurable.of_discrete).symm
      _ ≤ _ := lintegral_mono' hμ le_rfl

/-- **Projection until bad, event form.** Under the hypotheses of
`QueryImpl.prEvent_simulateQ_run_map_and_not_bad_le`, an event of the run of `impl₁` from the
mapped state is at most the same event, read through `f`, or `bad`, in the run of `impl₂`. -/
theorem prEvent_simulateQ_run_le_map_or_bad (f : σ₂ → σ₁) {inv bad : σ₂ → Prop}
    (hinv : PreservesInv impl₂ inv) (hbad : PreservesInv impl₂ bad)
    (h : ∀ t s, inv s → ¬bad s → ∀ Q : spec.Range t × σ₁ → Prop,
      Pr{let z ← (impl₂ t).run s}[Q (z.1, f z.2) ∧ ¬bad z.2] ≤
        Pr{let z ← (impl₁ t).run (f s)}[Q z])
    (oa : OracleComp spec α) (s : σ₂) (hs : inv s) (P : α × σ₁ → Prop) :
    Pr{let z ← (simulateQ impl₁ oa).run (f s)}[P z] ≤
      Pr{let z ← (simulateQ impl₂ oa).run s}[P (z.1, f z.2) ∨ bad z.2] := by
  have hcore := prEvent_simulateQ_run_map_and_not_bad_le f hinv hbad h oa s hs fun z ↦ ¬P z
  have e₁ := prEvent_add_prEvent_not_eq_prEvent_true ((simulateQ impl₁ oa).run (f s)) P
  have e₂ := prEvent_add_prEvent_not_eq_prEvent_true ((simulateQ impl₂ oa).run s)
    fun z ↦ P (z.1, f z.2) ∨ bad z.2
  rw [prEvent_true_eq_one] at e₁ e₂
  refine ENNReal.le_of_add_le_add_right
    (ne_top_of_le_ne_top ENNReal.one_ne_top
      (prEvent_le_one ((simulateQ impl₁ oa).run (f s)) fun z ↦ ¬P z)) ?_
  rw [e₁, ← e₂]
  refine add_le_add le_rfl (le_trans (le_of_eq ?_) hcore)
  exact prEvent_congr _ _ _ fun z ↦ not_or

end Projection

end QueryImpl
