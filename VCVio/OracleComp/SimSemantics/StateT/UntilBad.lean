/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module

public import VCVio.OracleComp.SimSemantics.StateT.PreservesInv
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

## Main statements

- `QueryImpl.AgreeUntilBad`: agreement of two handlers on non-bad post-states.
- `QueryImpl.AgreeUntilBad.prEvent_simulateQ_run_and_not_bad_le`: the one-sided core.
- `QueryImpl.AgreeUntilBad.prEvent_simulateQ_run_and_not_bad_eq`: equal mass off the bad event.
- `QueryImpl.AgreeUntilBad.prEvent_simulateQ_run_bad_eq`: equal bad mass.
- `QueryImpl.AgreeUntilBad.prEvent_simulateQ_run_le_add_bad_left` and
  `QueryImpl.AgreeUntilBad.prEvent_simulateQ_run_le_add_bad_right`: an event of the first run
  exceeds the same event of the second by at most the bad mass of the first, respectively the
  second, run.

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

end QueryImpl
