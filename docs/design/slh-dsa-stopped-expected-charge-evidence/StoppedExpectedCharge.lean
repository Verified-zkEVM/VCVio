/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module
public import CostTail
public import ExpectedCharge

/-! # Expected potential charges under an independently stopped handler -/

public section
open OracleComp OracleSpec MeasureTheory
open scoped ENNReal

namespace OracleComp

/-- Freezing at an arbitrary prestate predicate preserves the original hazard charge. -/
theorem IsPotentialStep.stoppedAtBad
    {ι σ : Type} {spec : OracleSpec ι}
    (handler : QueryImpl spec (StateT σ ProbComp))
    (bad stopPredicate : σ → Prop) [DecidablePred stopPredicate] (potential : σ → ℝ≥0∞)
    (charged : IsPotentialStep handler bad potential)
    (fallback : (t : spec.Domain) → spec.Range t) :
    IsPotentialStep (handler.stoppedAtBad stopPredicate fallback) bad potential :=
 by
  constructor
  · intro t s z hz
    by_cases stopped : stopPredicate s
    · have same : z = (fallback t, s) := by
        simpa [QueryImpl.stoppedAtBad, stopped, support_pure, Set.mem_singleton_iff] using hz
      subst z
      exact le_rfl
    · apply charged.mono t s z
      simpa [QueryImpl.stoppedAtBad, stopped] using hz
  · intro t s good
    by_cases stopped : stopPredicate s
    · exact Or.inl ⟨fallback t, s, by simp [QueryImpl.stoppedAtBad, stopped], good⟩
    · simpa [QueryImpl.stoppedAtBad, stopped] using charged.step t s good

/-- A terminal hazard in the independently stopped run is paid by expected potential growth. -/
theorem prEvent_stopped_run_add_initial_potential_le_expected_final
    {ι σ α : Type} {spec : OracleSpec ι}
    (handler : QueryImpl spec (StateT σ ProbComp))
    (bad stopPredicate : σ → Prop) [DecidablePred stopPredicate] (potential : σ → ℝ≥0∞)
    (charged : IsPotentialStep handler bad potential)
    (fallback : (t : spec.Domain) → spec.Range t)
    (program : OracleComp spec α) (state : σ) (initiallyGood : ¬bad state) :
    Pr{let z ←
      ((simulateQ (handler.stoppedAtBad stopPredicate fallback) program).run state)}[bad z.2] +
      potential state ≤
        ∫⁻ r, r ∂𝒟[(fun z => potential z.2) <$>
          (simulateQ (handler.stoppedAtBad stopPredicate fallback) program).run state] :=
 by
  exact prEvent_run_add_initial_potential_le_expected_final
    (handler.stoppedAtBad stopPredicate fallback) bad potential
    (IsPotentialStep.stoppedAtBad handler bad stopPredicate potential charged fallback)
    program state initiallyGood

end OracleComp

#print axioms OracleComp.IsPotentialStep.stoppedAtBad
#print axioms OracleComp.prEvent_stopped_run_add_initial_potential_le_expected_final
