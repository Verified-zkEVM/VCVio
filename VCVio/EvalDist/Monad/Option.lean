/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module
public import VCVio.EvalDist.Defs.Measure.OptionT
public import VCVio.EvalDist.ProbabilityNotation

/-!
# Events of optional computations

Native successful-output semantics turns a sampled guard into a condition on the sampled value.
The intermediate measurable space is internal to the observation law.
-/

public section

open MeasureTheory

universe v

namespace OptionT

/-- A guard contributes its condition to the observed event after a lifted draw. -/
@[simp↓ high, grind norm↓]
theorem prEvent_bind_guard {m : Type → Type v} [Monad m] [LawfulMonad m]
    [EvalDistSemantics m] [LawfulEvalDistSemantics m]
    {α : Type} (mx : m α) (p q : α → Prop) [DecidablePred p] :
    Pr{let x ← OptionT.lift mx; guard (p x)}[q x] =
      Pr{let x ← mx}[p x ∧ q x] := by
  classical
  let : MeasurableSpace α := ⊤
  have h (x : α) : Pr{let _ ← (guard (p x) : OptionT m Unit)}[q x] =
      if p x ∧ q x then 1 else 0 := by
    by_cases hp : p x <;> by_cases hq : q x <;> simp [guard, hp, hq]
  rw [_root_.evalDist_bind_of_discrete,
    Measure.bind_apply (measurableSet_singleton True) Measurable.of_discrete.aemeasurable,
    OptionT.evalDist_lift]
  simp_rw [h]
  rw [prEvent_eq_evalDist_of_discrete]
  simpa only [Set.indicator_apply, Pi.one_apply, Set.mem_ofPred_eq] using
    lintegral_indicator_one (μ := 𝒟[mx]) (MeasurableSet.of_discrete (s := {x | p x ∧ q x}))

end OptionT
