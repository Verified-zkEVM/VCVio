/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module
public import VCVio.EvalDist.Defs.Measure.Core
public import ToMathlib.MeasureTheory.Measure.Coupling.Discard

/-!
# Discarding exceptional initial states in probabilistic programs

The explicit residual subcoupling for state laws bounds replacement of a continuation by the
mass of the initial states on which their output laws may differ. Both continuations may fail.
-/

public section

open MeasureTheory

universe u v

variable {m : Type u → Type v} [Monad m] [EvalDistSemantics m]
  [LawfulEvalDistSemantics m] {α β : Type u} [MeasurableSpace α] [MeasurableSpace β]

/-- Replace a continuation outside an exceptional initial-state event. The event's mass is
charged under the actual initial law, and no successful-output mass is silently normalized. -/
theorem evalDist_bind_apply_le_of_discard (mx : m α) (f g : α → m β)
    (hf : Measurable fun a => 𝒟[f a]) (hg : Measurable fun a => 𝒟[g a])
    {bad : Set α} (hbad : MeasurableSet bad)
    (heq : ∀ᵐ a ∂𝒟[mx], a ∉ bad → 𝒟[f a] = 𝒟[g a])
    {event : Set β} (hevent : MeasurableSet event) :
    𝒟[mx >>= f] event ≤ 𝒟[mx >>= g] event + 𝒟[mx] bad := by
  rw [evalDist_bind mx f hf, evalDist_bind mx g hg]
  exact Measure.bind_apply_le_of_discard 𝒟[mx] hf hg hbad heq hevent
