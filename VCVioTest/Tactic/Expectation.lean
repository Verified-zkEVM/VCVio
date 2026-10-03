/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import VCVio.EvalDist.Defs.Measure.Core

/-!
# Structural simplification of expectations

An expectation is an integral against the output measure. Mapping a computation precomposes the
payoff without unfolding the integral. These tests need only discrete measurable structures on the
outputs, with no support semantics or losslessness assumptions. The negative probe isolates the
contribution of the map rule.
-/

public section

open MeasureTheory
open scoped ENNReal

namespace VCVioTest.Tactic.Expectation

universe u v

variable {m : Type u → Type v} [Monad m] [LawfulMonad m] [EvalDistSemantics m]
  [LawfulEvalDistSemantics m] {α β γ : Type u}
  [MeasurableSpace α] [DiscreteMeasurableSpace α] [MeasurableSpace β] [DiscreteMeasurableSpace β]
  [MeasurableSpace γ] [DiscreteMeasurableSpace γ]

example (mx : m α) (f : α → β) (g : β → ℝ≥0∞) :
    ∫⁻ y, g y ∂𝒟[f <$> mx] = ∫⁻ x, g (f x) ∂𝒟[mx] := by simp

example (mx : m α) (f : α → β) (g : β → γ) (h : γ → ℝ≥0∞) :
    ∫⁻ z, h z ∂𝒟[g <$> (f <$> mx)] = ∫⁻ x, h (g (f x)) ∂𝒟[mx] := by simp

example (mx : m α) (f : Fin 3 → α → β) (g : β → ℝ≥0∞) :
    ∑ i, ∫⁻ y, g y ∂𝒟[f i <$> mx] = ∑ i, ∫⁻ x, g (f i x) ∂𝒟[mx] := by simp

/-- Without the map rule, a generic mapped expectation is not simplified. -/
example (mx : m α) (f : α → β) (g : β → ℝ≥0∞) :
    ∫⁻ y, g y ∂𝒟[f <$> mx] = ∫⁻ x, g (f x) ∂𝒟[mx] := by
  fail_if_success solve | simp [-lintegral_evalDist_map_of_discrete]
  simp

end VCVioTest.Tactic.Expectation
