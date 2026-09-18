/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Devon Tuma
-/

module
public import VCVio.EvalDist.Defs.Measure.Core
public import ToMathlib.MeasureTheory.Integral.Quadratic

/-!
# Marginalized quadratic probability bounds

A per-output acceptance and extraction bound transports through a computation's successful-output
measure by Cauchy–Schwarz. The common draw may lose mass and its result space may be continuous.
Only the acceptance function needs almost-everywhere measurability; both bounds need hold only
almost everywhere. Discrete outputs provide a pointwise specialization.
-/

public section

open MeasureTheory
open scoped ENNReal

universe u v

namespace OracleComp.EvalDist

variable {m : Type u → Type v} [EvalDistSemantics m]

/-- A per-output forking bound transports through the successful-output measure of a common draw. -/
lemma marginalized_jensen_forking_bound {X : Type u} [MeasurableSpace X] (mx : m X)
    (acc B : X → ENNReal) (q hinv : ENNReal) (hacc : AEMeasurable acc 𝒟[mx])
    (hacc_le : ∀ᵐ x ∂𝒟[mx], acc x ≤ 1)
    (hper : ∀ᵐ x ∂𝒟[mx], acc x * (acc x / q - hinv) ≤ B x) :
    (∫⁻ x, acc x ∂𝒟[mx]) * ((∫⁻ x, acc x ∂𝒟[mx]) / q - hinv) ≤ ∫⁻ x, B x ∂𝒟[mx] :=
  ENNReal.lintegral_mul_div_sub_le hacc q hinv hacc_le hper

/-- A discrete common draw needs only pointwise acceptance and extraction bounds. -/
lemma marginalized_jensen_forking_bound_of_discrete {X : Type u} [MeasurableSpace X]
    [DiscreteMeasurableSpace X] (mx : m X) (acc B : X → ENNReal) (q hinv : ENNReal)
    (hacc_le : ∀ x, acc x ≤ 1) (hper : ∀ x, acc x * (acc x / q - hinv) ≤ B x) :
    (∫⁻ x, acc x ∂𝒟[mx]) * ((∫⁻ x, acc x ∂𝒟[mx]) / q - hinv) ≤ ∫⁻ x, B x ∂𝒟[mx] :=
  marginalized_jensen_forking_bound mx acc B q hinv Measurable.of_discrete.aemeasurable
    (Filter.Eventually.of_forall hacc_le) (Filter.Eventually.of_forall hper)

/-- Acceptance and extraction observations satisfy the marginalized bound without choosing a
measurable space on the common draw's intermediate result. -/
lemma marginalized_jensen_forking_bound_map {m : Type → Type v} [Monad m] [LawfulMonad m]
    [EvalDistSemantics m] [LawfulEvalDistSemantics m] {X : Type}
    (mx : m X) (acc B : X → ENNReal) (q hinv : ENNReal)
    (hacc_le : ∀ x, acc x ≤ 1) (hper : ∀ x, acc x * (acc x / q - hinv) ≤ B x) :
    (∫⁻ a, a ∂𝒟[acc <$> mx]) * ((∫⁻ a, a ∂𝒟[acc <$> mx]) / q - hinv) ≤
      ∫⁻ b, b ∂𝒟[B <$> mx] := by
  let : MeasurableSpace X := ⊤
  rw [lintegral_evalDist_map mx (f := acc) Measurable.of_discrete
    (g := fun a ↦ a) measurable_id,
    lintegral_evalDist_map mx (f := B) Measurable.of_discrete
      (g := fun b ↦ b) measurable_id]
  exact marginalized_jensen_forking_bound_of_discrete mx acc B q hinv hacc_le hper

end OracleComp.EvalDist
