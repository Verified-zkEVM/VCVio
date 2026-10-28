/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma, Quang Dao
-/

module
public import ToMathlib.MeasureTheory.Measure.Subprobability
public import Mathlib.MeasureTheory.Integral.MeanInequalities
public import Mathlib.MeasureTheory.Integral.Lebesgue.Sub

/-!
# Quadratic bounds for nonnegative integrals

Hölder's inequality at exponent two gives Cauchy–Schwarz for arbitrary measures. For
subprobability measures it bounds the squared mean by the second moment. A bounded acceptance
function then transports a quadratic lower bound through integration, including for continuous
spaces and almost-everywhere bounds.
-/

public section

open MeasureTheory
open scoped ENNReal

namespace ENNReal

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-- Cauchy–Schwarz bounds the squared integral by the second moment times total mass. -/
lemma sq_lintegral_le_lintegral_sq_mul {f : α → ENNReal} (hf : AEMeasurable f μ) :
    (∫⁻ a, f a ∂μ) ^ 2 ≤ (∫⁻ a, f a ^ 2 ∂μ) * μ Set.univ := by
  have h := pow_le_pow_left' (lintegral_mul_le_Lp_mul_Lq μ
    Real.HolderConjugate.two_two hf (aemeasurable_const (b := (1 : ENNReal)))) 2
  simpa only [Pi.mul_apply, mul_one, one_rpow, lintegral_one, one_div, mul_pow,
    ← rpow_two, rpow_inv_rpow (by norm_num : (2 : ℝ) ≠ 0)] using h

/-- For a subprobability measure, the squared integral is bounded by the second moment. -/
lemma sq_lintegral_le_lintegral_sq [IsSubprobabilityMeasure μ] {f : α → ENNReal}
    (hf : AEMeasurable f μ) :
    (∫⁻ a, f a ∂μ) ^ 2 ≤ ∫⁻ a, f a ^ 2 ∂μ :=
  (sq_lintegral_le_lintegral_sq_mul hf).trans
    ((mul_le_mul' le_rfl (measure_univ_le μ)).trans_eq (mul_one _))

/-- A bounded acceptance function inherits its pointwise quadratic bound after integration.
The acceptance bounds and quadratic inequalities need hold only almost everywhere. -/
lemma lintegral_mul_div_sub_le [IsSubprobabilityMeasure μ] {acc B : α → ENNReal}
    (hacc : AEMeasurable acc μ) (q hinv : ENNReal)
    (hacc_le : ∀ᵐ a ∂μ, acc a ≤ 1)
    (hper : ∀ᵐ a ∂μ, acc a * (acc a / q - hinv) ≤ B a) :
    (∫⁻ a, acc a ∂μ) * ((∫⁻ a, acc a ∂μ) / q - hinv) ≤ ∫⁻ a, B a ∂μ := by
  have hmean : (∫⁻ a, acc a ∂μ) ≤ 1 :=
    (lintegral_mono_ae hacc_le).trans (by simpa using measure_univ_le μ)
  have hmean_ne_top := ne_top_of_le_ne_top one_ne_top hmean
  calc
    _ = (∫⁻ a, acc a ∂μ) ^ 2 / q - (∫⁻ a, acc a ∂μ) * hinv := by
      rw [ENNReal.mul_sub (fun _ _ ↦ hmean_ne_top), sq, mul_div_assoc]
    _ ≤ (∫⁻ a, acc a ^ 2 ∂μ) / q - (∫⁻ a, acc a ∂μ) * hinv := by
      gcongr
      exact sq_lintegral_le_lintegral_sq hacc
    _ = (∫⁻ a, acc a ^ 2 / q ∂μ) - ∫⁻ a, acc a * hinv ∂μ := by
      simp only [div_eq_mul_inv, lintegral_mul_const'' _ (hacc.pow_const (2 : ℕ)),
        lintegral_mul_const'' _ hacc]
    _ ≤ ∫⁻ a, acc a ^ 2 / q - acc a * hinv ∂μ :=
      lintegral_sub_le' _ _ (hacc.mul_const hinv)
    _ = ∫⁻ a, acc a * (acc a / q - hinv) ∂μ := by
      apply lintegral_congr_ae
      filter_upwards [hacc_le] with a ha
      rw [ENNReal.mul_sub (fun _ _ ↦ ne_top_of_le_ne_top one_ne_top ha), sq, mul_div_assoc]
    _ ≤ ∫⁻ a, B a ∂μ := lintegral_mono_ae hper

end ENNReal
