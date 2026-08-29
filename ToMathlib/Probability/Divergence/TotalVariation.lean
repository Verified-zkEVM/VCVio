/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import ToMathlib.Data.ENNReal.AbsDiff
public import Mathlib.MeasureTheory.Integral.MeanInequalities

/-!
# Total variation against the Hellinger affinity

For two densities against a common measure, this is the inequality `TV² ≤ 1 - BC²`, where `BC` is
the Hellinger affinity (the Bhattacharyya coefficient in the discrete case). It is one of the two
halves of the Renyi-to-total-variation bound; the other is log-convexity of the Renyi moment
generating function, in `ToMathlib.Probability.Divergence.Renyi`.

## The argument

Writing `m = ∫ min f g` and `M = ∫ max f g`, the two pointwise identities `min + max = f + g` and
`|f - g| + 2·min f g = f + g` give `m + M = 2` and `TV + m = 1`, hence `M = 1 + TV`. Since
`min · max = f · g`, Cauchy-Schwarz — Hölder at exponents `1/2` and `1/2`, so the *same*
`ENNReal.lintegral_mul_norm_pow_le` that powers the log-convexity step — bounds
`BC ≤ m^{1/2} M^{1/2}`, whence `BC² ≤ m·M` and `BC² + TV² ≤ 1`.

Stating it for a pair of densities rather than a pair of measures keeps it free of
Radon-Nikodym bookkeeping, and lets the discrete corollary instantiate at a counting measure while
a measure-level one instantiates at `Measure.rnDeriv` against a common dominating measure.

The whole argument is additive: `BC² + TV² ≤ 1` is established first, and truncated subtraction
appears only in the final restatement.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace InformationTheory

variable {α : Type*} [MeasurableSpace α]

/-- **Total variation is controlled by the Hellinger affinity**, for two densities against a
common measure. -/
theorem lintegral_absDiff_div_two_rpow_two_le (μ : Measure α) {f g : α → ℝ≥0∞}
    (hf : AEMeasurable f μ) (hg : AEMeasurable g μ)
    (hf1 : ∫⁻ x, f x ∂μ = 1) (hg1 : ∫⁻ x, g x ∂μ = 1) :
    ((∫⁻ x, ENNReal.absDiff (f x) (g x) ∂μ) / 2) ^ (2:ℝ)
      ≤ 1 - (∫⁻ x, (f x * g x) ^ (1/2:ℝ) ∂μ) ^ (2:ℝ) := by
  set m := ∫⁻ x, f x ⊓ g x ∂μ with hm
  set M := ∫⁻ x, f x ⊔ g x ∂μ with hMdef
  set D := ∫⁻ x, ENNReal.absDiff (f x) (g x) ∂μ with hD
  set T := D / 2 with hT
  have hmin : AEMeasurable (fun x => f x ⊓ g x) μ := hf.inf hg
  have habs : AEMeasurable (fun x => ENNReal.absDiff (f x) (g x)) μ :=
    (hf.sub hg).add (hg.sub hf)
  have hmM : m + M = 2 := by
    have h := lintegral_congr (μ := μ) (fun x => min_add_max (f x) (g x))
    rw [lintegral_add_left' hmin, lintegral_add_left' hf, hf1, hg1] at h
    rw [hm, hMdef, h]; norm_num
  have hDm : D + 2 * m = 2 := by
    have h := lintegral_congr (μ := μ) (fun x => ENNReal.absDiff_add_two_mul_min (f x) (g x))
    rw [lintegral_add_left' habs, lintegral_const_mul' _ _ (by norm_num : (2:ℝ≥0∞) ≠ ⊤),
      lintegral_add_left' hf, hf1, hg1] at h
    rw [hD, hm, h]; norm_num
  have hmT : T + m = 1 := by
    have h2 : (D + 2 * m) / 2 = 2 / 2 := by rw [hDm]
    rwa [ENNReal.add_div, mul_comm (2:ℝ≥0∞) m,
      ENNReal.mul_div_cancel_right (by norm_num) (by norm_num),
      ENNReal.div_self (by norm_num) (by norm_num)] at h2
  have hmtop : m ≠ ⊤ := by
    intro h; rw [h, add_top] at hmT; exact ENNReal.top_ne_one hmT
  have hM : M = 1 + T := by
    refine (ENNReal.add_right_inj hmtop).mp ?_
    rw [hmM, show m + (1 + T) = (T + m) + 1 from by ring, hmT]
    norm_num
  have hMtop : M ≠ ⊤ := by
    intro h; rw [h] at hmM; simp at hmM
  set B := ∫⁻ x, (f x * g x) ^ (1/2:ℝ) ∂μ with hB
  have hCS : B ≤ m ^ (1/2:ℝ) * M ^ (1/2:ℝ) := by
    have key := ENNReal.lintegral_mul_norm_pow_le (μ := μ)
      (f := fun x => f x ⊓ g x) (g := fun x => f x ⊔ g x) (p := 1/2) (q := 1/2)
      hmin (hf.sup hg) (by norm_num) (by norm_num) (by norm_num)
    refine le_trans (le_of_eq ?_) key
    refine lintegral_congr fun x => ?_
    rw [← ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), min_mul_max]
  have hB2 : B ^ (2:ℝ) ≤ m * M := by
    have h := ENNReal.rpow_le_rpow hCS (by norm_num : (0:ℝ) ≤ 2)
    rwa [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ← ENNReal.rpow_mul, ← ENNReal.rpow_mul,
      show (1/2:ℝ) * 2 = 1 by norm_num, ENNReal.rpow_one, ENNReal.rpow_one] at h
  have hkey : m * M + T ^ (2:ℝ) = 1 := by
    rw [hM, ENNReal.rpow_two, sq, mul_add, mul_one, add_assoc, ← add_mul,
      add_comm m T, hmT, one_mul, add_comm m T, hmT]
  have hsum : B ^ (2:ℝ) + T ^ (2:ℝ) ≤ 1 := by
    calc B ^ (2:ℝ) + T ^ (2:ℝ) ≤ m * M + T ^ (2:ℝ) := by gcongr
      _ = 1 := hkey
  have hBtop : B ^ (2:ℝ) ≠ ⊤ :=
    ne_top_of_le_ne_top (ENNReal.mul_ne_top hmtop hMtop) hB2
  exact ENNReal.le_sub_of_add_le_left hBtop hsum

end InformationTheory
