/-
Copyright (c) 2026 XC0R. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XC0R
-/

module
public import LatticeCrypto.DiscreteGaussian.ThetaTail

/-!
# The sub-Gaussian moment bound of the discrete Gaussian

For `z ~ D_{ℤ,σ,c}` (`discreteGaussianMeasure σ c`) and real `s`, completing the square gives
`E[exp(s(z - c))] = exp(σ²s²/2) · S(σ, c + σ²s) / S(σ, c)` (`tsum_pmf_mul_exp`), and the bounds on
the normalizer from `discreteGaussianSum_eq_fourier` give `E[exp(s(z - c))] ≤ κ(σ) exp(σ²s²/2)`
with `κ(σ) = (1 + T(σ))/(1 - T(σ))` (`lintegral_exp_le`). For `σ ≥ 1.277`, `κ(σ) ≤ 1 + 2⁻³⁶`
(`kappa_le_of_le`). This is the moment bound behind Lemma 1 of De Almeida Braga, Fouque, Lachguel
and Prest, ePrint 2026/1531 ([Lyu12, Lemma 4.3]), for a discrete Gaussian at any centre, with the
factor `κ(σ)`.
-/

public section

open Real MeasureTheory
open scoped ENNReal

namespace LatticeCrypto.Theta

/-- `κ(σ) = (1 + T(σ))/(1 - T(σ))`. -/
@[expose] noncomputable def kappa (σ : ℝ) : ℝ := (1 + tail σ) / (1 - tail σ)

/-- The normalizer is `σ√(2π)` up to the relative error `T(σ)`. -/
theorem discreteGaussianSum_mem (σ u : ℝ) (hσ : 0 < σ) :
    σ * √(2 * π) * (1 - tail σ) ≤ discreteGaussianSum σ u ∧
      discreteGaussianSum σ u ≤ σ * √(2 * π) * (1 + tail σ) := by
  have he : discreteGaussianSum σ u = σ * √(2 * π) * series σ u :=
    discreteGaussianSum_eq_fourier σ u hσ
  obtain ⟨h1, h2⟩ := series_mem σ u hσ
  have hc : 0 ≤ σ * √(2 * π) := by positivity
  rw [he]
  exact ⟨mul_le_mul_of_nonneg_left h1 hc, mul_le_mul_of_nonneg_left h2 hc⟩

theorem tail_nonneg (σ : ℝ) (hσ : 0 < σ) : 0 ≤ tail σ := by
  obtain ⟨h1, h2⟩ := discreteGaussianSum_mem σ 0 hσ
  have := le_of_mul_le_mul_left (h1.trans h2) (by positivity)
  linarith

theorem kappa_pos (σ : ℝ) (hσ : 0 < σ) (hT : tail σ < 1) : 0 < kappa σ :=
  div_pos (by linarith [tail_nonneg σ hσ]) (by linarith)

theorem weight_mul_exp (σ c s : ℝ) (hσ : 0 < σ) (z : ℤ) :
    discreteGaussianWeight σ c z * Real.exp (s * (z - c)) =
      Real.exp (σ ^ 2 * s ^ 2 / 2) * discreteGaussianWeight σ (c + σ ^ 2 * s) z := by
  have : σ ≠ 0 := hσ.ne'
  simp only [discreteGaussianWeight, ← Real.exp_add]
  congr 1
  field_simp
  ring

theorem pmf_mul_exp (σ c s : ℝ) (hσ : 0 < σ) (z : ℤ) :
    discreteGaussianPMF σ c z * Real.exp (s * (z - c)) =
      Real.exp (σ ^ 2 * s ^ 2 / 2) * discreteGaussianWeight σ (c + σ ^ 2 * s) z /
        discreteGaussianSum σ c := by
  rw [discreteGaussianPMF, div_mul_eq_mul_div, weight_mul_exp σ c s hσ]

theorem summable_pmf_mul_exp (σ c s : ℝ) (hσ : 0 < σ) :
    Summable fun z : ℤ => discreteGaussianPMF σ c z * Real.exp (s * (z - c)) :=
  (((discreteGaussianSum_summable σ (c + σ ^ 2 * s) hσ).mul_left
    (Real.exp (σ ^ 2 * s ^ 2 / 2))).div_const (discreteGaussianSum σ c)).congr
      fun z => (pmf_mul_exp σ c s hσ z).symm

/-- **Moment generating function** of `z - c`, `z ~ D_{ℤ,σ,c}`. -/
theorem tsum_pmf_mul_exp (σ c s : ℝ) (hσ : 0 < σ) :
    ∑' z : ℤ, discreteGaussianPMF σ c z * Real.exp (s * (z - c)) =
      Real.exp (σ ^ 2 * s ^ 2 / 2) * discreteGaussianSum σ (c + σ ^ 2 * s) /
        discreteGaussianSum σ c := by
  rw [tsum_congr (pmf_mul_exp σ c s hσ), tsum_div_const, tsum_mul_left]
  rfl

/-- Normalizers at two centres differ by at most the factor `κ(σ)`. -/
theorem sum_div_sum_le (σ c u : ℝ) (hσ : 0 < σ) (hT : tail σ < 1) :
    discreteGaussianSum σ u / discreteGaussianSum σ c ≤ kappa σ := by
  have h1 := (discreteGaussianSum_mem σ u hσ).2
  have h2 := (discreteGaussianSum_mem σ c hσ).1
  have h0 : 0 < 1 - tail σ := by linarith
  rw [div_le_iff₀ (discreteGaussianSum_pos σ c hσ)]
  calc discreteGaussianSum σ u ≤ σ * √(2 * π) * (1 + tail σ) := h1
    _ = kappa σ * (σ * √(2 * π) * (1 - tail σ)) := by rw [kappa]; field_simp
    _ ≤ kappa σ * discreteGaussianSum σ c := mul_le_mul_of_nonneg_left h2 (kappa_pos σ hσ hT).le

theorem lintegral_exp_eq (σ c s : ℝ) (hσ : 0 < σ) :
    ∫⁻ z, ENNReal.ofReal (Real.exp (s * (z - c))) ∂discreteGaussianMeasure σ c =
      ENNReal.ofReal (∑' z : ℤ, discreteGaussianPMF σ c z * Real.exp (s * (z - c))) := by
  rw [discreteGaussianMeasure, lintegral_withDensity_eq_lintegral_mul _
    (measurable_of_countable _) (measurable_of_countable _), lintegral_count,
    ENNReal.ofReal_tsum_of_nonneg
      (fun z => mul_nonneg (discreteGaussianPMF_nonneg σ c hσ z) (Real.exp_pos _).le)
      (summable_pmf_mul_exp σ c s hσ)]
  refine tsum_congr fun z => ?_
  rw [Pi.mul_apply, ENNReal.ofReal_mul (discreteGaussianPMF_nonneg σ c hσ z)]

/-- **Sub-Gaussian moment bound**: `E[exp(s(z - c))] ≤ κ(σ) exp(σ²s²/2)`, `z ~ D_{ℤ,σ,c}`. -/
theorem lintegral_exp_le (σ c s : ℝ) (hσ : 0 < σ) (hT : tail σ < 1) :
    ∫⁻ z, ENNReal.ofReal (Real.exp (s * (z - c))) ∂discreteGaussianMeasure σ c ≤
      ENNReal.ofReal (kappa σ * Real.exp (σ ^ 2 * s ^ 2 / 2)) := by
  rw [lintegral_exp_eq σ c s hσ, tsum_pmf_mul_exp σ c s hσ]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [mul_div_assoc, mul_comm (kappa σ)]
  exact mul_le_mul_of_nonneg_left (sum_div_sum_le σ c _ hσ hT) (Real.exp_pos _).le

/-- **The Falcon leaf range**: for `σ ≥ 1.277`, `T(σ) < 1` and `κ(σ) ≤ 1 + 2⁻³⁶`. -/
theorem kappa_le_of_le (σ : ℝ) (hσ : 1277 / 1000 ≤ σ) :
    tail σ < 1 ∧ kappa σ ≤ 1 + 1 / 2 ^ 36 := by
  have hσ0 : 0 < σ := by linarith
  have hT := (tail_le σ (1 / 2 ^ 40) hσ0 (four_mul_exp_le σ hσ) (by norm_num)).1
  have hT' : tail σ ≤ 1 / 2 ^ 38 := hT.trans (by norm_num)
  refine ⟨by linarith, ?_⟩
  rw [kappa, div_le_iff₀ (by linarith)]
  nlinarith [hT', tail_nonneg σ hσ0]

end LatticeCrypto.Theta
