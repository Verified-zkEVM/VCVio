/-
Copyright (c) 2026 XC0R. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XC0R
-/

module
public import LatticeCrypto.DiscreteGaussian.ThetaTail
public import ToMathlib.Analysis.Calculus.TaylorSecondOrder
public import ToMathlib.Probability.Divergence.RenyiChain

/-!
# Rényi divergence between shifted discrete Gaussians

For `a > 1`, completing the square gives the Hellinger sum of two discrete Gaussians with the same
width `σ` and centres `c + δ` and `c` in closed form (`renyiMGF_discreteGaussianMeasure_add`):

`∑_x D_{σ,c+δ}(x)^a D_{σ,c}(x)^(1-a)`
`  = exp(a(a-1)δ²/(2σ²)) · ρσ(ℤ-c-aδ) / (ρσ(ℤ-c-δ)^a ρσ(ℤ-c)^(1-a))`.

Writing each normalizer as `σ√(2π) · Theta.series σ ·` (Poisson summation), the normalizer ratio
is the exponential of a second difference of `log (Theta.series σ ·)`, which the second-order
Taylor bound controls by `Theta.curvature σ`. For `Theta.tail σ < 1` this gives
(`renyiDiv_discreteGaussianMeasure_add_le`)

`R_a(D_{σ,c+δ} ‖ D_{σ,c}) ≤ exp(aδ²/(2σ²) + a(a+1)δ² · Theta.curvature σ / (2(a-1)))`.

This is Lemma 4 of De Almeida Braga, Fouque, Lachguel and Prest, *Toward a Secure Fixed-Point
Implementation of the Falcon Signature Scheme* (ePrint 2026/1531), with its `O(ε)` term replaced by
the explicit `Theta.curvature σ`; `Theta.tail_lt_one_and_curvature_le` bounds it by `2^(-30)` for
`σ ≥ 1.277`.
-/

public section

open Real MeasureTheory InformationTheory
open scoped ENNReal

namespace LatticeCrypto

/-- Completing the square: the Hellinger weight of two shifted Gaussian weights is a Gaussian
weight at the `a`-shifted centre. -/
theorem discreteGaussianWeight_rpow_mul_rpow (σ c δ a : ℝ) (x : ℤ) :
    discreteGaussianWeight σ (c + δ) x ^ a * discreteGaussianWeight σ c x ^ (1 - a) =
      Real.exp (a * (a - 1) * δ ^ 2 / (2 * σ ^ 2)) * discreteGaussianWeight σ (c + a * δ) x := by
  simp only [discreteGaussianWeight, ← Real.exp_mul, ← Real.exp_add]
  congr 1
  ring

theorem discreteGaussianPMF_rpow_mul_rpow (σ c δ a : ℝ) (hσ : 0 < σ) (x : ℤ) :
    discreteGaussianPMF σ (c + δ) x ^ a * discreteGaussianPMF σ c x ^ (1 - a) =
      Real.exp (a * (a - 1) * δ ^ 2 / (2 * σ ^ 2)) * discreteGaussianWeight σ (c + a * δ) x /
        (discreteGaussianSum σ (c + δ) ^ a * discreteGaussianSum σ c ^ (1 - a)) := by
  have hS : ∀ μ, 0 < discreteGaussianSum σ μ := fun μ => discreteGaussianSum_pos σ μ hσ
  simp only [discreteGaussianPMF]
  rw [Real.div_rpow (discreteGaussianWeight_nonneg _ _ _) (hS _).le,
    Real.div_rpow (discreteGaussianWeight_nonneg _ _ _) (hS _).le, div_mul_div_comm,
    discreteGaussianWeight_rpow_mul_rpow]

/-- The Hellinger sum of two shifted discrete Gaussian PMFs. -/
theorem tsum_discreteGaussianPMF_rpow_mul_rpow (σ c δ a : ℝ) (hσ : 0 < σ) :
    ∑' x : ℤ, discreteGaussianPMF σ (c + δ) x ^ a * discreteGaussianPMF σ c x ^ (1 - a) =
      Real.exp (a * (a - 1) * δ ^ 2 / (2 * σ ^ 2)) * discreteGaussianSum σ (c + a * δ) /
        (discreteGaussianSum σ (c + δ) ^ a * discreteGaussianSum σ c ^ (1 - a)) := by
  rw [tsum_congr (discreteGaussianPMF_rpow_mul_rpow σ c δ a hσ), tsum_div_const, tsum_mul_left]
  rfl

/-- **The Rényi MGF between shifted discrete Gaussians**, in closed form. -/
theorem renyiMGF_discreteGaussianMeasure_add (σ c δ a : ℝ) (hσ : 0 < σ) (ha : 1 < a) :
    renyiMGF a (discreteGaussianMeasure σ (c + δ)) (discreteGaussianMeasure σ c) =
      ENNReal.ofReal
        (Real.exp (a * (a - 1) * δ ^ 2 / (2 * σ ^ 2)) * discreteGaussianSum σ (c + a * δ) /
          (discreteGaussianSum σ (c + δ) ^ a * discreteGaussianSum σ c ^ (1 - a))) := by
  have := isProbabilityMeasure_discreteGaussianMeasure σ c hσ
  have := isProbabilityMeasure_discreteGaussianMeasure σ (c + δ) hσ
  have hpos : ∀ μ (x : ℤ), 0 < discreteGaussianPMF σ μ x :=
    fun μ x => discreteGaussianPMF_pos σ μ hσ x
  rw [renyiMGF_eq_tsum ha, ← tsum_discreteGaussianPMF_rpow_mul_rpow σ c δ a hσ,
    ENNReal.ofReal_tsum_of_nonneg
      (fun x => mul_nonneg (Real.rpow_nonneg (hpos _ x).le _) (Real.rpow_nonneg (hpos _ x).le _))]
  · refine tsum_congr fun x => ?_
    rw [discreteGaussianMeasure_singleton, discreteGaussianMeasure_singleton,
      ENNReal.ofReal_rpow_of_pos (hpos _ x), ENNReal.ofReal_rpow_of_pos (hpos _ x),
      ← ENNReal.ofReal_mul (Real.rpow_nonneg (hpos _ x).le _)]
  · refine Summable.congr ?_ (fun x => (discreteGaussianPMF_rpow_mul_rpow σ c δ a hσ x).symm)
    exact ((discreteGaussianSum_summable σ (c + a * δ) hσ).mul_left _).div_const _

namespace Theta

private theorem sum_eq (σ u : ℝ) (hσ : 0 < σ) :
    discreteGaussianSum σ u = σ * √(2 * π) * series σ u := by
  rw [discreteGaussianSum_eq_fourier σ u hσ]; rfl

private theorem series_pos (σ u : ℝ) (hσ : 0 < σ) (hT : tail σ < 1) : 0 < series σ u := by
  linarith [(series_mem σ u hσ).1]

/-- The second difference of `log (series σ ·)` at `c`, `c + δ`, `c + aδ`. -/
private noncomputable def logDiff (σ c δ a : ℝ) : ℝ :=
  Real.log (series σ (c + a * δ)) - a * Real.log (series σ (c + δ)) -
    (1 - a) * Real.log (series σ c)

/-- The normalizer ratio of the closed form is `exp` of the second difference. -/
private theorem ratio_eq (σ c δ a : ℝ) (hσ : 0 < σ) (hT : tail σ < 1) :
    discreteGaussianSum σ (c + a * δ) /
        (discreteGaussianSum σ (c + δ) ^ a * discreteGaussianSum σ c ^ (1 - a)) =
      Real.exp (logDiff σ c δ a) := by
  have hK : 0 < σ * √(2 * π) := by positivity
  have h1 := series_pos σ (c + a * δ) hσ hT
  have h2 := series_pos σ (c + δ) hσ hT
  have h3 := series_pos σ c hσ hT
  rw [sum_eq _ _ hσ, sum_eq _ _ hσ, sum_eq _ _ hσ, Real.mul_rpow hK.le h2.le,
    Real.mul_rpow hK.le h3.le]
  have hKK : (σ * √(2 * π)) ^ a * (σ * √(2 * π)) ^ (1 - a) = σ * √(2 * π) := by
    rw [← Real.rpow_add hK]; simp
  set K := σ * √(2 * π)
  rw [show K ^ a * series σ (c + δ) ^ a * (K ^ (1 - a) * series σ c ^ (1 - a)) =
      (K ^ a * K ^ (1 - a)) * (series σ (c + δ) ^ a * series σ c ^ (1 - a)) by ring, hKK,
    mul_div_mul_left _ _ hK.ne', logDiff,
    show Real.log (series σ (c + a * δ)) - a * Real.log (series σ (c + δ)) -
        (1 - a) * Real.log (series σ c) = Real.log (series σ (c + a * δ)) -
          (Real.log (series σ (c + δ)) * a + Real.log (series σ c) * (1 - a)) by ring,
    Real.exp_sub, Real.exp_add, Real.exp_log h1, ← Real.rpow_def_of_pos h2,
    ← Real.rpow_def_of_pos h3]

/-- The second difference is a Taylor remainder: `|Δ| ≤ curvature σ · a(a+1)δ²/2`. -/
private theorem abs_logDiff_le (σ c δ a : ℝ) (hσ : 0 < σ) (hT : tail σ < 1) (ha : 0 ≤ a) :
    |logDiff σ c δ a| ≤ curvature σ * (a * (a + 1)) * δ ^ 2 / 2 := by
  set L : ℝ → ℝ := fun v => Real.log (series σ v)
  set D : ℝ := series₁ σ c / series σ c
  have hT' := fun x h => Real.abs_taylor_two_sub_le (g := L)
    (g' := fun v => series₁ σ v / series σ v)
    (g'' := fun v => (series₂ σ v * series σ v - series₁ σ v * series₁ σ v) / series σ v ^ 2)
    (hasDerivAt_log_series σ hσ hT) (hasDerivAt_series₁_div_series σ hσ hT)
    (abs_deriv2_log_series_le σ hσ hT) x h
  have hA : |L (c + a * δ) - L c - a * δ * D| ≤ curvature σ * (a * δ) ^ 2 / 2 := hT' c (a * δ)
  have hB : |L (c + δ) - L c - δ * D| ≤ curvature σ * δ ^ 2 / 2 := hT' c δ
  have hid : logDiff σ c δ a = (L (c + a * δ) - L c - a * δ * D) - a * (L (c + δ) - L c - δ * D) :=
    by simp only [logDiff, L]; ring
  rw [hid]
  calc _ ≤ |L (c + a * δ) - L c - a * δ * D| + |a * (L (c + δ) - L c - δ * D)| := abs_sub _ _
    _ ≤ curvature σ * (a * δ) ^ 2 / 2 + a * (curvature σ * δ ^ 2 / 2) := by
        rw [abs_mul, abs_of_nonneg ha]; gcongr
    _ = _ := by ring

end Theta

/-- **Rényi divergence between shifted discrete Gaussians**, with an explicit second-order term:
for `a > 1` and `Theta.tail σ < 1`,
`R_a(D_{σ,c+δ} ‖ D_{σ,c}) ≤ exp(aδ²/(2σ²) + a(a+1)δ² · Theta.curvature σ / (2(a-1)))`. -/
theorem renyiDiv_discreteGaussianMeasure_add_le (σ c δ a : ℝ) (hσ : 0 < σ) (ha : 1 < a)
    (hT : Theta.tail σ < 1) :
    renyiDiv a (discreteGaussianMeasure σ (c + δ)) (discreteGaussianMeasure σ c) ≤
      ENNReal.ofReal (Real.exp
        (a * δ ^ 2 / (2 * σ ^ 2) + a * (a + 1) * δ ^ 2 * Theta.curvature σ / (2 * (a - 1)))) := by
  have ha0 : 0 ≤ a := by linarith
  have ham : 0 < a - 1 := by linarith
  rw [renyiDiv_eq_rpow ha, renyiMGF_discreteGaussianMeasure_add σ c δ a hσ ha, mul_div_assoc,
    Theta.ratio_eq σ c δ a hσ hT, ← Real.exp_add]
  have hΔ := (le_abs_self _).trans (Theta.abs_logDiff_le σ c δ a hσ hT ha0)
  calc ENNReal.ofReal (Real.exp (a * (a - 1) * δ ^ 2 / (2 * σ ^ 2) +
        Theta.logDiff σ c δ a)) ^ (a - 1)⁻¹
      ≤ ENNReal.ofReal (Real.exp (a * (a - 1) * δ ^ 2 / (2 * σ ^ 2) +
          Theta.curvature σ * (a * (a + 1)) * δ ^ 2 / 2)) ^ (a - 1)⁻¹ := by
        gcongr
    _ = _ := by
        rw [ENNReal.ofReal_rpow_of_nonneg (Real.exp_pos _).le (inv_nonneg.2 ham.le),
          ← Real.exp_mul]
        congr 2
        field_simp

end LatticeCrypto
