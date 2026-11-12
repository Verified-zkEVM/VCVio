/-
Copyright (c) 2026 XC0R. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XC0R
-/

module
public import LatticeCrypto.DiscreteGaussian
public import Mathlib.Analysis.SpecialFunctions.Gaussian.PoissonSummation
public import Mathlib.Analysis.Calculus.SmoothSeries
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# The theta tail of the discrete Gaussian normalizer

Poisson summation turns `ρσ(ℤ - u) = ∑ₙ exp(-(n - u)²/(2σ²))` into
`σ√(2π) ∑ₙ exp(-2π²σ²n²) cos(2πnu)` (`discreteGaussianSum_eq_fourier`), so the normalizer is
`σ√(2π)` up to the relative error `Theta.tail σ = ∑_{n ≠ 0} exp(-2π²σ²n²)`.

Writing the normalizer as `σ√(2π) · Theta.series σ u`, the function `log (Theta.series σ ·)` has
second derivative bounded by `Theta.curvature σ`, built from `tail` and the moment tails
`moment₁`, `moment₂` (`abs_deriv2_log_series_le`). With `q = exp(-2π²σ²)` and any `r` with
`4q ≤ r < 1`, the three tails are at most `2r/(1-r)`, `2π · 2r/(1-r)` and `4π² · 2r/(1-r)`
(`tail_le`). For `σ ≥ 1.277`, which covers the leaf standard deviations of both Falcon parameter
sets, `tail σ < 1` and `curvature σ ≤ 2^(-30)` (`tail_lt_one_and_curvature_le`).
-/

public section

open Real Complex

namespace LatticeCrypto.Theta


private theorem weight_eq_cexp (σ u : ℝ) (hσ : 0 < σ) (n : ℤ) :
    (discreteGaussianWeight σ u n : ℂ) =
      cexp (-(u ^ 2 / (2 * σ ^ 2) : ℝ)) *
        cexp (-π * ((2 * π * σ ^ 2)⁻¹ : ℝ) * n ^ 2 + 2 * π * ((u / (2 * π * σ ^ 2)) : ℝ) * n) := by
  rw [discreteGaussianWeight, Complex.ofReal_exp, ← Complex.exp_add]
  congr 1
  have : (σ : ℂ) ≠ 0 := by exact_mod_cast hσ.ne'
  have hp : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  push_cast
  field_simp
  ring

private theorem fourier_term_eq (σ u : ℝ) (hσ : 0 < σ) (n : ℤ) :
    cexp (-π / ((2 * π * σ ^ 2)⁻¹ : ℝ) * (n + I * ((u / (2 * π * σ ^ 2)) : ℝ)) ^ 2) =
      cexp ((u ^ 2 / (2 * σ ^ 2) : ℝ)) *
        (Real.exp (-(2 * π ^ 2 * σ ^ 2) * n ^ 2) * cexp (-(2 * π * n * u : ℝ) * I)) := by
  rw [Complex.ofReal_exp, ← Complex.exp_add, ← Complex.exp_add]
  congr 1
  have : (σ : ℂ) ≠ 0 := by exact_mod_cast hσ.ne'
  have hp : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  push_cast
  field_simp
  ring_nf
  simp only [Complex.I_sq]
  ring

private theorem summable_exp_sq (σ : ℝ) (hσ : 0 < σ) :
    Summable fun n : ℤ => Real.exp (-(2 * π ^ 2 * σ ^ 2) * n ^ 2) := by
  have h := discreteGaussianSum_summable (1 / (2 * π * σ)) 0 (by positivity)
  refine h.congr fun n => ?_
  rw [discreteGaussianWeight]
  congr 1
  have : σ ≠ 0 := hσ.ne'
  have hp : π ≠ 0 := Real.pi_ne_zero
  field_simp
  ring

/-- **Poisson summation** for the discrete Gaussian normalizer. -/
theorem discreteGaussianSum_eq_fourier (σ u : ℝ) (hσ : 0 < σ) :
    discreteGaussianSum σ u =
      σ * √(2 * π) * ∑' n : ℤ, Real.exp (-(2 * π ^ 2 * σ ^ 2) * n ^ 2) *
          Real.cos (2 * π * n * u) := by
  have ha : 0 < (((2 * π * σ ^ 2)⁻¹ : ℝ) : ℂ).re := by
    rw [Complex.ofReal_re]; positivity
  have hP := Complex.tsum_exp_neg_quadratic ha (((u / (2 * π * σ ^ 2)) : ℝ) : ℂ)
  have hH : Summable fun n : ℤ =>
      (Real.exp (-(2 * π ^ 2 * σ ^ 2) * n ^ 2) : ℂ) * cexp (-(2 * π * n * u : ℝ) * I) := by
    refine Summable.of_norm ?_
    refine (summable_exp_sq σ hσ).congr fun n => ?_
    rw [norm_mul, ← Complex.ofReal_neg, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
        Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _)]
  have hc : (discreteGaussianSum σ u : ℂ) =
      1 / (((2 * π * σ ^ 2)⁻¹ : ℝ) : ℂ) ^ (1 / 2 : ℂ) * ∑' n : ℤ,
        (Real.exp (-(2 * π ^ 2 * σ ^ 2) * n ^ 2) : ℂ) * cexp (-(2 * π * n * u : ℝ) * I) := by
    rw [discreteGaussianSum, Complex.ofReal_tsum, tsum_congr (weight_eq_cexp σ u hσ),
        tsum_mul_left, hP,
      tsum_congr (fourier_term_eq σ u hσ), tsum_mul_left, ← mul_assoc, mul_comm (cexp _), mul_assoc,
      ← mul_assoc (cexp _), ← Complex.exp_add]
    simp
  have hroot : 1 / (((2 * π * σ ^ 2)⁻¹ : ℝ) : ℂ) ^ (1 / 2 : ℂ) = ((σ * √(2 * π) : ℝ) : ℂ) := by
    have hr : (0 : ℝ) ≤ (2 * π * σ ^ 2)⁻¹ := by positivity
    rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by push_cast; ring, ← Complex.ofReal_cpow hr,
      ← Real.sqrt_eq_rpow, ← Complex.ofReal_one, ← Complex.ofReal_div]
    congr 1
    rw [Real.sqrt_inv, one_div, inv_inv, Real.sqrt_mul (by positivity), Real.sqrt_sq hσ.le,
        mul_comm]
  have hre := congrArg Complex.re hc
  rw [Complex.ofReal_re, hroot, Complex.re_ofReal_mul, Complex.re_tsum hH] at hre
  rw [hre]
  congr 1
  refine tsum_congr fun n => ?_
  rw [Complex.re_ofReal_mul, ← Complex.ofReal_neg, Complex.exp_ofReal_mul_I_re, Real.cos_neg]

/-- The theta tail `∑_{n ≠ 0} exp(-2π²σ²n²)`. -/
@[expose] noncomputable def tail (σ : ℝ) : ℝ :=
  (∑' n : ℤ, Real.exp (-(2 * π ^ 2 * σ ^ 2) * n ^ 2)) - 1

private theorem fourier_sum_mem (σ u : ℝ) (hσ : 0 < σ) :
    1 - tail σ ≤ ∑' n : ℤ, Real.exp (-(2 * π ^ 2 * σ ^ 2) * n ^ 2) * Real.cos (2 * π * n * u) ∧
      ∑' n : ℤ, Real.exp (-(2 * π ^ 2 * σ ^ 2) * n ^ 2) * Real.cos (2 * π * n * u) ≤ 1 + tail σ :=
          by
  have hs := summable_exp_sq σ hσ
  have hsc : Summable fun n : ℤ => Real.exp (-(2 * π ^ 2 * σ ^ 2) * n ^ 2) *
      Real.cos (2 * π * n * u) :=
    hs.of_norm_bounded fun n => by
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
      exact mul_le_of_le_one_right (Real.exp_pos _).le (Real.abs_cos_le_one _)
  constructor
  · have hle : ∀ n : ℤ, -Real.exp (-(2 * π ^ 2 * σ ^ 2) * n ^ 2) + (if n = 0 then 2 else 0) ≤
        Real.exp (-(2 * π ^ 2 * σ ^ 2) * n ^ 2) * Real.cos (2 * π * n * u) := fun n => by
      split_ifs with h
      · subst h; simp; norm_num
      · have := Real.neg_one_le_cos (2 * π * n * u)
        nlinarith [Real.exp_pos (-(2 * π ^ 2 * σ ^ 2) * n ^ 2)]
    have := Summable.tsum_le_tsum hle (hs.neg.add (summable_of_ne_finset_zero (s := {0})
      fun n hn => by simp at hn; simp [hn])) hsc
    rw [hs.neg.tsum_add
        (summable_of_ne_finset_zero (s := {0}) fun n hn => by simp at hn; simp [hn]),
      tsum_neg, tsum_ite_eq] at this
    unfold tail; linarith
  · have := Summable.tsum_le_tsum (fun n : ℤ => mul_le_of_le_one_right (Real.exp_pos _).le
      (Real.cos_le_one (2 * π * n * u))) hsc hs
    unfold tail; linarith

/-! ## Derivatives of the Fourier series -/

/-- The Fourier weights `exp(-2π²σ²n²)`. -/
@[expose] noncomputable def weight (σ : ℝ) (n : ℤ) : ℝ := Real.exp (-(2 * π ^ 2 * σ ^ 2) * n ^ 2)

/-- `series σ u = ∑ₙ weight n cos(2πnu)`, so that `ρσ(Z - u) = σ√(2π) series σ u`. -/
@[expose] noncomputable def series (σ u : ℝ) : ℝ := ∑' n : ℤ, weight σ n * Real.cos (2 * π * n * u)
/-- The derivative of `series σ`. -/
@[expose] noncomputable def series₁ (σ u : ℝ) : ℝ :=
    ∑' n : ℤ, -(weight σ n * (2 * π * n)) * Real.sin (2 * π * n * u)
/-- The second derivative of `series σ`. -/
@[expose] noncomputable def series₂ (σ u : ℝ) : ℝ :=
    ∑' n : ℤ, -(weight σ n * (2 * π * n) ^ 2) * Real.cos (2 * π * n * u)

/-- The first moment tail. -/
@[expose] noncomputable def moment₁ (σ : ℝ) : ℝ := ∑' n : ℤ, weight σ n * |2 * π * n|
/-- The second moment tail. -/
@[expose] noncomputable def moment₂ (σ : ℝ) : ℝ := ∑' n : ℤ, weight σ n * (2 * π * n) ^ 2

theorem weight_pos (σ : ℝ) (n : ℤ) : 0 < weight σ n := Real.exp_pos _

private theorem sq_mul_weight_le (σ : ℝ) (hσ : 0 < σ) (n : ℤ) :
    (n : ℝ) ^ 2 * weight σ n ≤ 1 / (π ^ 2 * σ ^ 2) * weight (σ / √2) n := by
  have hc : 0 < π ^ 2 * σ ^ 2 := by positivity
  set y := π ^ 2 * σ ^ 2 * (n : ℝ) ^ 2 with hy
  have hy0 : 0 ≤ y := by positivity
  have hw : weight σ n = Real.exp (-y) * Real.exp (-y) := by
    rw [weight, ← Real.exp_add]; congr 1; rw [hy]; ring
  have hw2 : weight (σ / √2) n = Real.exp (-y) := by
    rw [weight]; congr 1; rw [hy, div_pow, Real.sq_sqrt zero_le_two]; field_simp
  rw [hw, hw2]
  have hle : y * Real.exp (-y) ≤ 1 := by
    have := Real.add_one_le_exp y
    rw [Real.exp_neg]
    rw [mul_inv_le_iff₀ (Real.exp_pos y)]; linarith
  have : (n : ℝ) ^ 2 = y / (π ^ 2 * σ ^ 2) := by rw [hy]; field_simp
  rw [this]
  calc y / (π ^ 2 * σ ^ 2) * (Real.exp (-y) * Real.exp (-y))
      = (y * Real.exp (-y)) / (π ^ 2 * σ ^ 2) * Real.exp (-y) := by ring
    _ ≤ 1 / (π ^ 2 * σ ^ 2) * Real.exp (-y) := by gcongr

theorem summable_weight (σ : ℝ) (hσ : 0 < σ) : Summable (weight σ) := summable_exp_sq σ hσ

theorem summable_moment₂ (σ : ℝ) (hσ : 0 < σ) :
    Summable fun n : ℤ => weight σ n * (2 * π * n) ^ 2 := by
  have hs := (summable_weight (σ / √2) (by positivity)).mul_left (4 * π ^ 2 * (1 / (π ^ 2 * σ ^ 2)))
  refine Summable.of_nonneg_of_le (fun n => by have := weight_pos σ n; positivity) (fun n => ?_) hs
  have := sq_mul_weight_le σ hσ n
  calc weight σ n * (2 * π * n) ^ 2 = 4 * π ^ 2 * ((n : ℝ) ^ 2 * weight σ n) := by ring
    _ ≤ 4 * π ^ 2 * (1 / (π ^ 2 * σ ^ 2) * weight (σ / √2) n) := by gcongr
    _ = _ := by ring

theorem summable_moment₁ (σ : ℝ) (hσ : 0 < σ) : Summable fun n : ℤ => weight σ n * |2 * π * n| := by
  refine Summable.of_nonneg_of_le (fun n => by have := weight_pos σ n; positivity) (fun n => ?_)
    ((summable_weight σ hσ).add (summable_moment₂ σ hσ))
  have h := weight_pos σ n
  have : |2 * π * (n : ℝ)| ≤ 1 + (2 * π * n) ^ 2 := by
    nlinarith [abs_nonneg (2 * π * (n : ℝ)), sq_abs (2 * π * (n : ℝ))]
  calc weight σ n * |2 * π * n| ≤ weight σ n * (1 + (2 * π * n) ^ 2) := by gcongr
    _ = _ := by ring

theorem hasDerivAt_series (σ : ℝ) (hσ : 0 < σ) (u : ℝ) : HasDerivAt (series σ) (series₁ σ u) u := by
  refine hasDerivAt_tsum (g := fun (n : ℤ) (y : ℝ) => weight σ n * Real.cos (2 * π * n * y))
    (g' := fun (n : ℤ) (y : ℝ) => -(weight σ n * (2 * π * n)) * Real.sin (2 * π * n * y))
    (summable_moment₁ σ hσ) (fun n y => ?_) (fun n y => ?_) (y₀ := 0) ?_ u
  · have :=
      ((Real.hasDerivAt_cos (2 * π * n * y)).comp y
          ((hasDerivAt_id y).const_mul (2 * π * n))).const_mul
      (weight σ n)
    convert this using 1 <;> simp; ring
  · rw [Real.norm_eq_abs, abs_mul, abs_neg, abs_mul, abs_of_pos (weight_pos σ n)]
    exact mul_le_of_le_one_right (mul_nonneg (weight_pos σ n).le (abs_nonneg _))
      (Real.abs_sin_le_one _)
  · simpa using summable_weight σ hσ

theorem hasDerivAt_series₁ (σ : ℝ) (hσ : 0 < σ) (u : ℝ) :
    HasDerivAt (series₁ σ) (series₂ σ u) u := by
  refine hasDerivAt_tsum
      (g := fun (n : ℤ) (y : ℝ) => -(weight σ n * (2 * π * n)) * Real.sin (2 * π * n * y))
    (g' := fun (n : ℤ) (y : ℝ) => -(weight σ n * (2 * π * n) ^ 2) * Real.cos (2 * π * n * y))
    (summable_moment₂ σ hσ) (fun n y => ?_) (fun n y => ?_) (y₀ := 0) ?_ u
  · have :=
      ((Real.hasDerivAt_sin (2 * π * n * y)).comp y
          ((hasDerivAt_id y).const_mul (2 * π * n))).const_mul
      (-(weight σ n * (2 * π * n)))
    convert this using 1 <;> simp; ring
  · rw [Real.norm_eq_abs, abs_mul, abs_neg, abs_mul, abs_of_pos (weight_pos σ n),
      abs_of_nonneg (sq_nonneg _)]
    exact mul_le_of_le_one_right (by have := weight_pos σ n; positivity) (Real.abs_cos_le_one _)
  · simp

theorem abs_series₁_le (σ : ℝ) (hσ : 0 < σ) (u : ℝ) : |series₁ σ u| ≤ moment₁ σ := by
  have hb : ∀ n : ℤ,
      ‖-(weight σ n * (2 * π * n)) * Real.sin (2 * π * n * u)‖ ≤ weight σ n * |2 * π * n| :=
      fun n => by
    rw [Real.norm_eq_abs, abs_mul, abs_neg, abs_mul, abs_of_pos (weight_pos σ n)]
    exact mul_le_of_le_one_right (mul_nonneg (weight_pos σ n).le (abs_nonneg _))
      (Real.abs_sin_le_one _)
  have hs := Summable.of_nonneg_of_le (fun n => norm_nonneg _) hb (summable_moment₁ σ hσ)
  exact (norm_tsum_le_tsum_norm hs).trans (Summable.tsum_le_tsum hb hs (summable_moment₁ σ hσ))

theorem abs_series₂_le (σ : ℝ) (hσ : 0 < σ) (u : ℝ) : |series₂ σ u| ≤ moment₂ σ := by
  have hb : ∀ n : ℤ, ‖-(weight σ n * (2 * π * n) ^ 2) * Real.cos (2 * π * n * u)‖ ≤ weight σ n *
      (2 * π * n) ^ 2 :=
    fun n => by
      rw [Real.norm_eq_abs, abs_mul, abs_neg, abs_mul, abs_of_pos (weight_pos σ n),
          abs_of_nonneg (sq_nonneg _)]
      exact mul_le_of_le_one_right (by have := weight_pos σ n; positivity) (Real.abs_cos_le_one _)
  have hs := Summable.of_nonneg_of_le (fun n => norm_nonneg _) hb (summable_moment₂ σ hσ)
  exact (norm_tsum_le_tsum_norm hs).trans (Summable.tsum_le_tsum hb hs (summable_moment₂ σ hσ))

theorem series_mem (σ u : ℝ) (hσ : 0 < σ) : 1 - tail σ ≤ series σ u ∧ series σ u ≤ 1 + tail σ :=
  fourier_sum_mem σ u hσ

/-- The second-derivative bound for `log series`. -/
@[expose] noncomputable def curvature (σ : ℝ) : ℝ :=
  (moment₂ σ * (1 + tail σ) + moment₁ σ ^ 2) / (1 - tail σ) ^ 2

/-- **Second derivative of `log series`.** `log series` has derivative `series₁ / series` and
second derivative `(series₂ series - series₁²) / series²`, bounded by `curvature σ`. -/
theorem hasDerivAt_log_series (σ : ℝ) (hσ : 0 < σ) (hT : tail σ < 1) (u : ℝ) :
    HasDerivAt (fun v => Real.log (series σ v)) (series₁ σ u / series σ u) u :=
  (hasDerivAt_series σ hσ u).log (by linarith [(series_mem σ u hσ).1])

theorem hasDerivAt_series₁_div_series (σ : ℝ) (hσ : 0 < σ) (hT : tail σ < 1) (u : ℝ) :
    HasDerivAt (fun v => series₁ σ v / series σ v)
      ((series₂ σ u * series σ u - series₁ σ u * series₁ σ u) / series σ u ^ 2) u :=
  (hasDerivAt_series₁ σ hσ u).div (hasDerivAt_series σ hσ u) (by linarith [(series_mem σ u hσ).1])

theorem abs_deriv2_log_series_le (σ : ℝ) (hσ : 0 < σ) (hT : tail σ < 1) (u : ℝ) :
    |(series₂ σ u * series σ u - series₁ σ u * series₁ σ u) / series σ u ^ 2| ≤ curvature σ := by
  obtain ⟨hlo, hhi⟩ := series_mem σ u hσ
  have hf0 : 0 < series σ u := by linarith
  have h1 := abs_series₁_le σ hσ u
  have h2 := abs_series₂_le σ hσ u
  have hT0 : 0 ≤ tail σ := by
    have h := (summable_weight σ hσ).le_tsum 0 fun n _ => (weight_pos σ n).le
    simp only [weight, Int.cast_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
      mul_zero, Real.exp_zero] at h
    unfold tail; linarith
  have hT1 : 0 ≤ moment₁ σ := le_trans (abs_nonneg _) h1
  have hT2 : 0 ≤ moment₂ σ := le_trans (abs_nonneg _) h2
  rw [abs_div, abs_of_pos (by positivity : 0 < series σ u ^ 2), curvature]
  have hnum : |series₂ σ u * series σ u - series₁ σ u * series₁ σ u| ≤
      moment₂ σ * (1 + tail σ) + moment₁ σ ^ 2 := by
    calc |series₂ σ u * series σ u - series₁ σ u * series₁ σ u| ≤
        |series₂ σ u| * |series σ u| + |series₁ σ u| * |series₁ σ u| := by
          rw [← abs_mul, ← abs_mul]; exact abs_sub _ _
      _ ≤ moment₂ σ * (1 + tail σ) + moment₁ σ * moment₁ σ :=
          add_le_add (mul_le_mul h2 (by rw [abs_of_pos hf0]; exact hhi) (abs_nonneg _) hT2)
            (mul_le_mul h1 h1 (abs_nonneg _) hT1)
      _ = _ := by ring
  have hden : (1 - tail σ) ^ 2 ≤ series σ u ^ 2 := by
    have : 0 ≤ 1 - tail σ := by linarith
    gcongr
  exact div_le_div₀ (by nlinarith [sq_nonneg (moment₁ σ)]) hnum (by nlinarith) hden

/-! ## Explicit bounds on the tails -/

private theorem tsum_rpow_natAbs (r : ℝ) (h0 : 0 ≤ r) (h1 : r < 1) :
    HasSum (fun n : ℤ => r ^ n.natAbs) ((1 + r) / (1 - r)) := by
  have ha : HasSum (fun n : ℕ => r ^ n) (1 - r)⁻¹ := hasSum_geometric_of_lt_one h0 h1
  have hb : HasSum (fun n : ℕ => r ^ (n + 1)) (r * (1 - r)⁻¹) := by
    simpa [pow_succ, mul_comm] using ha.mul_left r
  have e : ∀ n : ℕ, (-((n : ℤ) + 1)).natAbs = n + 1 := fun n => by omega
  have hb' : HasSum (fun n : ℕ => r ^ (-((n : ℤ) + 1)).natAbs) (r * (1 - r)⁻¹) := by
    simp only [e]; exact hb
  have := HasSum.of_nat_of_neg_add_one (f := fun n : ℤ => r ^ n.natAbs) (by simpa using ha) hb'
  convert this using 1
  have : 1 - r ≠ 0 := sub_ne_zero.2 h1.ne'
  field_simp

/-- Each weighted term is at most `r^|n|` once `4 exp(-2π²σ²) ≤ r`. -/
private theorem term_le (σ r : ℝ) (hr : 4 * Real.exp (-(2 * π ^ 2 * σ ^ 2)) ≤ r) (n : ℤ) (j : ℕ)
    (hj : j ≤ 2) :
    (n.natAbs : ℝ) ^ j * weight σ n ≤ r ^ n.natAbs := by
  set k := n.natAbs
  have hq0 : 0 ≤ Real.exp (-(2 * π ^ 2 * σ ^ 2)) := (Real.exp_pos _).le
  have hw : weight σ n ≤ Real.exp (-(2 * π ^ 2 * σ ^ 2)) ^ k := by
    rw [weight, ← Real.exp_nat_mul]
    apply Real.exp_le_exp.2
    have hk : (k : ℝ) ≤ (n : ℝ) ^ 2 := by
      have : (k : ℝ) = |(n : ℝ)| := by rw [Nat.cast_natAbs, Int.cast_abs]
      rw [this, ← sq_abs]
      rcases eq_or_ne n 0 with h | h
      · simp [h]
      · have : (1 : ℝ) ≤ |(n : ℝ)| := by
          rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs h
        nlinarith
    have hc : 0 ≤ 2 * π ^ 2 * σ ^ 2 := by positivity
    nlinarith
  have hkj : (k : ℝ) ^ j ≤ 4 ^ k := by
    have h1 : (k : ℝ) ^ j ≤ (k : ℝ) ^ 2 ∨ k = 0 := by
      rcases Nat.eq_zero_or_pos k with h | h
      · right; exact h
      · left; exact pow_le_pow_right₀ (by exact_mod_cast h) hj
    have h2 : (k : ℝ) ^ 2 ≤ 4 ^ k := by
      have : k ^ 2 ≤ 4 ^ k := by
        calc k ^ 2 ≤ (2 ^ k) ^ 2 := Nat.pow_le_pow_left (Nat.lt_two_pow_self).le 2
          _ = 4 ^ k := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
      exact_mod_cast this
    rcases h1 with h | h
    · exact h.trans h2
    · rcases Nat.eq_zero_or_pos j with hj0 | hj0
      · subst hj0; simp [h]
      · simp [h, zero_pow hj0.ne']
  calc (k : ℝ) ^ j * weight σ n ≤ 4 ^ k * Real.exp (-(2 * π ^ 2 * σ ^ 2)) ^ k :=
        mul_le_mul hkj hw (Real.exp_pos _).le (by positivity)
    _ = (4 * Real.exp (-(2 * π ^ 2 * σ ^ 2))) ^ k := by rw [mul_pow]
    _ ≤ r ^ k := pow_le_pow_left₀ (by positivity) hr k

private theorem hasSum_b (r : ℝ) (h0 : 0 ≤ r) (h1 : r < 1) :
    HasSum (fun n : ℤ => r ^ n.natAbs - if n = 0 then 1 else 0) (2 * r / (1 - r)) := by
  have := (tsum_rpow_natAbs r h0 h1).sub (hasSum_ite_eq (0 : ℤ) (1 : ℝ))
  convert this using 1
  have : 1 - r ≠ 0 := sub_ne_zero.2 h1.ne'
  field_simp; ring

/-- `|n|ʲ weight σ n ≤ r^|n| - [n = 0]` for `j = 1, 2`. -/
private theorem term_le_b (σ r : ℝ) (hr : 4 * Real.exp (-(2 * π ^ 2 * σ ^ 2)) ≤ r) (n : ℤ) (j : ℕ)
    (hj1 : 1 ≤ j)
    (hj : j ≤ 2) : (n.natAbs : ℝ) ^ j * weight σ n ≤ r ^ n.natAbs - if n = 0 then 1 else 0 := by
  split_ifs with h
  · subst h; simp [zero_pow (by omega : j ≠ 0)]
  · simpa using term_le σ r hr n j hj

/-- **Explicit tails.** -/
theorem tail_le (σ r : ℝ) (hσ : 0 < σ) (hr : 4 * Real.exp (-(2 * π ^ 2 * σ ^ 2)) ≤ r)
    (h1 : r < 1) :
    tail σ ≤ 2 * r / (1 - r) ∧ moment₁ σ ≤ 2 * π * (2 * r / (1 - r)) ∧
      moment₂ σ ≤ 4 * π ^ 2 * (2 * r / (1 - r)) := by
  have h0 : 0 ≤ r := le_trans (by positivity) hr
  have hB := hasSum_b r h0 h1
  have hG := tsum_rpow_natAbs r h0 h1
  refine ⟨?_, ?_, ?_⟩
  · have := Summable.tsum_le_tsum (fun n => by simpa using term_le σ r hr n 0 (by norm_num))
      (summable_weight σ hσ) hG.summable
    rw [hG.tsum_eq] at this
    unfold tail
    have : 1 - r ≠ 0 := sub_ne_zero.2 h1.ne'
    calc (∑' n : ℤ, Real.exp (-(2 * π ^ 2 * σ ^ 2) * n ^ 2)) - 1 ≤ (1 + r) / (1 - r) - 1 := by
          unfold weight at *; linarith
      _ = 2 * r / (1 - r) := by field_simp; ring
  · have hle : ∀ n : ℤ, weight σ n * |2 * π * n| = 2 * π * ((n.natAbs : ℝ) ^ 1 * weight σ n) :=
        fun n => by
      rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * π), pow_one, Nat.cast_natAbs,
          Int.cast_abs]; ring
    unfold moment₁
    rw [tsum_congr hle, tsum_mul_left]
    gcongr
    rw [← hB.tsum_eq]
    have hp : (2 * π) ≠ 0 := by positivity
    exact Summable.tsum_le_tsum (fun n => term_le_b σ r hr n 1 le_rfl (by norm_num))
      (((summable_moment₁ σ hσ).mul_left (2 * π)⁻¹).congr fun n => by rw [hle]; field_simp)
      hB.summable
  · have hle : ∀ n : ℤ,
        weight σ n * (2 * π * n) ^ 2 = 4 * π ^ 2 * ((n.natAbs : ℝ) ^ 2 * weight σ n) :=
      fun n => by
      rw [Nat.cast_natAbs, Int.cast_abs, sq_abs]; ring
    unfold moment₂
    rw [tsum_congr hle, tsum_mul_left]
    gcongr
    rw [← hB.tsum_eq]
    have hp : (4 * π ^ 2) ≠ 0 := by positivity
    exact Summable.tsum_le_tsum (fun n => term_le_b σ r hr n 2 (by norm_num) le_rfl)
      (((summable_moment₂ σ hσ).mul_left (4 * π ^ 2)⁻¹).congr fun n => by rw [hle]; field_simp)
          hB.summable

/-- `4 exp(-2π²σ²) ≤ 2⁻⁴⁰` for `σ ≥ 1.277`. -/
theorem four_mul_exp_le (σ : ℝ)
    (hσ : 1277 / 1000 ≤ σ) : 4 * Real.exp (-(2 * π ^ 2 * σ ^ 2)) ≤ 1 / 2 ^ 40 := by
  have hpi := Real.pi_gt_d2
  have hp2 : (3.14 : ℝ) ^ 2 ≤ π ^ 2 := pow_le_pow_left₀ (by norm_num) hpi.le 2
  have hs2 : (1277 / 1000 : ℝ) ^ 2 ≤ σ ^ 2 := pow_le_pow_left₀ (by norm_num) hσ 2
  have hps := mul_le_mul hp2 hs2 (by norm_num) (sq_nonneg π)
  have hc : (32 : ℝ) ≤ 2 * π ^ 2 * σ ^ 2 := by nlinarith
  have he : (2 : ℝ) ^ 42 ≤ Real.exp 32 := by
    have h1 : (2.7 : ℝ) ≤ Real.exp 1 := le_trans (by norm_num) (Real.exp_one_gt_d9).le
    calc (2 : ℝ) ^ 42 ≤ 2.7 ^ 32 := by norm_num
      _ ≤ Real.exp 1 ^ 32 := pow_le_pow_left₀ (by norm_num) h1 32
      _ = Real.exp 32 := by rw [← Real.exp_nat_mul]; norm_num
  have : Real.exp (-(2 * π ^ 2 * σ ^ 2)) ≤ Real.exp (-32) := Real.exp_le_exp.2 (by linarith)
  calc 4 * Real.exp (-(2 * π ^ 2 * σ ^ 2)) ≤ 4 * Real.exp (-32) := by gcongr
    _ = 4 * (Real.exp 32)⁻¹ := by rw [Real.exp_neg]
    _ ≤ 4 * ((2 : ℝ) ^ 42)⁻¹ := by gcongr
    _ = 1 / 2 ^ 40 := by norm_num

/-- **The Falcon leaf range.** For every standard deviation `σ ≥ 1.277`, which covers the leaves
of both Falcon parameter sets, the theta tail is below `1` and the curvature bound is at most
`2^(-30)`. -/
theorem tail_lt_one_and_curvature_le (σ : ℝ) (hσ : 1277 / 1000 ≤ σ) :
    tail σ < 1 ∧ curvature σ ≤ 1 / 2 ^ 30 := by
  have hσ0 : 0 < σ := by linarith
  set r : ℝ := 1 / 2 ^ 40 with hr
  have hr1 : r < 1 := by norm_num [hr]
  obtain ⟨hT, hT1, hT2⟩ := tail_le σ r hσ0 (four_mul_exp_le σ hσ) hr1
  have hpi := Real.pi_lt_d2
  have hpi0 := Real.pi_pos
  have hε : 2 * r / (1 - r) ≤ 1 / 2 ^ 38 := by
    rw [div_le_iff₀ (by norm_num [hr])]; norm_num [hr]
  have hT0 : 0 ≤ tail σ := by
    have h := (summable_weight σ hσ0).le_tsum 0 fun n _ => (weight_pos σ n).le
    simp only [weight, Int.cast_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
      mul_zero, Real.exp_zero] at h
    unfold tail; linarith
  have hT1' : 0 ≤ moment₁ σ := le_trans (abs_nonneg _) (abs_series₁_le σ hσ0 0)
  have hT2' : 0 ≤ moment₂ σ := le_trans (abs_nonneg _) (abs_series₂_le σ hσ0 0)
  set ε : ℝ := 1 / 2 ^ 38
  have hTε : tail σ ≤ ε := hT.trans hε
  have hT1ε : moment₁ σ ≤ 7 * ε := hT1.trans (by nlinarith)
  have hT2ε : moment₂ σ ≤ 40 * ε := hT2.trans (by nlinarith)
  have hεs : ε ≤ 1 / 2 ^ 38 := le_rfl
  refine ⟨by norm_num [ε] at hTε; linarith, ?_⟩
  rw [curvature, div_le_iff₀ (by nlinarith [show tail σ < 1 by norm_num [ε] at hTε; linarith])]
  have hden : 1 / 2 ≤ (1 - tail σ) ^ 2 := by nlinarith [show tail σ ≤ 1 / 2 ^ 38 from hTε]
  have hnum : moment₂ σ * (1 + tail σ) + moment₁ σ ^ 2 ≤ 81 * ε := by
    have h1 : moment₂ σ * (1 + tail σ) ≤ 40 * ε * 2 := by
      apply mul_le_mul hT2ε (by norm_num [ε] at hTε; linarith) (by linarith) (by norm_num [ε])
    have h2 : moment₁ σ ^ 2 ≤ (7 * ε) ^ 2 := pow_le_pow_left₀ hT1' hT1ε 2
    have : (7 * ε) ^ 2 ≤ ε := by norm_num [ε]
    linarith
  calc moment₂ σ * (1 + tail σ) + moment₁ σ ^ 2 ≤ 81 * ε := hnum
    _ ≤ 1 / 2 ^ 30 * (1 / 2) := by norm_num [ε]
    _ ≤ 1 / 2 ^ 30 * (1 - tail σ) ^ 2 := by gcongr


end LatticeCrypto.Theta
