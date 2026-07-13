/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# Discrete Gaussian Distribution

This file defines the discrete Gaussian distribution `D_{ℤ,σ,μ}` over the integers,
parameterized by a standard deviation `σ > 0` and a center `μ ∈ ℝ`. This distribution is
fundamental to lattice-based cryptography, where it is used for trapdoor sampling (GPV
framework, Falcon) and masking (ML-DSA / Dilithium).

## Main Definitions

- `discreteGaussianWeight σ μ z` — the unnormalized Gaussian weight
  `exp(-(z - μ)² / (2σ²))` at integer `z`.
- `discreteGaussianSum σ μ` — the normalizing constant `∑_{z ∈ ℤ} ρ_{σ,μ}(z)`.
- `discreteGaussianPMF σ μ` — the probability mass function, defined as
  `ρ_{σ,μ}(z) / ∑_z ρ_{σ,μ}(z)`.
- `discreteGaussianDist σ μ hσ` — the same distribution as a Mathlib `PMF ℤ`,
  for use with `PMF.tvDist`, `PMF.renyiDiv`, etc.

## References

- Falcon specification v1.2, Section 3.9.3 (SamplerZ)
- Gentry, Peikert, Vaikuntanathan. STOC 2008.
- Micciancio, Regev. "Lattice-based Cryptography." 2009.
-/


open Real BigOperators

namespace LatticeCrypto

/-- The unnormalized Gaussian weight at integer point `z` with center `μ` and standard
deviation `σ`. -/
noncomputable def discreteGaussianWeight (σ μ : ℝ) (z : ℤ) : ℝ :=
  Real.exp (-(↑z - μ) ^ 2 / (2 * σ ^ 2))

/-- The discrete Gaussian weight is strictly positive at every integer point. -/
theorem discreteGaussianWeight_pos (σ μ : ℝ) (z : ℤ) :
    0 < discreteGaussianWeight σ μ z :=
  exp_pos _

/-- The discrete Gaussian weight is nonnegative at every integer point. -/
theorem discreteGaussianWeight_nonneg (σ μ : ℝ) (z : ℤ) :
    0 ≤ discreteGaussianWeight σ μ z :=
  le_of_lt (discreteGaussianWeight_pos σ μ z)

/-- The normalizing constant for the discrete Gaussian: `∑_{z ∈ ℤ} ρ_{σ,μ}(z)`. -/
noncomputable def discreteGaussianSum (σ μ : ℝ) : ℝ :=
  ∑' (z : ℤ), discreteGaussianWeight σ μ z

/-- The discrete Gaussian sum converges for any `σ > 0`. The Gaussian weight decays
exponentially, so the sum over `ℤ` is absolutely convergent. -/
theorem discreteGaussianSum_summable (σ μ : ℝ) (hσ : 0 < σ) :
    Summable (discreteGaussianWeight σ μ) := by
  rw [summable_int_iff_summable_nat_and_neg]
  have hσ2 : (0 : ℝ) < 2 * σ ^ 2 := by positivity
  constructor
  · -- Nonneg part: compare with exp(μ + σ²/2) * exp(-n)
    refine .of_norm_bounded (g := fun n ↦ exp (μ + σ ^ 2 / 2) * exp (-(↑n : ℝ)))
      (summable_exp_neg_nat.mul_left _) fun n ↦ ?_
    simp only [discreteGaussianWeight, Int.cast_natCast, norm_of_nonneg (exp_nonneg _), ← exp_add]
    apply exp_le_exp_of_le
    rw [neg_div]
    have h : ((↑n : ℝ) - μ - σ ^ 2) ^ 2 / (2 * σ ^ 2) =
             ((↑n : ℝ) - μ) ^ 2 / (2 * σ ^ 2) - ↑n + μ + σ ^ 2 / 2 := by
      field_simp; ring
    linarith [div_nonneg (sq_nonneg ((↑n : ℝ) - μ - σ ^ 2)) hσ2.le]
  · -- Neg part: compare with exp(-μ + σ²/2) * exp(-n)
    refine .of_norm_bounded (g := fun n ↦ exp (-μ + σ ^ 2 / 2) * exp (-(↑n : ℝ)))
      (summable_exp_neg_nat.mul_left _) fun n ↦ ?_
    simp only [discreteGaussianWeight, Int.cast_neg, Int.cast_natCast,
      norm_of_nonneg (exp_nonneg _), ← exp_add]
    apply exp_le_exp_of_le
    have hsq : (-(↑n : ℝ) - μ) ^ 2 = ((↑n : ℝ) + μ) ^ 2 := by ring
    rw [hsq, neg_div]
    have h : ((↑n : ℝ) + μ - σ ^ 2) ^ 2 / (2 * σ ^ 2) =
             ((↑n : ℝ) + μ) ^ 2 / (2 * σ ^ 2) - ↑n - μ + σ ^ 2 / 2 := by
      field_simp; ring
    linarith [div_nonneg (sq_nonneg ((↑n : ℝ) + μ - σ ^ 2)) hσ2.le]

/-- The discrete Gaussian normalizing constant is strictly positive when `σ > 0`. -/
theorem discreteGaussianSum_pos (σ μ : ℝ) (hσ : 0 < σ) :
    0 < discreteGaussianSum σ μ :=
  (discreteGaussianSum_summable σ μ hσ).tsum_pos
    (fun z => discreteGaussianWeight_nonneg σ μ z) 0
    (discreteGaussianWeight_pos σ μ 0)

/-- The discrete Gaussian probability mass function over `ℤ` with center `μ` and standard
deviation `σ`. Defined as the normalized Gaussian weight:

  `P(z) = exp(-(z - μ)² / (2σ²)) / (∑_{z' ∈ ℤ} exp(-(z' - μ)² / (2σ²)))` -/
noncomputable def discreteGaussianPMF (σ μ : ℝ) : ℤ → ℝ :=
  fun z => discreteGaussianWeight σ μ z / discreteGaussianSum σ μ

/-- The discrete Gaussian PMF is pointwise nonnegative. -/
theorem discreteGaussianPMF_nonneg (σ μ : ℝ) (hσ : 0 < σ) (z : ℤ) :
    0 ≤ discreteGaussianPMF σ μ z :=
  div_nonneg (discreteGaussianWeight_nonneg σ μ z)
    (le_of_lt (discreteGaussianSum_pos σ μ hσ))

/-- The discrete Gaussian PMF sums to `1`. -/
theorem discreteGaussianPMF_sum_eq_one (σ μ : ℝ) (hσ : 0 < σ) :
    ∑' (z : ℤ), discreteGaussianPMF σ μ z = 1 := by
  unfold discreteGaussianPMF
  rw [tsum_div_const]
  exact div_self (ne_of_gt (discreteGaussianSum_pos σ μ hσ))

/-- The discrete Gaussian PMF is strictly positive at every integer point. -/
theorem discreteGaussianPMF_pos (σ μ : ℝ) (hσ : 0 < σ) (z : ℤ) :
    0 < discreteGaussianPMF σ μ z :=
  div_pos (discreteGaussianWeight_pos σ μ z) (discreteGaussianSum_pos σ μ hσ)

/-! ## Mathlib `PMF ℤ` Construction -/

/-- The discrete Gaussian PMF is summable (as a real-valued function). -/
theorem discreteGaussianPMF_summable (σ μ : ℝ) (hσ : 0 < σ) :
    Summable (discreteGaussianPMF σ μ) := by
  have h := discreteGaussianPMF_sum_eq_one σ μ hσ
  by_contra hns
  simp [tsum_eq_zero_of_not_summable hns] at h

private theorem hasSum_ofReal_discreteGaussian (σ μ : ℝ) (hσ : 0 < σ) :
    HasSum (fun z => ENNReal.ofReal (discreteGaussianPMF σ μ z)) 1 := by
  rw [ENNReal.summable.hasSum_iff, ← ENNReal.ofReal_one,
    ← discreteGaussianPMF_sum_eq_one σ μ hσ]
  exact (ENNReal.ofReal_tsum_of_nonneg (discreteGaussianPMF_nonneg σ μ hσ)
    (discreteGaussianPMF_summable σ μ hσ)).symm

/-- The discrete Gaussian distribution as a Mathlib `PMF ℤ`. -/
noncomputable def discreteGaussianDist (σ μ : ℝ) (hσ : 0 < σ) : PMF ℤ :=
  ⟨fun z => ENNReal.ofReal (discreteGaussianPMF σ μ z),
    hasSum_ofReal_discreteGaussian σ μ hσ⟩

@[simp]
theorem discreteGaussianDist_apply (σ μ : ℝ) (hσ : 0 < σ) (z : ℤ) :
    (discreteGaussianDist σ μ hσ z).toReal = discreteGaussianPMF σ μ z :=
  ENNReal.toReal_ofReal (discreteGaussianPMF_nonneg σ μ hσ z)

theorem discreteGaussianDist_pos (σ μ : ℝ) (hσ : 0 < σ) (z : ℤ) :
    0 < discreteGaussianDist σ μ hσ z :=
  ENNReal.ofReal_pos.mpr (discreteGaussianPMF_pos σ μ hσ z)

theorem discreteGaussianDist_ne_zero (σ μ : ℝ) (hσ : 0 < σ) (z : ℤ) :
    discreteGaussianDist σ μ hσ z ≠ 0 :=
  ne_of_gt (discreteGaussianDist_pos σ μ hσ z)

/-! ## Pointwise Mass Bounds

The discrete Gaussian weight is maximized over `ℤ` at `round μ`, the integer nearest to the
center, so every pointwise mass of `discreteGaussianPMF` is at most the mode mass
`discreteGaussianWeight σ μ (round μ) / discreteGaussianSum σ μ`. -/

/-- The discrete Gaussian weight never exceeds `1`: the exponent `-(z - μ)² / (2σ²)` is
nonpositive (including the degenerate `σ = 0` case, where it is zero by convention). -/
theorem discreteGaussianWeight_le_one (σ μ : ℝ) (z : ℤ) :
    discreteGaussianWeight σ μ z ≤ 1 := by
  rw [discreteGaussianWeight, ← Real.exp_zero]
  apply exp_le_exp_of_le
  rw [neg_div, neg_nonpos]
  positivity

/-- The discrete Gaussian weight is maximized over `ℤ` at `round μ`, the nearest integer to
the center: the exponent is antitone in the squared distance `(z - μ)²`, which `round μ`
minimizes (`round_le`). -/
theorem discreteGaussianWeight_le_weight_round (σ μ : ℝ) (z : ℤ) :
    discreteGaussianWeight σ μ z ≤ discreteGaussianWeight σ μ (round μ) := by
  have hkey : |(round μ : ℝ) - μ| ≤ |(z : ℝ) - μ| := by
    rw [abs_sub_comm ((round μ : ℝ)) μ, abs_sub_comm ((z : ℝ)) μ]
    exact round_le μ z
  have hsq : ((round μ : ℝ) - μ) ^ 2 ≤ ((z : ℝ) - μ) ^ 2 := by
    have h := abs_le.mp hkey
    calc ((round μ : ℝ) - μ) ^ 2 ≤ |(z : ℝ) - μ| ^ 2 := sq_le_sq' h.1 h.2
      _ = ((z : ℝ) - μ) ^ 2 := sq_abs _
  rw [discreteGaussianWeight, discreteGaussianWeight]
  apply exp_le_exp_of_le
  rw [neg_div, neg_div, neg_le_neg_iff]
  gcongr

/-- **Mode-mass bound**: every pointwise mass of the discrete Gaussian PMF is at most the
mass of the mode `round μ`. -/
theorem discreteGaussianPMF_le_weight_round_div_sum (σ μ : ℝ) (hσ : 0 < σ) (z : ℤ) :
    discreteGaussianPMF σ μ z ≤
      discreteGaussianWeight σ μ (round μ) / discreteGaussianSum σ μ := by
  have hS := discreteGaussianSum_pos σ μ hσ
  rw [discreteGaussianPMF]
  gcongr
  exact discreteGaussianWeight_le_weight_round σ μ z

/-! ## Sum-Integral Comparison For Monotone Tails

`integral_Ioi_le_tsum_of_antitoneOn` and `integral_Iic_le_tsum_of_monotoneOn` bound the
improper integral of a one-sided monotone function by the sum of its values on a unit-spaced
grid anchored at the interval endpoint.  They provide the two tail estimates behind the
quantitative lower bound `le_discreteGaussianSum`. -/

section SumIntegralComparison

open Filter MeasureTheory Set

/-- The integral of an antitone function over `(c, ∞)` is at most the sum of its values on
the unit grid `c, c + 1, c + 2, …`: each grid value dominates the integral over the unit
interval to its right. -/
theorem integral_Ioi_le_tsum_of_antitoneOn {f : ℝ → ℝ} {c : ℝ}
    (hf : AntitoneOn f (Ici c)) (hint : IntegrableOn f (Ioi c))
    (hsum : Summable fun n : ℕ => f (c + n)) :
    ∫ x in Ioi c, f x ≤ ∑' n : ℕ, f (c + n) := by
  refine le_of_tendsto_of_tendsto'
    (intervalIntegral_tendsto_integral_Ioi c hint
      (tendsto_atTop_add_const_left atTop c tendsto_natCast_atTop_atTop))
    hsum.hasSum.tendsto_sum_nat
    fun N => AntitoneOn.integral_le_sum (hf.mono Icc_subset_Ici_self)

/-- The integral of a monotone function over `(-∞, c]` is at most the sum of its values on
the unit grid `c, c - 1, c - 2, …`: each grid value dominates the integral over the unit
interval to its left. -/
theorem integral_Iic_le_tsum_of_monotoneOn {f : ℝ → ℝ} {c : ℝ}
    (hf : MonotoneOn f (Iic c)) (hint : IntegrableOn f (Iic c))
    (hsum : Summable fun n : ℕ => f (c - n)) :
    ∫ x in Iic c, f x ≤ ∑' n : ℕ, f (c - n) := by
  have hlim : Tendsto (fun N : ℕ => c - (N : ℝ)) atTop atBot := by
    simpa [sub_eq_add_neg] using
      tendsto_atBot_add_const_left atTop c
        (tendsto_neg_atTop_atBot.comp tendsto_natCast_atTop_atTop)
  refine le_of_tendsto_of_tendsto'
    (intervalIntegral_tendsto_integral_Iic c hint hlim)
    hsum.hasSum.tendsto_sum_nat
    fun N => ?_
  have hc : c - (N : ℝ) + (N : ℝ) = c := by ring
  have key := MonotoneOn.integral_le_sum (f := f) (x₀ := c - (N : ℝ)) (a := N)
    (by rw [hc]; exact hf.mono Icc_subset_Iic_self)
  rw [hc] at key
  refine key.trans (le_of_eq ?_)
  rw [← Finset.sum_range_reflect (fun i => f (c - (N : ℝ) + (i + 1 : ℕ))) N]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hiN : i < N := Finset.mem_range.mp hi
  congr 1
  rw [show N - 1 - i + 1 = N - i by omega, Nat.cast_sub hiN.le]
  ring

end SumIntegralComparison

/-! ## Normalizing-Constant Lower Bound -/

section LowerBound

open Filter MeasureTheory Set

/-- **Quantitative lower bound on the discrete Gaussian normalizing constant**:
`σ√(2π) - 1 ≤ ∑_{z ∈ ℤ} ρ_{σ,μ}(z)`.

The sum over `ℤ` splits at `⌊μ⌋` into two monotone tails, each of which dominates the
corresponding tail of the Gaussian integral `∫ exp (-(x - μ)² / (2σ²)) dx = σ√(2π)`
(`integral_Iic_le_tsum_of_monotoneOn`, `integral_Ioi_le_tsum_of_antitoneOn`); the missing
unit interval `(⌊μ⌋, ⌊μ⌋ + 1]` carries integral mass at most `1` since the integrand is
bounded by `1`. -/
theorem le_discreteGaussianSum (σ μ : ℝ) (hσ : 0 < σ) :
    σ * Real.sqrt (2 * π) - 1 ≤ discreteGaussianSum σ μ := by
  set f : ℝ → ℝ := fun x => Real.exp (-(x - μ) ^ 2 / (2 * σ ^ 2)) with hf_def
  have hfz : ∀ z : ℤ, discreteGaussianWeight σ μ z = f z := fun z => rfl
  have hb : (0 : ℝ) < (2 * σ ^ 2)⁻¹ := by positivity
  have hfx : f = fun x => Real.exp (-(2 * σ ^ 2)⁻¹ * (x - μ) ^ 2) := by
    funext x
    simp only [hf_def]
    congr 1
    ring
  have hint : Integrable f := by
    rw [hfx]
    exact (integrable_exp_neg_mul_sq hb).comp_sub_right μ
  have hIval : ∫ x, f x = σ * Real.sqrt (2 * π) := by
    rw [hfx, integral_sub_right_eq_self (fun y : ℝ => Real.exp (-(2 * σ ^ 2)⁻¹ * y ^ 2)) μ,
      integral_gaussian,
      show π / (2 * σ ^ 2)⁻¹ = σ ^ 2 * (2 * π) by rw [div_eq_mul_inv, inv_inv]; ring,
      Real.sqrt_mul (sq_nonneg σ) (2 * π), Real.sqrt_sq hσ.le]
  have hf_le_one : ∀ x : ℝ, f x ≤ 1 := by
    intro x
    simp only [hf_def]
    rw [← Real.exp_zero]
    apply exp_le_exp_of_le
    rw [neg_div, neg_nonpos]
    positivity
  have hmono : MonotoneOn f (Iic ((⌊μ⌋ : ℤ) : ℝ)) := by
    intro x hx y hy hxy
    have hyμ : y ≤ μ := le_trans (mem_Iic.mp hy) (Int.floor_le μ)
    simp only [hf_def]
    apply exp_le_exp_of_le
    rw [neg_div, neg_div, neg_le_neg_iff]
    have hsq : (y - μ) ^ 2 ≤ (x - μ) ^ 2 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hxy) (by linarith : (0 : ℝ) ≤ 2 * μ - x - y)]
    gcongr
  have hanti : AntitoneOn f (Ici (((⌊μ⌋ : ℤ) : ℝ) + 1)) := by
    intro x hx y hy hxy
    have hμx : μ ≤ x := le_trans (Int.lt_floor_add_one μ).le (mem_Ici.mp hx)
    simp only [hf_def]
    apply exp_le_exp_of_le
    rw [neg_div, neg_div, neg_le_neg_iff]
    have hsq : (x - μ) ^ 2 ≤ (y - μ) ^ 2 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hxy) (by linarith : (0 : ℝ) ≤ x + y - 2 * μ)]
    gcongr
  have hw := discreteGaussianSum_summable σ μ hσ
  have hFsummable : Summable fun z : ℤ => discreteGaussianWeight σ μ (z + (⌊μ⌋ + 1)) :=
    hw.comp_injective (add_left_injective (⌊μ⌋ + 1))
  have hFnat : Summable fun n : ℕ => discreteGaussianWeight σ μ ((n : ℤ) + (⌊μ⌋ + 1)) :=
    hFsummable.comp_injective Nat.cast_injective
  have hFneg :
      Summable fun n : ℕ => discreteGaussianWeight σ μ (-((n : ℤ) + 1) + (⌊μ⌋ + 1)) :=
    hFsummable.comp_injective fun a b h => by omega
  have hR : ∀ n : ℕ, discreteGaussianWeight σ μ ((n : ℤ) + (⌊μ⌋ + 1))
      = f (((⌊μ⌋ : ℤ) : ℝ) + 1 + n) := fun n => by
    rw [hfz]
    congr 1
    push_cast
    ring
  have hL : ∀ n : ℕ, discreteGaussianWeight σ μ (-((n : ℤ) + 1) + (⌊μ⌋ + 1))
      = f (((⌊μ⌋ : ℤ) : ℝ) - n) := fun n => by
    rw [hfz]
    congr 1
    push_cast
    ring
  have hsplit : discreteGaussianSum σ μ
      = (∑' n : ℕ, f (((⌊μ⌋ : ℤ) : ℝ) + 1 + n)) + ∑' n : ℕ, f (((⌊μ⌋ : ℤ) : ℝ) - n) := by
    have h1 : ∑' z : ℤ, discreteGaussianWeight σ μ (z + (⌊μ⌋ + 1))
        = discreteGaussianSum σ μ :=
      (Equiv.addRight ((⌊μ⌋ : ℤ) + 1)).tsum_eq (discreteGaussianWeight σ μ)
    have h2 : ∑' z : ℤ, discreteGaussianWeight σ μ (z + (⌊μ⌋ + 1))
        = (∑' n : ℕ, discreteGaussianWeight σ μ ((n : ℤ) + (⌊μ⌋ + 1)))
          + ∑' n : ℕ, discreteGaussianWeight σ μ (-((n : ℤ) + 1) + (⌊μ⌋ + 1)) :=
      tsum_of_nat_of_neg_add_one
        (f := fun z : ℤ => discreteGaussianWeight σ μ (z + (⌊μ⌋ + 1))) hFnat hFneg
    rw [← h1, h2, tsum_congr hR, tsum_congr hL]
  have hsumR : Summable fun n : ℕ => f (((⌊μ⌋ : ℤ) : ℝ) + 1 + n) := hFnat.congr hR
  have hsumL : Summable fun n : ℕ => f (((⌊μ⌋ : ℤ) : ℝ) - n) := hFneg.congr hL
  have hRle : ∫ x in Ioi (((⌊μ⌋ : ℤ) : ℝ) + 1), f x
      ≤ ∑' n : ℕ, f (((⌊μ⌋ : ℤ) : ℝ) + 1 + n) :=
    integral_Ioi_le_tsum_of_antitoneOn hanti hint.integrableOn hsumR
  have hLle : ∫ x in Iic ((⌊μ⌋ : ℤ) : ℝ), f x ≤ ∑' n : ℕ, f (((⌊μ⌋ : ℤ) : ℝ) - n) :=
    integral_Iic_le_tsum_of_monotoneOn hmono hint.integrableOn hsumL
  have hmid : ∫ x in Ioc ((⌊μ⌋ : ℤ) : ℝ) (((⌊μ⌋ : ℤ) : ℝ) + 1), f x ≤ 1 := by
    have hle : ∫ x in Ioc ((⌊μ⌋ : ℤ) : ℝ) (((⌊μ⌋ : ℤ) : ℝ) + 1), f x
        ≤ ∫ _x in Ioc ((⌊μ⌋ : ℤ) : ℝ) (((⌊μ⌋ : ℤ) : ℝ) + 1), (1 : ℝ) :=
      setIntegral_mono_on hint.integrableOn (integrableOn_const (hs := measure_Ioc_lt_top.ne))
        measurableSet_Ioc fun x _ => hf_le_one x
    have heq : ∫ _x in Ioc ((⌊μ⌋ : ℤ) : ℝ) (((⌊μ⌋ : ℤ) : ℝ) + 1), (1 : ℝ) = 1 := by
      rw [setIntegral_const, smul_eq_mul, mul_one,
        Real.volume_real_Ioc_of_le (by linarith)]
      ring
    linarith
  have hsplit2 : ∫ x in Ioi ((⌊μ⌋ : ℤ) : ℝ), f x
      = (∫ x in Ioc ((⌊μ⌋ : ℤ) : ℝ) (((⌊μ⌋ : ℤ) : ℝ) + 1), f x)
        + ∫ x in Ioi (((⌊μ⌋ : ℤ) : ℝ) + 1), f x := by
    rw [← setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi
      hint.integrableOn hint.integrableOn, Ioc_union_Ioi_eq_Ioi (by linarith)]
  have hsplit1 : (∫ x in Iic ((⌊μ⌋ : ℤ) : ℝ), f x) + ∫ x in Ioi ((⌊μ⌋ : ℤ) : ℝ), f x
      = ∫ x, f x :=
    intervalIntegral.integral_Iic_add_Ioi hint.integrableOn hint.integrableOn
  calc σ * Real.sqrt (2 * π) - 1
      ≤ (∫ x in Iic ((⌊μ⌋ : ℤ) : ℝ), f x) + ∫ x in Ioi (((⌊μ⌋ : ℤ) : ℝ) + 1), f x := by
        rw [← hIval, ← hsplit1, hsplit2]
        linarith
    _ ≤ (∑' n : ℕ, f (((⌊μ⌋ : ℤ) : ℝ) - n)) + ∑' n : ℕ, f (((⌊μ⌋ : ℤ) : ℝ) + 1 + n) :=
        add_le_add hLle hRle
    _ = discreteGaussianSum σ μ := by rw [hsplit]; ring

end LowerBound

end LatticeCrypto
