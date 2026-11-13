/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import Mathlib.NumberTheory.ModularForms.JacobiTheta.OneVariable
public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.MeasureTheory.Measure.Count
public import Mathlib.Topology.Algebra.InfiniteSum.Real

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
- `discreteGaussianMeasure σ μ` — the same distribution as a probability measure on `ℤ`,
  for use with `Measure.etvDist`, `InformationTheory.renyiDiv`, etc.

## References

- Falcon specification v1.2, Section 3.9.3 (SamplerZ)
- Gentry, Peikert, Vaikuntanathan. STOC 2008.
- Micciancio, Regev. "Lattice-based Cryptography." 2009.
-/

@[expose] public section


open Real MeasureTheory

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

/-! ## The discrete Gaussian as a measure on `ℤ` -/

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

/-- The discrete Gaussian distribution as a measure on `ℤ`: the density `discreteGaussianPMF`
against the counting measure. -/
noncomputable def discreteGaussianMeasure (σ μ : ℝ) : Measure ℤ :=
  Measure.count.withDensity fun z => ENNReal.ofReal (discreteGaussianPMF σ μ z)

@[simp]
theorem discreteGaussianMeasure_singleton (σ μ : ℝ) (z : ℤ) :
    discreteGaussianMeasure σ μ {z} = ENNReal.ofReal (discreteGaussianPMF σ μ z) := by
  rw [discreteGaussianMeasure, withDensity_apply _ (measurableSet_singleton z),
    Measure.restrict_singleton, Measure.count_singleton, one_smul, lintegral_dirac]

theorem isProbabilityMeasure_discreteGaussianMeasure (σ μ : ℝ) (hσ : 0 < σ) :
    IsProbabilityMeasure (discreteGaussianMeasure σ μ) := by
  constructor
  rw [discreteGaussianMeasure, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    lintegral_count]
  exact (hasSum_ofReal_discreteGaussian σ μ hσ).tsum_eq

theorem discreteGaussianMeasure_singleton_pos (σ μ : ℝ) (hσ : 0 < σ) (z : ℤ) :
    0 < discreteGaussianMeasure σ μ {z} := by
  rw [discreteGaussianMeasure_singleton]
  exact ENNReal.ofReal_pos.mpr (discreteGaussianPMF_pos σ μ hσ z)

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

/-! ## Poisson Summation

Poisson summation (`Complex.tsum_exp_neg_quadratic`) gives the exact theta form
`∑_{z ∈ ℤ} ρ_{σ,μ}(z) = σ√(2π) · jacobiTheta₂ μ (2πσ²i)`, hence a two-sided bound
`|∑_{z ∈ ℤ} ρ_{σ,μ}(z) - σ√(2π)| ≤ σ√(2π) · 2e^{-2π²σ²} / (1 - e^{-2π²σ²})` uniform in the
center `μ`. This is the `Λ = ℤ` case of the smoothing-parameter estimate behind GPV08
Lemma 2.10 at `s = σ√(2π)`, whose `ε = ∑_{n ≠ 0} e^{-2π²σ²n²}` is at most
`2e^{-2π²σ²} / (1 - e^{-2π²σ²})`. -/

section Poisson

open Complex

/-- **Poisson summation for the discrete Gaussian**: the normalizing constant is `σ√(2π)` times
the Jacobi theta function `θ(μ, τ) = ∑_{n ∈ ℤ} exp(2πinμ + πin²τ)` at `τ = 2πσ²i`. -/
theorem discreteGaussianSum_eq_jacobiTheta₂ (σ μ : ℝ) (hσ : 0 < σ) :
    (discreteGaussianSum σ μ : ℂ) = σ * Real.sqrt (2 * π) * jacobiTheta₂ μ (2 * π * σ ^ 2 * I) := by
  have hσ' : (σ : ℂ) ≠ 0 := ofReal_ne_zero.mpr hσ.ne'
  have ha : 0 < ((2 * π * σ ^ 2 : ℝ) : ℂ).re := by rw [ofReal_re]; positivity
  have hroot : ((2 * π * σ ^ 2 : ℝ) : ℂ) ^ (1 / 2 : ℂ) = σ * Real.sqrt (2 * π) := by
    rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by push_cast; ring, ← ofReal_cpow (by positivity),
      ← Real.sqrt_eq_rpow, Real.sqrt_mul' _ (sq_nonneg σ), Real.sqrt_sq hσ.le, mul_comm]
    push_cast
    ring
  have h := Complex.tsum_exp_neg_quadratic ha (I * μ)
  have hθ : ∀ n : ℤ, jacobiTheta₂_term n μ (2 * π * σ ^ 2 * I) =
      cexp (-π * ((2 * π * σ ^ 2 : ℝ) : ℂ) * n ^ 2 + 2 * π * (I * μ) * n) := fun n => by
    rw [jacobiTheta₂_term]
    congr 1
    push_cast
    ring_nf
    rw [I_sq]
    ring
  have hw : ∀ n : ℤ, ((discreteGaussianWeight σ μ n : ℝ) : ℂ) =
      cexp (-π / ((2 * π * σ ^ 2 : ℝ) : ℂ) * (n + I * (I * μ)) ^ 2) := fun n => by
    rw [discreteGaussianWeight, ofReal_exp]
    congr 1
    push_cast
    field_simp
    ring_nf
    simp only [I_sq, I_pow_four]
    ring
  rw [hroot] at h
  rw [discreteGaussianSum, ofReal_tsum, tsum_congr hw, jacobiTheta₂, tsum_congr hθ, h, one_div,
    mul_inv_cancel_left₀ (mul_ne_zero hσ' (ofReal_ne_zero.mpr (by positivity)))]

/-- **Two-sided bound on the normalizing constant**: uniformly in the center `μ`,
`|∑_{z ∈ ℤ} ρ_{σ,μ}(z) - σ√(2π)| ≤ σ√(2π) · 2e^{-2π²σ²} / (1 - e^{-2π²σ²})`. -/
theorem abs_discreteGaussianSum_sub_le (σ μ : ℝ) (hσ : 0 < σ) :
    |discreteGaussianSum σ μ - σ * Real.sqrt (2 * π)| ≤ σ * Real.sqrt (2 * π) *
      (2 / (1 - Real.exp (-2 * π ^ 2 * σ ^ 2)) * Real.exp (-2 * π ^ 2 * σ ^ 2)) := by
  set τ : ℂ := 2 * π * σ ^ 2 * I with hτ_def
  have hτi : τ.im = 2 * π * σ ^ 2 := by simp [hτ_def, sq]
  have hτ : 0 < τ.im := by rw [hτi]; positivity
  have h0 : ∀ z : ℂ, jacobiTheta₂_term 0 z τ = 1 := by simp [jacobiTheta₂_term]
  have hf := (hasSum_jacobiTheta₂_term (μ : ℂ) hτ).update 0 0
  have hg := (hasSum_jacobiTheta₂_term (0 : ℂ) hτ).update 0 0
  rw [h0, zero_sub, neg_add_eq_sub] at hf hg
  have hre : ∀ n : ℤ, (Function.update (jacobiTheta₂_term · 0 τ) 0 0 n).re =
      ‖Function.update (jacobiTheta₂_term · (μ : ℂ) τ) 0 0 n‖ := fun n => by
    rcases eq_or_ne n 0 with rfl | hn
    · simp
    rw [Function.update_of_ne hn, Function.update_of_ne hn, norm_jacobiTheta₂_term, ofReal_im,
      jacobiTheta₂_term, exp_re, hτ_def]
    simp [sq]
  have hle := (hf.norm_le_of_bounded (Complex.hasSum_re hg) fun n => (hre n).ge).trans
    ((re_le_norm _).trans (jacobiTheta_eq_jacobiTheta₂ τ ▸ norm_jacobiTheta_sub_one_le hτ))
  rw [hτi, show -π * (2 * π * σ ^ 2) = -2 * π ^ 2 * σ ^ 2 by ring] at hle
  have hS : ((discreteGaussianSum σ μ - σ * Real.sqrt (2 * π) : ℝ) : ℂ) =
      ((σ * Real.sqrt (2 * π) : ℝ) : ℂ) * (jacobiTheta₂ μ τ - 1) := by
    rw [ofReal_sub, discreteGaussianSum_eq_jacobiTheta₂ σ μ hσ]
    push_cast
    ring
  rw [← Real.norm_eq_abs, ← Complex.norm_real, hS, norm_mul, Complex.norm_real,
    Real.norm_of_nonneg (by positivity)]
  gcongr

end Poisson

/-! ## Normalizing-Constant Lower Bound -/

/-- **Quantitative lower bound on the discrete Gaussian normalizing constant**:
`σ√(2π) - 1 ≤ ∑_{z ∈ ℤ} ρ_{σ,μ}(z)`, from `abs_discreteGaussianSum_sub_le` once `1 < σ√(2π)`
and from positivity otherwise. -/
theorem le_discreteGaussianSum (σ μ : ℝ) (hσ : 0 < σ) :
    σ * Real.sqrt (2 * π) - 1 ≤ discreteGaussianSum σ μ := by
  set t := σ * Real.sqrt (2 * π) with ht_def
  rcases le_or_gt t 1 with ht | ht
  · linarith [discreteGaussianSum_pos σ μ hσ]
  set r := Real.exp (-2 * π ^ 2 * σ ^ 2) with hr_def
  have hr : r * (2 * t + 1) ≤ 1 := by
    have h1 : 2 * t ≤ π * t ^ 2 := by nlinarith [Real.two_le_pi]
    have h2 : π * t ^ 2 = 2 * π ^ 2 * σ ^ 2 := by
      rw [ht_def, mul_pow, Real.sq_sqrt (by positivity)]
      ring
    have h3 : r * Real.exp (2 * π ^ 2 * σ ^ 2) = 1 := by
      rw [hr_def, ← Real.exp_add, neg_mul, neg_mul, neg_add_cancel, Real.exp_zero]
    calc r * (2 * t + 1) ≤ r * Real.exp (2 * π ^ 2 * σ ^ 2) := by
          gcongr
          linarith [Real.add_one_le_exp (2 * π ^ 2 * σ ^ 2)]
      _ = 1 := h3
  have hb : t * (2 / (1 - r) * r) ≤ 1 := by
    rw [show t * (2 / (1 - r) * r) = 2 * t * r / (1 - r) by ring,
      div_le_one (by nlinarith [Real.exp_pos (-2 * π ^ 2 * σ ^ 2)])]
    linarith
  linarith [(abs_le.mp (abs_discreteGaussianSum_sub_le σ μ hσ)).1]

/-! ## Guessing-Probability Bound

Combining the mode-mass bound with the normalizing-constant lower bound yields a computable
per-point guessing bound for the one-dimensional discrete Gaussian: once
`1 < σ√(2π)`, no integer carries more than `1 / (σ√(2π) - 1)` of the mass — a min-entropy of
at least `log₂ (σ√(2π) - 1)` bits.  This is the one-dimensional building block for the
per-call guessing-probability (min-entropy) assumptions of GPV-style hash-and-sign security
proofs; the lift to the `2n`-dimensional NTRU coset Gaussian via the smoothing-parameter
bound (GPV08 Lemma 2.10) remains future work. -/

/-- **Guessing bound for the discrete Gaussian**: when `1 < σ√(2π)`, every integer carries
mass at most `1 / (σ√(2π) - 1)`, since the weight is at most `1` and the normalizing
constant is at least `σ√(2π) - 1` (`le_discreteGaussianSum`). -/
theorem discreteGaussianPMF_le_one_div_sub_one (σ μ : ℝ) (hσ : 0 < σ)
    (hσ' : 1 < σ * Real.sqrt (2 * π)) (z : ℤ) :
    discreteGaussianPMF σ μ z ≤ 1 / (σ * Real.sqrt (2 * π) - 1) := by
  have hpos : 0 < σ * Real.sqrt (2 * π) - 1 := by linarith
  have h1 := discreteGaussianWeight_le_one σ μ z
  have h2 := le_discreteGaussianSum σ μ hσ
  rw [discreteGaussianPMF]
  gcongr

/-- The guessing bound for the discrete Gaussian, stated on its measure: when `1 < σ√(2π)`,
every singleton mass of `discreteGaussianMeasure` is at most `ENNReal.ofReal (1 / (σ√(2π) - 1))`.
One-dimensional building block for min-entropy assumptions on lattice-coset trapdoor samplers. -/
theorem discreteGaussianMeasure_singleton_le (σ μ : ℝ) (hσ : 0 < σ)
    (hσ' : 1 < σ * Real.sqrt (2 * π)) (z : ℤ) :
    discreteGaussianMeasure σ μ {z} ≤ ENNReal.ofReal (1 / (σ * Real.sqrt (2 * π) - 1)) := by
  rw [discreteGaussianMeasure_singleton]
  exact ENNReal.ofReal_le_ofReal (discreteGaussianPMF_le_one_div_sub_one σ μ hσ hσ' z)

end LatticeCrypto
