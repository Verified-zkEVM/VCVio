/-
Copyright (c) 2026 Tom Wambsgans. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Wambsgans
-/

module

public import HashSig.SLHDSA.SHAKE128s.Proof.ForsMoments
public import Mathlib.Probability.Distributions.Poisson.Basic
public import Mathlib.Tactic.FieldSimp

/-!
# Moments of the Poisson load distribution

This file identifies the checked Touchard polynomials with integrals against
`poissonMeasure`, proves integrability, and checks the centered moments used in
the independent-load concentration argument. It does not couple Poisson loads
to a signing transcript or assert any cryptographic security bound.
-/

public section

open MeasureTheory ProbabilityTheory
open scoped NNReal Nat

namespace SlhDsaSecurity.ForsConcentration

/-- Shifting a Poisson weight by `k`: the weight of `n + k` times `(n + k)! / n!` is `rate ^ k`
times the weight of `n`. -/
lemma poisson_factorial_shift (rate : ℝ≥0) (k n : Nat) :
    (Real.exp (-rate) * (rate : ℝ) ^ (n + k) / ((n + k).factorial : ℝ)) *
        ((n + k).descFactorial k : ℝ) =
      (rate : ℝ) ^ k * (Real.exp (-rate) * (rate : ℝ) ^ n / (n.factorial : ℝ)) := by
  have hf : (n.factorial : ℝ) * ((n + k).descFactorial k : ℝ) =
      ((n + k).factorial : ℝ) := by
    exact_mod_cast (by
      simpa using (Nat.factorial_mul_descFactorial (n := n + k) (k := k) (by omega)) :
        n.factorial * (n + k).descFactorial k = (n + k).factorial)
  rw [pow_add, ← hf]
  have hn : (n.factorial : ℝ) ≠ 0 := by positivity
  have hk : ((n + k).descFactorial k : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.descFactorial_pos.mpr (by omega : k ≤ n + k)).ne'
  field_simp

/-- The `k`-th factorial moment of a Poisson variable of rate `rate` is `rate ^ k`, as a sum. -/
lemma poisson_hasSum_descFactorial (rate : ℝ≥0) (k : Nat) :
    HasSum (fun n : Nat =>
      (Real.exp (-rate) * (rate : ℝ) ^ n / (n.factorial : ℝ)) *
        (n.descFactorial k : ℝ)) ((rate : ℝ) ^ k) := by
  have hz : ∑ n ∈ Finset.range k,
      (Real.exp (-rate) * (rate : ℝ) ^ n / (n.factorial : ℝ)) *
        (n.descFactorial k : ℝ) = 0 := by
    apply Finset.sum_eq_zero
    intro n hn
    simp [Nat.descFactorial_eq_zero_iff_lt.mpr (Finset.mem_range.mp hn)]
  have hs := (hasSum_one_poissonMeasure rate).mul_left ((rate : ℝ) ^ k)
  simp only [mul_one] at hs
  apply (hasSum_nat_add_iff' k).mp
  simpa only [poisson_factorial_shift, hz, sub_zero] using hs

/-- Multiplying a falling factorial by its base raises its order by one, up to a correction:
`c * c^(d) = c^(d+1) + d * c^(d)`. -/
theorem mul_descFactorial_eq (count degree : Nat) :
    count * count.descFactorial degree =
      count.descFactorial (degree + 1) + degree * count.descFactorial degree := by
  by_cases h : degree ≤ count
  · rw [Nat.descFactorial_succ, ← Nat.add_mul, Nat.sub_add_cancel h]
  · rw [Nat.descFactorial_eq_zero_iff_lt.mpr (by omega), Nat.mul_zero,
      Nat.descFactorial_eq_zero_iff_lt.mpr (by omega), Nat.mul_zero, Nat.add_zero]

/-- A power expands in falling factorials with Stirling numbers of the second kind as
coefficients. -/
theorem power_eq_stirling_descFactorial (count degree : Nat) :
    count ^ degree = ∑ order ∈ Finset.range (degree + 1),
      Nat.stirlingSecond degree order * count.descFactorial order := by
  induction degree with
  | zero => simp
  | succ degree ih =>
      rw [pow_succ, ih, Finset.sum_mul,
        Finset.sum_range_succ'
          (fun order => Nat.stirlingSecond (degree + 1) order * count.descFactorial order)]
      simp only [Nat.stirlingSecond_succ_zero, Nat.zero_mul, Nat.add_zero,
        Nat.stirlingSecond_succ_succ, Nat.add_mul, Finset.sum_add_distrib]
      have hshift :
          (∑ order ∈ Finset.range (degree + 1),
            (order + 1) * Nat.stirlingSecond degree (order + 1) * count.descFactorial (order + 1)) =
          ∑ order ∈ Finset.range (degree + 1),
            order * Nat.stirlingSecond degree order * count.descFactorial order := by
        let f := fun order => order * Nat.stirlingSecond degree order * count.descFactorial order
        change (∑ order ∈ Finset.range (degree + 1), f (order + 1)) =
          ∑ order ∈ Finset.range (degree + 1), f order
        calc
          _ = ∑ order ∈ Finset.range (degree + 2), f order := by
            simpa [f] using (Finset.sum_range_succ' f (degree + 1)).symm
          _ = _ := by
            rw [Finset.sum_range_succ]
            simp [f, Nat.stirlingSecond_eq_zero_of_lt (Nat.lt_succ_self degree)]
      simp only [Nat.add_mul, Finset.sum_add_distrib] at hshift
      rw [hshift, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro order _
      calc
        _ = Nat.stirlingSecond degree order * (count * count.descFactorial order) := by ring
        _ = _ := by rw [mul_descFactorial_eq]; ring

/-- Falling factorials are integrable against a Poisson distribution. -/
lemma poisson_integrable_descFactorial (rate : ℝ≥0) (k : Nat) :
    Integrable (fun n : Nat => (n.descFactorial k : ℝ)) (poissonMeasure rate) := by
  rw [integrable_poissonMeasure_iff]
  simpa only [Real.norm_natCast] using (poisson_hasSum_descFactorial rate k).summable

/-- The `k`-th factorial moment of a Poisson distribution of rate `rate` is `rate ^ k`. -/
lemma poisson_integral_descFactorial (rate : ℝ≥0) (k : Nat) :
    (∫ n : Nat, (n.descFactorial k : ℝ) ∂poissonMeasure rate) = (rate : ℝ) ^ k := by
  rw [integral_poissonMeasure]
  simpa only [smul_eq_mul] using (poisson_hasSum_descFactorial rate k).tsum_eq

/-- `power_eq_stirling_descFactorial`, cast to the reals. -/
lemma power_eq_stirling_descFactorial_real (n degree : Nat) :
    (n : ℝ) ^ degree = ∑ k ∈ Finset.range (degree + 1),
      (Nat.stirlingSecond degree k : ℝ) * (n.descFactorial k : ℝ) := by
  exact_mod_cast power_eq_stirling_descFactorial n degree

/-- Powers are integrable against a Poisson distribution. -/
lemma poisson_integrable_power (rate : ℝ≥0) (degree : Nat) :
    Integrable (fun n : Nat => (n : ℝ) ^ degree) (poissonMeasure rate) := by
  simp_rw [power_eq_stirling_descFactorial_real]
  exact integrable_finsetSum _ (fun k _ =>
    (poisson_integrable_descFactorial rate k).const_mul _)

/-- The raw moment of a Poisson distribution is its Touchard polynomial evaluated at the rate. -/
lemma poisson_integral_power (rate : ℝ≥0) (degree : Nat) :
    (∫ n : Nat, (n : ℝ) ^ degree ∂poissonMeasure rate) =
      ∑ k ∈ Finset.range (degree + 1),
        (Nat.stirlingSecond degree k : ℝ) * (rate : ℝ) ^ k := by
  simp_rw [power_eq_stirling_descFactorial_real]
  rw [integral_finsetSum _ (fun k _ =>
    (poisson_integrable_descFactorial rate k).const_mul _)]
  simp_rw [integral_const_mul, poisson_integral_descFactorial]

/-- For an integer rate, the raw moment of a Poisson distribution is `ForsMoments.touchard`. -/
lemma poisson_integral_power_nat (rate degree : Nat) :
    (∫ n : Nat, (n : ℝ) ^ degree ∂poissonMeasure (rate : ℝ≥0)) =
      (ForsMoments.touchard degree rate : ℝ) := by
  rw [poisson_integral_power]
  simp only [ForsMoments.touchard, Nat.cast_sum, Nat.cast_mul, Nat.cast_pow,
    NNReal.coe_natCast]

/-- The exact `order`-th centered moment of `N ^ 14` for a rate-three Poisson load `N`, expressed
through Touchard polynomials. -/
@[expose] def centeredMoment (order : Nat) : ℤ :=
  ∑ k ∈ Finset.range (order + 1),
    (ForsMoments.touchard (14 * k) 3 : ℤ) *
      (-(ForsMoments.touchard 14 3 : ℤ)) ^ (order - k) * order.choose k

/-- Centered powers of powers are integrable against a Poisson distribution. -/
lemma poisson_integrable_centered_power (rate : ℝ≥0) (degree order : Nat) (center : ℝ) :
    Integrable (fun n : Nat => ((n : ℝ) ^ degree - center) ^ order)
      (poissonMeasure rate) := by
  simp only [sub_eq_add_neg, add_pow, ← pow_mul]
  exact integrable_finsetSum _ (fun k _ =>
    ((poisson_integrable_power rate (degree * k)).mul_const _).mul_const _)

/-- The centered moments of `N ^ 14` for a rate-three Poisson load `N` are `centeredMoment`. -/
lemma poisson_integral_centered_power (order : Nat) :
    (∫ n : Nat, ((n : ℝ) ^ 14 - (ForsMoments.touchard 14 3 : ℝ)) ^ order
      ∂poissonMeasure 3) = (centeredMoment order : ℝ) := by
  simp only [sub_eq_add_neg, add_pow, ← pow_mul]
  rw [integral_finsetSum _ (fun k _ =>
    ((poisson_integrable_power 3 (14 * k)).mul_const _).mul_const _)]
  simp only [integral_mul_const]
  have hf (degree : Nat) :
      (∫ n : Nat, (n : ℝ) ^ degree ∂poissonMeasure 3) =
        (ForsMoments.touchard degree 3 : ℝ) := by
    simpa using poisson_integral_power_nat 3 degree
  simp only [hf, centeredMoment, Int.cast_sum, Int.cast_mul, Int.cast_pow,
    Int.cast_neg, Int.cast_natCast]

/-- The centered moments of orders `0` to `4` and `6` of `N ^ 14` for a rate-three Poisson load,
with the bounds used in the concentration argument. -/
theorem centeredMoment_bounds :
    centeredMoment 0 = 1 ∧ centeredMoment 1 = 0 ∧
    0 ≤ centeredMoment 2 ∧ centeredMoment 2 < 2 ^ 92 ∧
    0 ≤ centeredMoment 3 ∧ centeredMoment 3 < 2 ^ 154 ∧
    0 ≤ centeredMoment 4 ∧ centeredMoment 4 < 2 ^ 219 ∧
    0 ≤ centeredMoment 6 ∧ centeredMoment 6 < 2 ^ 359 := by
  simp only [centeredMoment, ForsMoments.touchard_eq_cached]
  decide +kernel

end SlhDsaSecurity.ForsConcentration
