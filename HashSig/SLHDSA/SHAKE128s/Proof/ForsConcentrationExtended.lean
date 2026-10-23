/-
Copyright (c) 2026 Tom Wambsgans. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Wambsgans
-/

module

public import HashSig.SLHDSA.SHAKE128s.Proof.ForsConcentrationOccupancy

/-!
# Additional uniform choices for the shared-oracle exceptional branch

`poisson_count_tail_extended_half` shows, by Chebyshev's inequality, that a Poisson count of
rate `3 * 2^63` reaches `5 * 2^62` with probability at least one half. This is the
de-Poissonization denominator that extends the independent occupancy experiment to five halves
of the number of instances. It does not assert a coupling to the adaptive random-oracle game.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace SlhDsaSecurity.ForsConcentration

set_option exponentiation.threshold 1024 in
/-- A rate-3B Poisson count reaches 5B/2 with probability at least one half. -/
theorem poisson_count_tail_extended_half :
    (1 : ENNReal) / 2 ≤ poissonMeasure (3 * ((2 ^ 63 : Nat) : ℝ≥0)) {n | 5 * 2 ^ 62 ≤ n} := by
  let rate : Nat := 3 * 2 ^ 63
  have hr : (rate : ℝ≥0) = 3 * ((2 ^ 63 : Nat) : ℝ≥0) := by norm_num [rate]
  rw [← hr]
  have hsub : {n : Nat | n < 5 * 2 ^ 62} ⊆
      {n | (2 ^ 62 : ℝ) ^ 2 ≤ ((n : ℝ) - rate) ^ 2} := by
    intro n hn
    have hn' : (n : ℝ) ≤ 23058430092136939520 := by
      exact_mod_cast Nat.le_of_lt hn
    norm_num [rate]
    nlinarith only [hn', sq_nonneg ((n : ℝ) - 23058430092136939520)]
  have hi : Integrable (fun n : Nat => ((n : ℝ) - rate) ^ 2)
      (poissonMeasure (rate : ℝ≥0)) := by
    simpa using poisson_integrable_centered_power (rate : ℝ≥0) 1 2 (rate : ℝ)
  have hm := mul_meas_ge_le_integral_of_nonneg
    (μ := poissonMeasure (rate : ℝ≥0)) (f := fun n : Nat => ((n : ℝ) - rate) ^ 2)
    (Filter.Eventually.of_forall fun n => sq_nonneg ((n : ℝ) - rate)) hi ((2 ^ 62 : ℝ) ^ 2)
  rw [poisson_integral_square_sub] at hm
  have hsmall : (poissonMeasure (rate : ℝ≥0)).real {n | n < 5 * 2 ^ 62} ≤ (1 : ℝ) / 2 := by
    have hmono := measureReal_mono (μ := poissonMeasure (rate : ℝ≥0)) hsub
    have hscaled := mul_le_mul_of_nonneg_left hmono (sq_nonneg (2 ^ 62 : ℝ))
    have hscaled' := hscaled.trans hm
    norm_num [rate] at hscaled'
    linarith
  have hcompl := measureReal_add_measureReal_compl
    (μ := poissonMeasure (rate : ℝ≥0)) (s := {n : Nat | n < 5 * 2 ^ 62}) MeasurableSet.of_discrete
  simp only [probReal_univ] at hcompl
  have hrest : (poissonMeasure (rate : ℝ≥0)).real {n | n < 5 * 2 ^ 62}ᶜ =
      1 - (poissonMeasure (rate : ℝ≥0)).real {n | n < 5 * 2 ^ 62} := by
    apply eq_sub_iff_add_eq.mpr
    simpa only [add_comm] using hcompl
  have htail : (1 : ℝ) / 2 ≤
      (poissonMeasure (rate : ℝ≥0)).real {n | 5 * 2 ^ 62 ≤ n} := by
    have hle : (1 : ℝ) / 2 ≤
        1 - (poissonMeasure (rate : ℝ≥0)).real {n | n < 5 * 2 ^ 62} := by
      linarith only [hsmall]
    rw [← hrest] at hle
    simpa only [Set.compl_ofPred, Nat.not_lt] using hle
  apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
  simpa only [measureReal_def, ENNReal.toReal_div, ENNReal.toReal_one,
    ENNReal.toReal_ofNat] using htail

end SlhDsaSecurity.ForsConcentration
