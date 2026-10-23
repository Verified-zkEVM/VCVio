/-
Copyright (c) 2026 Tom Wambsgans. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Wambsgans
-/

module

public import HashSig.SLHDSA.SHAKE128s.Proof.ForsDisclosureTape
public import HashSig.SLHDSA.SHAKE128s.Proof.ForsAdaptiveTargets
public import VCVio.OracleComp.QueryTracking.RandomOracle.DeferredSampling

/-!
# A sharper FORS load cap

A smaller cap on the FORS load potential, `∑ i, loads i ^ 14 ≤ 2 ^ 102`, improves the
fresh-target coverage bound to `2 ^ -129` (`ForsCoverage.fresh_coverage_le_sharper`), at a larger
tail cost: the cap fails with probability at most `2 ^ -127` under Poisson loads
(`ForsConcentration.poisson_load_tail_sharper`, by a sixth-moment Markov bound around the exact
mean), hence at most `2 ^ -126` for up to `5 * 2 ^ 62` uniform choices
(`ForsConcentration.uniform_load_tail_sharper_of_le`) and for the disclosure tape
(`ForsDisclosureTape.bad_load_probability_sharper`).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory OracleComp OracleSpec
open scoped NNReal ENNReal

namespace SlhDsaSecurity.ForsConcentration

/-- The Touchard polynomial value `T₁₄(3)`, the exact fourteenth moment of a `Poisson(3)` load. -/
theorem touchard_fourteen_three : ForsMoments.touchard 14 3 = 461101962108 := by
  rw [ForsMoments.touchard_eq_cached]
  decide +kernel

set_option exponentiation.threshold 1024 in
/-- The exact mean leaves enough room below 2^102 for a sixth-moment bound. -/
theorem poisson_load_tail_sharper :
    poissonLoads (2 ^ 63) {loads | (2 ^ 102 : ℝ) ≤ loadPotential loads} ≤
      (1 : ENNReal) / 2 ^ 127 := by
  let gap : ℝ := 2 ^ 102 - 2 ^ 63 * 461101962108
  let threshold : ℝ := gap ^ 6
  let bound : ℝ := (2 ^ 63 : ℝ) * 2 ^ 359 +
    15 * (2 ^ 63) ^ 2 * 2 ^ 219 * 2 ^ 92 +
    10 * (2 ^ 63) ^ 2 * 2 ^ 308 +
    15 * (2 ^ 63) ^ 3 * (2 ^ 92) ^ 3
  have hgap : 0 < gap := by norm_num [gap]
  have ht : 0 < threshold := pow_pos hgap _
  have hsubset : {loads : Fin (2 ^ 63) → Nat | (2 ^ 102 : ℝ) ≤ loadPotential loads} ⊆
      {loads | threshold ≤ centeredLoadSum loads ^ 6} := by
    intro loads hl
    change (2 ^ 102 : ℝ) ≤ loadPotential loads at hl
    have hcenter : gap ≤ centeredLoadSum loads := by
      rw [centeredLoadSum_eq, touchard_fourteen_three]
      simpa only [gap, Nat.cast_pow, Nat.cast_ofNat] using
        sub_le_sub_right hl ((2 ^ 63 : ℝ) * 461101962108)
    exact pow_le_pow_left₀ hgap.le hcenter 6
  have hmarkov := mul_meas_ge_le_integral_of_nonneg
    (μ := poissonLoads (2 ^ 63))
    (f := fun loads => centeredLoadSum loads ^ 6)
    (Filter.Eventually.of_forall (fun loads =>
      (show Even 6 by decide).pow_nonneg (centeredLoadSum loads)))
    (poisson_centered_sum_moments (2 ^ 63) 6 (by decide)).1 threshold
  have hprob : (poissonLoads (2 ^ 63)).real
      {loads | (2 ^ 102 : ℝ) ≤ loadPotential loads} ≤ bound / threshold := by
    apply (le_div_iff₀ ht).mpr
    calc
      _ ≤ (poissonLoads (2 ^ 63)).real
          {loads | threshold ≤ centeredLoadSum loads ^ 6} * threshold :=
        mul_le_mul_of_nonneg_right (measureReal_mono hsubset) ht.le
      _ ≤ ∫ loads, centeredLoadSum loads ^ 6 ∂poissonLoads (2 ^ 63) := by
        simpa only [mul_comm] using hmarkov
      _ ≤ bound := poisson_sixth_sum_bound
  have hscalar : bound / threshold < (1 : ℝ) / 2 ^ 127 := by
    norm_num [bound, threshold, gap]
  apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
  change (poissonLoads (2 ^ 63)).real {loads | (2 ^ 102 : ℝ) ≤ loadPotential loads} ≤ _
  simpa using hprob.trans hscalar.le

set_option exponentiation.threshold 1024 in
/-- At most 5*2^62 independent choices satisfy the smaller cap except with probability 2^-126. -/
theorem uniform_load_tail_sharper_of_le (requests : Nat) (hrequests : requests ≤ 5 * 2 ^ 62) :
    uniformLoads (2 ^ 63) requests {loads | 2 ^ 102 < ∑ i, loads i ^ 14} ≤
      (1 : ENNReal) / 2 ^ 126 := by
  have hup : ∀ {a b : Fin (2 ^ 63) → Nat}, a ≤ b →
      (2 ^ 102 : ℝ) ≤ loadPotential a → (2 ^ 102 : ℝ) ≤ loadPotential b := by
    intro a b hab ha
    refine ha.trans (Finset.sum_le_sum (fun i _ => ?_))
    exact pow_le_pow_left₀ (Nat.cast_nonneg _) (Nat.cast_le.mpr (hab i)) 14
  have hcouple := uniformLoads_mul_poisson_tail_le (2 ^ 63) (5 * 2 ^ 62)
    {loads | (2 ^ 102 : ℝ) ≤ loadPotential loads} hup
  have hhalf := mul_le_mul_right poisson_count_tail_extended_half
    (uniformLoads (2 ^ 63) (5 * 2 ^ 62) {loads | (2 ^ 102 : ℝ) ≤ loadPotential loads})
  have hbound := hhalf.trans (hcouple.trans poisson_load_tail_sharper)
  have htail : uniformLoads (2 ^ 63) (5 * 2 ^ 62)
      {loads | (2 ^ 102 : ℝ) ≤ loadPotential loads} ≤ (1 : ENNReal) / 2 ^ 126 := by
    apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
    have hreal := ENNReal.toReal_mono (by finiteness) hbound
    norm_num only [ENNReal.toReal_mul, ENNReal.toReal_div, ENNReal.toReal_pow,
      ENNReal.toReal_ofNat, ENNReal.toReal_one] at hreal ⊢
    linarith
  have hsub : {loads : Fin (2 ^ 63) → Nat | 2 ^ 102 < ∑ i, loads i ^ 14} ⊆
      {loads | (2 ^ 102 : ℝ) ≤ loadPotential loads} := by
    intro loads hloads
    change (2 ^ 102 : ℝ) ≤ ∑ i, (loads i : ℝ) ^ 14
    exact_mod_cast Nat.le_of_lt hloads
  exact (measure_mono hsub).trans
    ((uniformLoads_monotone (2 ^ 63) _ hup hrequests).trans htail)

end SlhDsaSecurity.ForsConcentration

namespace SlhDsaSecurity.ForsCoverage

/-- Smaller load cap for use when the joint query accounting needs a smaller coverage
coefficient. -/
theorem fresh_coverage_le_sharper (revealed : Disclosures) (loads : Instance → Nat)
    (hload : ∀ index tree, (revealed index tree).card ≤ loads index)
    (hmoment : ∑ index, loads index ^ 14 ≤ 2 ^ 102) :
    Pr{let x ← ($ᵗ View : ProbComp View)}[(Covered revealed) x] ≤
      1 / ((2 ^ 129 : Nat) : ℝ≥0∞) := by
  have hcount : (∑ index : Instance, ∏ tree : Tree, (revealed index tree).card) ≤ 2 ^ 102 := by
    apply le_trans (Finset.sum_le_sum fun index _ => ?_) hmoment
    calc
      _ ≤ ∏ _ : Tree, loads index := Finset.prod_le_prod (fun tree _ => hload index tree)
      _ = loads index ^ 14 := by
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
        rfl
  rw [fresh_coverage]
  calc
    _ ≤ ((2 ^ 102 : Nat) : ℝ≥0∞) / ((2 ^ 231 : Nat) : ℝ≥0∞) :=
      ENNReal.div_le_div_right (Nat.cast_le.mpr hcount) _
    _ = _ := by
      apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
      norm_num

end SlhDsaSecurity.ForsCoverage

namespace SlhDsaSecurity.ForsDisclosureTape

/-- A disclosure tape of at most `5 * 2 ^ 62` requests exceeds the smaller load cap with
probability at most `2 ^ -126`. -/
theorem bad_load_probability_sharper (requests : Nat) (hrequests : requests ≤ 5 * 2 ^ 62) :
    Pr{let tape ← ($ᵗ Tape requests : ProbComp (Tape requests))}[
        2 ^ 102 < ∑ i, loads tape i ^ 14] ≤
      (1 : ℝ≥0∞) / 2 ^ 126 := by
  rw [loads_probability (fun counts => 2 ^ 102 < ∑ i, counts i ^ 14)]
  exact ForsConcentration.uniform_load_tail_sharper_of_le requests hrequests

end SlhDsaSecurity.ForsDisclosureTape
