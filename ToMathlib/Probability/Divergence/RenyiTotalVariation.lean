/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import ToMathlib.Probability.Divergence.Renyi
public import ToMathlib.Probability.Divergence.TotalVariation
public import ToMathlib.MeasureTheory.Measure.TotalVariation

/-!
# Renyi divergence against total variation

Total variation between probability measures is controlled by every Renyi divergence of order
`a > 1` and by the max-divergence.

For `μ ≪ ν` the two measures have densities `∂μ/∂ν` and `1` against `ν`, so Scheffé's bound
reduces total variation to half the `L¹` distance between those densities, and
`lintegral_absDiff_div_two_rpow_two_le` compares that with the Hellinger affinity `M_{1/2}`.
Log-convexity of the MGF (`renyiDiv_inv_le_renyiMGF_half_rpow_two`) then passes from order `1/2`
to any order `a > 1`.
-/

public section

open MeasureTheory
open scoped ENNReal

namespace InformationTheory

variable {α : Type*} [MeasurableSpace α]

/-- **Scheffé bound.** Total variation between probability measures `μ ≪ ν` is at most half the
`L¹` distance between the likelihood ratio and one. -/
theorem etvDist_le_lintegral_absDiff_rnDeriv_div_two {μ ν : Measure α} [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (hac : μ ≪ ν) :
    μ.etvDist ν ≤ (∫⁻ x, ENNReal.absDiff (μ.rnDeriv ν x) 1 ∂ν) / 2 := by
  set f := μ.rnDeriv ν
  have hf : Measurable f := Measure.measurable_rnDeriv μ ν
  have hset : ∀ s, ∫⁻ x in s, f x ∂ν = μ s := Measure.setLIntegral_rnDeriv hac
  have hf1 : ∫⁻ x, f x ∂ν = 1 := by
    rw [← setLIntegral_univ, hset, measure_univ]
  set P := ∫⁻ x, (f x - 1) ∂ν
  set N := ∫⁻ x, (1 - f x) ∂ν
  -- The positive and negative parts of `f - 1` have equal mass, since `∫ f = ∫ 1`.
  have hPN : P = N := by
    have hP : P + 1 = ∫⁻ x, max (f x) 1 ∂ν := by
      have h : ∫⁻ x, (f x - 1 + 1) ∂ν = P + ∫⁻ _, 1 ∂ν :=
        lintegral_add_right _ measurable_const
      rw [lintegral_one, measure_univ] at h
      rw [← h]
      exact lintegral_congr fun x => tsub_add_eq_max
    have hN : N + 1 = ∫⁻ x, max (f x) 1 ∂ν := by
      have h : ∫⁻ x, (1 - f x + f x) ∂ν = N + ∫⁻ x, f x ∂ν := lintegral_add_right _ hf
      rw [hf1] at h
      rw [← h]
      exact lintegral_congr fun x => by rw [tsub_add_eq_max, max_comm]
    exact (ENNReal.add_left_inj ENNReal.one_ne_top).1 (hP.trans hN.symm)
  have hD : ∫⁻ x, ENNReal.absDiff (f x) 1 ∂ν = 2 * P := by
    have h : ∫⁻ x, ((f x - 1) + (1 - f x)) ∂ν = P + N :=
      lintegral_add_left (hf.sub measurable_const : Measurable fun x => f x - 1) _
    rw [two_mul]
    nth_rw 2 [hPN]
    rw [← h]
    rfl
  rw [hD, mul_comm, ENNReal.mul_div_cancel_right two_ne_zero ENNReal.ofNat_ne_top]
  refine iSup_le fun A => ENNReal.absDiff_le_iff.2 ⟨?_, ?_⟩
  · -- `μ A = ∫_A f ≤ ∫_A ((f - 1) + 1) ≤ P + ν A`.
    calc μ A.1 = ∫⁻ x in A.1, f x ∂ν := (hset A.1).symm
      _ ≤ ∫⁻ x in A.1, ((f x - 1) + 1) ∂ν := lintegral_mono fun x => le_tsub_add
      _ = ∫⁻ x in A.1, (f x - 1) ∂ν + ν A.1 := by
          rw [lintegral_add_right _ measurable_const, lintegral_one, Measure.restrict_apply_univ]
      _ ≤ P + ν A.1 := by gcongr; exact setLIntegral_le_lintegral _ _
      _ = ν A.1 + P := add_comm _ _
  · -- `ν A = ∫_A 1 ≤ ∫_A ((1 - f) + f) ≤ N + μ A`.
    calc ν A.1 = ∫⁻ _ in A.1, 1 ∂ν := by rw [lintegral_one, Measure.restrict_apply_univ]
      _ ≤ ∫⁻ x in A.1, ((1 - f x) + f x) ∂ν := lintegral_mono fun x => le_tsub_add
      _ = ∫⁻ x in A.1, (1 - f x) ∂ν + μ A.1 := by
          rw [lintegral_add_right _ hf, hset]
      _ ≤ N + μ A.1 := by gcongr; exact setLIntegral_le_lintegral _ _
      _ = μ A.1 + P := by rw [hPN, add_comm]

/-- **Total variation against the Hellinger affinity.** For probability measures `μ ≪ ν`,
`TV(μ, ν)² ≤ 1 - M_{1/2}(μ ‖ ν)²`. -/
theorem etvDist_rpow_two_le_one_sub_renyiMGF_half {μ ν : Measure α} [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (hac : μ ≪ ν) :
    μ.etvDist ν ^ (2 : ℝ) ≤ 1 - renyiMGF (1 / 2) μ ν ^ (2 : ℝ) := by
  have hf1 : ∫⁻ x, μ.rnDeriv ν x ∂ν = 1 := by
    rw [← setLIntegral_univ, Measure.setLIntegral_rnDeriv hac, measure_univ]
  have key := lintegral_absDiff_div_two_rpow_two_le ν
    (Measure.measurable_rnDeriv μ ν).aemeasurable aemeasurable_const hf1
    (by rw [lintegral_one, measure_univ])
  simp only [mul_one] at key
  rw [renyiMGF_of_ac hac]
  exact (ENNReal.rpow_le_rpow (etvDist_le_lintegral_absDiff_rnDeriv_div_two hac)
    (by norm_num)).trans key

/-- **Renyi divergence bounds total variation.** For probability measures and any order
`a > 1`, `TV(μ, ν)² ≤ 1 - R_a(μ ‖ ν)⁻¹`. -/
theorem etvDist_rpow_two_le_one_sub_inv_renyiDiv {a : ℝ} (ha : 1 < a) (μ ν : Measure α)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    μ.etvDist ν ^ (2 : ℝ) ≤ 1 - (renyiDiv a μ ν)⁻¹ := by
  by_cases hac : μ ≪ ν
  · exact (etvDist_rpow_two_le_one_sub_renyiMGF_half hac).trans
      (tsub_le_tsub_left (renyiDiv_inv_le_renyiMGF_half_rpow_two ha μ ν hac) 1)
  · rw [renyiDiv_eq_rpow ha, renyiMGF_of_not_ac hac,
      ENNReal.top_rpow_of_pos (inv_pos.2 (sub_pos.2 ha)), ENNReal.inv_top, tsub_zero]
    exact ENNReal.rpow_le_one (Measure.etvDist_le_one μ ν (by simp) (by simp)) (by norm_num)

/-- **Max-divergence bounds total variation.** For probability measures,
`TV(μ, ν) ≤ 1 - D_∞(μ ‖ ν)⁻¹`. -/
theorem etvDist_le_one_sub_inv_maxDiv (μ ν : Measure α) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] : μ.etvDist ν ≤ 1 - (maxDiv μ ν)⁻¹ := by
  classical
  set D := maxDiv μ ν
  by_cases hD : D = ⊤ ∨ ¬ μ ≪ ν
  · have hDtop : D = ⊤ := hD.elim id fun h => by simp [D, maxDiv, h]
    rw [hDtop, ENNReal.inv_top, tsub_zero]
    exact Measure.etvDist_le_one μ ν (by simp) (by simp)
  push Not at hD
  obtain ⟨hDtop, hac⟩ := hD
  have hle : ∀ s, μ s ≤ D * ν s := measure_le_maxDiv_mul hac
  have hD1 : 1 ≤ D := by simpa using hle Set.univ
  have hD0 : D ≠ 0 := (zero_lt_one.trans_le hD1).ne'
  set e := 1 - D⁻¹
  -- On every event, `μ` exceeds `ν` by at most `e`.
  have hup : ∀ s, μ s ≤ ν s + e := fun s => by
    have hνs : μ s * D⁻¹ ≤ ν s := by
      rw [← div_eq_mul_inv]
      exact ENNReal.div_le_of_le_mul (by rw [mul_comm]; exact hle s)
    calc μ s = μ s * D⁻¹ + μ s * e := by
          rw [← mul_add, add_tsub_cancel_of_le (ENNReal.inv_le_one.2 hD1), mul_one]
      _ ≤ ν s + 1 * e := by
          gcongr
          exact prob_le_one
      _ = ν s + e := by rw [one_mul]
  refine iSup_le fun A => ENNReal.absDiff_le_iff.2 ⟨hup A.1, ?_⟩
  -- The other direction is the same bound on the complement.
  have hc := hup A.1ᶜ
  rw [prob_compl_eq_one_sub A.2, prob_compl_eq_one_sub A.2] at hc
  calc ν A.1 = 1 - (1 - ν A.1) := (ENNReal.sub_sub_cancel ENNReal.one_ne_top prob_le_one).symm
    _ ≤ μ A.1 + e := by
        rw [tsub_le_iff_right]
        calc 1 ≤ (1 - μ A.1) + μ A.1 := le_tsub_add
          _ ≤ (1 - ν A.1 + e) + μ A.1 := by gcongr
          _ = μ A.1 + e + (1 - ν A.1) := by ring

end InformationTheory
