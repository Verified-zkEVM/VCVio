/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module

public import HashSig.SLHDSA.Security.BoundEval

/-!
# Uniform budget-range bounds

A coefficient envelope covers every hash budget between a positive minimum and a chosen
maximum, and every signing budget up to the lifetime cap. Unlike a point evaluation, the
same coefficient bounds the complete range. The verifier overhead is divided by the minimum
hash budget, and coverage is evaluated at the maximum budgets.
-/

public section

open scoped ENNReal
open KeyedHash.Covering

namespace SLHDSA.Security

/-- A uniform coefficient for the structured `c = 2, r = 1` bound on a budget rectangle. -/
@[expose] def securityCoefficientEval (p : Params) (card minHash maxHash maxSign : ℕ) : ℚ≥0 :=
  (1 + 1 / (minHash : ℚ≥0)) *
      weightedTargetCoverEval p.h p.a p.k maxSign maxHash ((maxSign : ℚ≥0) / card) +
    (2 + 2 * (GeneralScheme.verifyInternalQueryBound p : ℚ≥0) / minHash) / card

/-- Coverage evaluation is monotone in both query budgets at any positive node cardinality. -/
theorem weightedTargetCoverEval_query_mono (p : Params) {card qh qs qh' qs' : ℕ}
    (hc : card ≠ 0) (hh : qh ≤ qh') (hs : qs ≤ qs') :
    weightedTargetCoverEval p.h p.a p.k qs qh ((qs : ℚ≥0) / card) ≤
      weightedTargetCoverEval p.h p.a p.k qs' qh' ((qs' : ℚ≥0) / card) := by
  rw [← rationalValue_le_iff, rationalValue_weightedTargetCoverEval,
    rationalValue_weightedTargetCoverEval]
  have hc' : (card : ℚ≥0) ≠ 0 := by exact_mod_cast hc
  simp only [rationalValue_div _ hc', rationalValue_natCast]
  apply weightedTargetCoverBound_mono p.h p.a p.k hs hh
  gcongr

/-- The exact structured bound is below the same linear coefficient throughout the budget
range. The minimum must be positive; no assertion at zero adversary work is hidden. -/
theorem securityBoundEval_le_mul_coefficient (p : Params)
    {card minHash maxHash maxSign qh qs : ℕ} (hc : card ≠ 0) (hmin : minHash ≠ 0)
    (hlo : minHash ≤ qh) (hhi : qh ≤ maxHash) (hs : qs ≤ maxSign) :
    securityBoundEval p card 2 1 qh qs ≤
      (qh : ℚ≥0) * securityCoefficientEval p card minHash maxHash maxSign := by
  have hcover := weightedTargetCoverEval_query_mono p hc hhi hs
  have hcq : (0 : ℚ) < card := by exact_mod_cast Nat.pos_of_ne_zero hc
  have hlq : (0 : ℚ) < minHash := by exact_mod_cast Nat.pos_of_ne_zero hmin
  have hq : (minHash : ℚ) ≤ qh := by exact_mod_cast hlo
  apply NNRat.coe_le_coe.mp
  simp only [securityBoundEval, securityCoefficientEval, NNRat.coe_add, NNRat.coe_mul,
    NNRat.coe_div, NNRat.coe_natCast]
  have hcover' :
      (weightedTargetCoverEval p.h p.a p.k qs qh ((qs : ℚ≥0) / card) : ℚ) ≤
      (weightedTargetCoverEval p.h p.a p.k maxSign maxHash ((maxSign : ℚ≥0) / card) : ℚ) :=
    NNRat.coe_le_coe.mpr hcover
  have hnonneg :
      (0 : ℚ) ≤ weightedTargetCoverEval p.h p.a p.k maxSign maxHash ((maxSign : ℚ≥0) / card) :=
    (weightedTargetCoverEval _ _ _ _ _ _).property
  have hfactor : (qh : ℚ) + 1 ≤ qh * (1 + 1 / (minHash : ℚ)) := by
    apply (mul_le_mul_iff_right₀ hlq).mp
    field_simp
    nlinarith
  have hprod := mul_le_mul hfactor hcover' (by positivity) (by positivity)
  have hv :
      ((2 : ℚ) * qh + 2 * GeneralScheme.verifyInternalQueryBound p) / card ≤
      qh * ((2 + 2 * (GeneralScheme.verifyInternalQueryBound p : ℚ) / minHash) / card) := by
    apply (div_le_iff₀ hcq).mpr
    field_simp
    nlinarith
  convert add_le_add hprod hv using 1 <;> push_cast <;> ring

/-- The executable coefficient controls the original extended-real bound across the range. -/
theorem securityBound_le_mul_coefficient (p : Params)
    {card minHash maxHash maxSign qh qs : ℕ} (hc : card ≠ 0) (hmin : minHash ≠ 0)
    (hlo : minHash ≤ qh) (hhi : qh ≤ maxHash) (hs : qs ≤ maxSign) :
    securityBound p card 2 1 qh qs ≤
      (qh : ℝ≥0∞) * rationalValue (securityCoefficientEval p card minHash maxHash maxSign) := by
  rw [← rationalValue_securityBoundEval p hc 2 1 qh qs,
    ← rationalValue_natCast qh, ← rationalValue_mul, rationalValue_le_iff]
  exact securityBoundEval_le_mul_coefficient p hc hmin hlo hhi hs

/-- A single exact rational certificate yields the same bit floor at every budget in the
rectangle. Honest verification remains included in the coefficient. -/
theorem securityBound_le_div_pow_of_coefficient (p : Params)
    {card minHash maxHash maxSign qh qs bits : ℕ} (hc : card ≠ 0) (hmin : minHash ≠ 0)
    (hlo : minHash ≤ qh) (hhi : qh ≤ maxHash) (hs : qs ≤ maxSign)
    (hcert : securityCoefficientEval p card minHash maxHash maxSign ≤ 1 / (2 : ℚ≥0) ^ bits) :
    securityBound p card 2 1 qh qs ≤ (qh : ℝ≥0∞) / (2 : ℝ≥0∞) ^ bits := by
  apply (securityBound_le_mul_coefficient p hc hmin hlo hhi hs).trans
  have hh := rationalValue_le hcert
  have hr : rationalValue (1 / (2 : ℚ≥0) ^ bits) = 1 / (2 : ℝ≥0∞) ^ bits := by
    rw [rationalValue_div _ (by positivity), rationalValue_one, rationalValue_pow,
      rationalValue_ofNat]
  rw [hr] at hh
  simpa only [div_eq_mul_inv, one_mul] using mul_le_mul' (le_refl (qh : ℝ≥0∞)) hh

end SLHDSA.Security
