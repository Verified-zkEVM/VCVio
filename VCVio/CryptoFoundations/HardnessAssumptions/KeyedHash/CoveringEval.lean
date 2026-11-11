/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module

public import VCVio.CryptoFoundations.HardnessAssumptions.KeyedHash.Covering
public import Mathlib.Data.NNRat.Lemmas
import Mathlib.Data.Rat.Cast.CharZero

/-!
# Executable coverage coefficients

Counting functions by image size gives a triangular recurrence for surjection counts.
The table stores each coefficient once; its size depends on the number of FORS digits,
independently of the signing and hash-query budgets.
-/

public section

open scoped ENNReal

namespace KeyedHash.Covering

/-- The semantic coefficient counting surjections onto `r` labelled targets. -/
@[expose] noncomputable def surjectionCount (k r : ℕ) : ℕ :=
  (Finset.univ.filter fun s : Fin k → Fin r => Function.Surjective s).card

/-- Partitioning all functions by image size gives the binomial transform of surjections. -/
theorem pow_eq_sum_choose_mul_surjectionCount (k r : ℕ) :
    r ^ k = ∑ j ∈ Finset.range (r + 1), r.choose j * surjectionCount k j := by
  classical
  have h := Finset.card_eq_sum_card_fiberwise
    (s := (Finset.univ : Finset (Fin k → Fin r)))
    (t := Finset.range (r + 1)) (f := fun f => (Finset.univ.image f).card)
    (fun f _ => Finset.mem_range.mpr (Nat.lt_succ_of_le
      (by simpa using Finset.card_le_univ (Finset.univ.image f))))
  simpa only [Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
    card_filter_card_image_eq, surjectionCount] using h

/-- A surjection coefficient is obtained from the preceding coefficients by exact subtraction. -/
theorem surjectionCount_eq_sub (k r : ℕ) :
    surjectionCount k r =
      r ^ k - ∑ j ∈ Finset.range r, r.choose j * surjectionCount k j := by
  have h := pow_eq_sum_choose_mul_surjectionCount k r
  rw [Finset.sum_range_succ, Nat.choose_self, one_mul] at h
  omega

/-- A table of surjection coefficients for targets `0, …, r - 1`. The recurrence only
uses earlier entries and never enumerates a function space. -/
@[expose] def surjectionTable (k : ℕ) : ℕ → List ℕ
  | 0 => []
  | r + 1 =>
    let row := surjectionTable k r
    row ++ [r ^ k - ((List.range r).map fun j => Nat.fast_choose r j * row.getD j 0).sum]

/-- Every entry in the executable table equals its finite-cardinality specification. -/
theorem surjectionTable_eq (k r : ℕ) :
    surjectionTable k r = (List.range r).map (surjectionCount k) := by
  induction r with
  | zero => rfl
  | succ r ih =>
    rw [surjectionTable, ih, List.range_succ, List.map_append, List.map_singleton]
    congr 2
    rw [surjectionCount_eq_sub]
    congr 1
    rw [← List.sum_toFinset _ List.nodup_range]
    simp only [List.toFinset_range]
    apply Finset.sum_congr rfl
    intro j hj
    have hj' : j < r := by simpa using hj
    simp [List.getD_eq_getElem?_getD, hj', ← Nat.choose_eq_fast_choose]

/-- Exact nonnegative rational evaluation of the weighted coverage polynomial. -/
@[expose] def weightedTargetCoverEval (h a k qs qw : ℕ) (w : ℚ≥0) : ℚ≥0 :=
  let row := surjectionTable k (k + 1)
  ∑ r ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (r + 1),
    ((Nat.fast_choose qs (r - j) * Nat.fast_choose qw j * row.getD r 0 : ℕ) : ℚ≥0) *
      w ^ j * ((((2 : ℚ≥0) ^ h)⁻¹) ^ r * (((2 : ℚ≥0) ^ a)⁻¹) ^ k)

/-- Interpret an exact nonnegative rational as an extended nonnegative real. -/
@[expose] noncomputable def rationalValue (q : ℚ≥0) : ℝ≥0∞ := (q : NNReal)

@[simp] theorem rationalValue_natCast (n : ℕ) : rationalValue n = n := by
  simp [rationalValue]

@[simp] theorem rationalValue_one : rationalValue 1 = 1 := by simp [rationalValue]

@[simp] theorem rationalValue_zero : rationalValue 0 = 0 := by simp [rationalValue]

@[simp] theorem rationalValue_ofNat (n : ℕ) [n.AtLeastTwo] :
    rationalValue ofNat(n) = ofNat(n) := rationalValue_natCast n

@[simp] theorem rationalValue_add (x y : ℚ≥0) :
    rationalValue (x + y) = rationalValue x + rationalValue y := by
  simp [rationalValue, NNRat.cast_add]

@[simp] theorem rationalValue_mul (x y : ℚ≥0) :
    rationalValue (x * y) = rationalValue x * rationalValue y := by
  simp [rationalValue, NNRat.cast_mul]

@[simp] theorem rationalValue_pow (x : ℚ≥0) (n : ℕ) :
    rationalValue (x ^ n) = rationalValue x ^ n := by
  simp [rationalValue, NNRat.cast_pow]

theorem rationalValue_inv {x : ℚ≥0} (hx : x ≠ 0) :
    rationalValue x⁻¹ = (rationalValue x)⁻¹ := by
  have hx' : (x : NNReal) ≠ 0 := by exact_mod_cast hx
  simp [rationalValue, NNRat.cast_inv, ENNReal.coe_inv hx']

theorem rationalValue_div (x : ℚ≥0) {y : ℚ≥0} (hy : y ≠ 0) :
    rationalValue (x / y) = rationalValue x / rationalValue y := by
  simp only [div_eq_mul_inv, rationalValue_mul, rationalValue_inv hy]

/-- Rational inequalities can be transported without numerical approximation. -/
theorem rationalValue_le {x y : ℚ≥0} (h : x ≤ y) : rationalValue x ≤ rationalValue y := by
  unfold rationalValue
  exact ENNReal.coe_le_coe.mpr (by exact_mod_cast h)

@[simp] theorem rationalValue_le_iff {x y : ℚ≥0} : rationalValue x ≤ rationalValue y ↔ x ≤ y := by
  constructor
  · intro h
    have hc : (x : NNReal) ≤ (y : NNReal) := ENNReal.coe_le_coe.mp h
    exact_mod_cast hc
  · exact rationalValue_le

@[simp] theorem rationalValue_min (x y : ℚ≥0) :
    rationalValue (min x y) = min (rationalValue x) (rationalValue y) := by
  rcases le_total x y with h | h
  · rw [min_eq_left h, min_eq_left (rationalValue_le h)]
  · rw [min_eq_right h, min_eq_right (rationalValue_le h)]

/-- Coverage increases with either query budget and with the weighted exposure probability. -/
theorem weightedTargetCoverBound_mono {qs qs' qw qw' : ℕ} {w w' : ℝ≥0∞}
    (h a k : ℕ) (hs : qs ≤ qs') (hh : qw ≤ qw') (hw : w ≤ w') :
    weightedTargetCoverBound h a k qs qw w ≤ weightedTargetCoverBound h a k qs' qw' w' := by
  unfold weightedTargetCoverBound
  apply Finset.sum_le_sum
  intro r _
  apply Finset.sum_le_sum
  intro j _
  have hc : qs.choose (r - j) * qw.choose j * surjectionCount k r ≤
      qs'.choose (r - j) * qw'.choose j * surjectionCount k r :=
    Nat.mul_le_mul_right _ (Nat.mul_le_mul (Nat.choose_le_choose _ hs) (Nat.choose_le_choose _ hh))
  have hc' : ((qs.choose (r - j) * qw.choose j * surjectionCount k r : ℕ) : ℝ≥0∞) ≤
      ((qs'.choose (r - j) * qw'.choose j * surjectionCount k r : ℕ) : ℝ≥0∞) := by
    exact_mod_cast hc
  exact mul_le_mul' (mul_le_mul' hc' (pow_le_pow_left' hw j)) le_rfl

/-- Executing the evaluator computes exactly the coefficient in the security theorem. -/
theorem rationalValue_weightedTargetCoverEval (h a k qs qw : ℕ) (w : ℚ≥0) :
    rationalValue (weightedTargetCoverEval h a k qs qw w) =
      weightedTargetCoverBound h a k qs qw (rationalValue w) := by
  unfold weightedTargetCoverEval weightedTargetCoverBound rationalValue
  rw [surjectionTable_eq]
  simp only [← Nat.choose_eq_fast_choose]
  change ((NNRat.castHom NNReal) _ : ℝ≥0∞) = _
  simp only [map_sum, ENNReal.ofNNReal_finsetSum]
  apply Finset.sum_congr rfl
  intro r hr
  apply Finset.sum_congr rfl
  intro j _
  have hr' : r < k + 1 := Finset.mem_range.mp hr
  have hentry : ((List.range (k + 1)).map (surjectionCount k)).getD r 0 =
      surjectionCount k r := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hr']
    rfl
  rw [hentry]
  change (↑(((_ : ℚ≥0) : NNReal)) : ℝ≥0∞) = _
  simp [surjectionCount,
    NNRat.cast_mul, NNRat.cast_pow, NNRat.cast_inv, ENNReal.coe_mul,
    ENNReal.coe_pow, ENNReal.coe_inv, ENNReal.inv_pow]

end KeyedHash.Covering
