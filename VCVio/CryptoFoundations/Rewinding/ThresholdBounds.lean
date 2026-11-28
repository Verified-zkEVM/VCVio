/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.CryptoFoundations.Rewinding.Finder
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Data.Fintype.BigOperators
public import ToMathlib.Data.ENNReal.Gauss

/-!
# Finite averages and threshold error

Acceptance rates decompose along the first challenge coordinate. The complement of the threshold
error is multiplicative over rounds, yielding the affine recursion for successive extraction steps.
The threshold error is at most the sum of the per-round errors (`thresholdError_le_sum`). An
acceptance rate is at most one (`acceptRate_le_one`), and averaging commutes with affine estimates
(`average_affine`). The
generic `ℝ≥0∞` identities behind these recursions live in `ToMathlib.Data.ENNReal.Gauss`.
-/

public section

open scoped ENNReal

namespace Rewinding

/-- The acceptance rate is the average of the Boolean acceptance indicators. -/
theorem acceptRate_eq_sum {R : Type} [Fintype R] [DecidableEq R] {C : R → Type}
    [∀ r, Fintype (C r)]
    (f : ((r : R) → C r) → Bool) :
    acceptRate f = (∑ c, if f c then (1 : ℝ≥0∞) else 0) /
      Fintype.card ((r : R) → C r) := by
  rw [acceptRate]
  congr 1
  simp only [← Finset.sum_boole]

/-- Acceptance of a complete vector is the average acceptance rate of its first-coordinate
sections. -/
theorem acceptRate_cons {n : ℕ} {C : Fin (n + 1) → Type}
    [∀ i, Fintype (C i)]
    (f : ((i : Fin (n + 1)) → C i) → Bool) :
    acceptRate f = (∑ c : C 0, acceptRate (fun q => f (Fin.cons c q))) /
      Fintype.card (C 0) := by
  classical
  simp only [acceptRate_eq_sum]
  have hcard := Fintype.card_congr (Fin.consEquiv C)
  rw [Fintype.card_prod] at hcard
  have hsum : (∑ q : (i : Fin (n + 1)) → C i, if f q then (1 : ℝ≥0∞) else 0) =
      ∑ c : C 0, ∑ q : (i : Fin n) → C i.succ,
        if f (Fin.cons c q) then (1 : ℝ≥0∞) else 0 := by
    calc
      _ = ∑ cq : C 0 × ((i : Fin n) → C i.succ),
          if f (Fin.cons cq.1 cq.2) then (1 : ℝ≥0∞) else 0 :=
        (Fintype.sum_equiv (Fin.consEquiv C) _ _ (fun _ => rfl)).symm
      _ = _ := Fintype.sum_prod_type _
  rw [hsum, ← hcard, Nat.cast_mul]
  simp only [div_eq_mul_inv]
  rw [ENNReal.mul_inv (Or.inr (by finiteness)) (Or.inl (by finiteness)),
    ← Finset.sum_mul]
  ring

/-- Every factor in the complement of the threshold error lies below one. -/
theorem thresholdError_factor_le_one {R : Type} (C : R → Type)
    [∀ r, Fintype (C r)] (k : R → ℕ) (r : R) :
    1 - ((k r - 1 : ℕ) : ℝ≥0∞) / Fintype.card (C r) ≤ 1 := tsub_le_self

/-- The threshold error lies between zero and one. -/
theorem thresholdError_le_one {R : Type} [Fintype R] (C : R → Type)
    [∀ r, Fintype (C r)] (k : R → ℕ) : thresholdError C k ≤ 1 := tsub_le_self

/-- The complement of the threshold error is the product of the per-round complements. -/
theorem one_sub_thresholdError {R : Type} [Fintype R] (C : R → Type)
    [∀ r, Fintype (C r)] (k : R → ℕ) :
    1 - thresholdError C k =
      ∏ r, (1 - ((k r - 1 : ℕ) : ℝ≥0∞) / Fintype.card (C r)) := by
  rw [thresholdError]
  apply ENNReal.sub_sub_cancel (by finiteness)
  exact Finset.prod_le_one (fun r _ => thresholdError_factor_le_one C k r)

/-- The complement of threshold error factors into its first-round and tail contributions. -/
theorem one_sub_thresholdError_cons {n : ℕ} (C : Fin (n + 1) → Type)
    [∀ i, Fintype (C i)] (k : Fin (n + 1) → ℕ) :
    1 - thresholdError C k =
      (1 - ((k 0 - 1 : ℕ) : ℝ≥0∞) / Fintype.card (C 0)) *
        (1 - thresholdError (fun i : Fin n => C i.succ) (fun i => k i.succ)) := by
  rw [one_sub_thresholdError, Fin.prod_univ_succ, one_sub_thresholdError]

/-- The threshold error is at most the sum of the per-round errors `(k r - 1) / |C r|`. -/
theorem thresholdError_le_sum {R : Type} [Fintype R] (C : R → Type) [∀ r, Fintype (C r)]
    (k : R → ℕ) :
    thresholdError C k ≤ ∑ r, ((k r - 1 : ℕ) : ℝ≥0∞) / Fintype.card (C r) :=
  ENNReal.one_sub_prod_one_sub_le_sum Finset.univ _

/-- Per-round threshold error is at most one when the requested threshold fits the challenge
set. -/
theorem thresholdError_ratio_le_one {α : Type} [Fintype α] {k : ℕ}
    (hk0 : 1 ≤ k) (hk : k ≤ Fintype.card α) :
    ((k - 1 : ℕ) : ℝ≥0∞) / Fintype.card α ≤ 1 := by
  have hcard : (Fintype.card α : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast (show Fintype.card α ≠ 0 by omega)
  rw [ENNReal.div_le_iff hcard (by finiteness), one_mul]
  exact_mod_cast (show k - 1 ≤ Fintype.card α by omega)

/-- The threshold error combines its first-round error and the surviving tail error. -/
theorem thresholdError_cons {n : ℕ} (C : Fin (n + 1) → Type)
    [∀ i, Fintype (C i)] (k : Fin (n + 1) → ℕ)
    (hk0 : 1 ≤ k 0) (hk : k 0 ≤ Fintype.card (C 0)) :
    thresholdError C k =
      ((k 0 - 1 : ℕ) : ℝ≥0∞) / Fintype.card (C 0) +
      (1 - ((k 0 - 1 : ℕ) : ℝ≥0∞) / Fintype.card (C 0)) *
        thresholdError (fun i : Fin n => C i.succ) (fun i => k i.succ) := by
  rw [thresholdError, Fin.prod_univ_succ, ← one_sub_thresholdError]
  exact ENNReal.one_sub_one_sub_mul_one_sub_eq_add_one_sub_mul (thresholdError_ratio_le_one hk0 hk)
    (thresholdError_le_one _ _)

/-- Affine success estimates compose with the same multiplicative error complement. -/
theorem affine_error_compose {a b p ε : ℝ≥0∞} (ha : a ≤ 1) (hb : b ≤ 1)
    (h : ε ≤ b + (1 - b) * (a + (1 - a) * p)) :
    ε ≤ (a + (1 - a) * b) + (1 - (a + (1 - a) * b)) * p := by
  apply h.trans_eq
  rw [ENNReal.one_sub_add_one_sub_mul ha hb, mul_add, ← add_assoc]
  have hab : b + (1 - b) * a = a + (1 - a) * b := by
    rw [← ENNReal.one_sub_one_sub_mul_one_sub_eq_add_one_sub_mul hb ha, mul_comm,
      ENNReal.one_sub_one_sub_mul_one_sub_eq_add_one_sub_mul ha hb]
  rw [hab]
  ring

/-- The acceptance rate of any acceptance function is at most one. -/
theorem acceptRate_le_one {R : Type} [Fintype R] [DecidableEq R] {C : R → Type}
    [∀ r, Fintype (C r)] (f : ((r : R) → C r) → Bool) : acceptRate f ≤ 1 := by
  rw [acceptRate]
  refine ENNReal.div_le_of_le_mul ?_
  rw [one_mul]
  exact_mod_cast Finset.card_filter_le _ _

/-- The average of affine estimates `b + d p c` over a nonempty finite type is the affine estimate
of the average. -/
theorem average_affine {C : Type} [Fintype C] [Nonempty C] (b d : ℝ≥0∞) (p : C → ℝ≥0∞) :
    (∑ c, (b + d * p c)) / Fintype.card C = b + d * ((∑ c, p c) / Fintype.card C) := by
  have hN : (Fintype.card C : ℝ≥0∞) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, ← Finset.mul_sum, div_eq_mul_inv, add_mul]
  rw [mul_comm (Fintype.card C : ℝ≥0∞) b, mul_assoc b,
    ENNReal.mul_inv_cancel hN (by finiteness), mul_one, mul_assoc]

end Rewinding
