/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.CryptoFoundations.Rewinding.Finder
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Data.Fintype.BigOperators

/-!
# Finite averages and threshold error

Acceptance rates decompose along the first challenge coordinate. The complement of the threshold
error is multiplicative over rounds, yielding the affine recursion for successive extraction steps.
-/

public section

open scoped ENNReal

namespace Rewinding

/-- The acceptance rate is the average of the Boolean acceptance indicators. -/
theorem acceptRate_eq_sum {R : Type} [Fintype R] [DecidableEq R] {C : R → Type}
    [∀ r, Fintype (C r)] [∀ r, DecidableEq (C r)]
    (f : ((r : R) → C r) → Bool) :
    acceptRate f = (∑ c, if f c then (1 : ℝ≥0∞) else 0) /
      Fintype.card ((r : R) → C r) := by
  rw [acceptRate]
  congr 1
  simp only [← Finset.sum_boole]

/-- Acceptance of a complete vector is the average acceptance rate of its first-coordinate
sections. -/
theorem acceptRate_cons {n : ℕ} {C : Fin (n + 1) → Type}
    [∀ i, Fintype (C i)] [∀ i, DecidableEq (C i)] [∀ i, Nonempty (C i)]
    (f : ((i : Fin (n + 1)) → C i) → Bool) :
    acceptRate f = (∑ c : C 0, acceptRate (fun q => f (Fin.cons c q))) /
      Fintype.card (C 0) := by
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

/-- The union-error identity for two numbers between zero and one. -/
theorem one_sub_mul_one_sub {a b : ℝ≥0∞} (ha : a ≤ 1) (hb : b ≤ 1) :
    1 - (1 - a) * (1 - b) = a + (1 - a) * b := by
  apply ENNReal.sub_eq_of_eq_add' (by finiteness)
  symm
  calc
    _ = a + (1 - a) * (b + (1 - b)) := by ring
    _ = 1 := by rw [add_tsub_cancel_of_le hb, mul_one, add_tsub_cancel_of_le ha]

/-- The complement of the affine union error is the product of the two complements. -/
theorem one_sub_affine_error {a b : ℝ≥0∞} (ha : a ≤ 1) (hb : b ≤ 1) :
    1 - (a + (1 - a) * b) = (1 - a) * (1 - b) := by
  rw [← one_sub_mul_one_sub ha hb]
  apply ENNReal.sub_sub_cancel (by finiteness)
  calc
    _ ≤ (1 : ℝ≥0∞) * 1 :=
      mul_le_mul' (show 1 - a ≤ 1 from tsub_le_self) (show 1 - b ≤ 1 from tsub_le_self)
    _ = 1 := one_mul 1

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
  exact one_sub_mul_one_sub (thresholdError_ratio_le_one hk0 hk)
    (thresholdError_le_one _ _)

/-- Affine success estimates compose with the same multiplicative error complement. -/
theorem affine_error_compose {a b p ε : ℝ≥0∞} (ha : a ≤ 1) (hb : b ≤ 1)
    (h : ε ≤ b + (1 - b) * (a + (1 - a) * p)) :
    ε ≤ (a + (1 - a) * b) + (1 - (a + (1 - a) * b)) * p := by
  apply h.trans_eq
  rw [one_sub_affine_error ha hb, mul_add, ← add_assoc]
  have hab : b + (1 - b) * a = a + (1 - a) * b := by
    rw [← one_sub_mul_one_sub hb ha, mul_comm, one_sub_mul_one_sub ha hb]
  rw [hab]
  ring

end Rewinding
