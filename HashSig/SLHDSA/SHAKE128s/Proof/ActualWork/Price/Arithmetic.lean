/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module

public import HashSig.SLHDSA.SHAKE128s.Proof.ActualWork.Work.Signing

/-!
# Joint cache and coverage inequalities for SHAKE-128s

The denominator-cleared inequalities combine graph, private-key and FORS contributions using
cache cardinalities and the available joint work.
-/

public section
open scoped ENNReal
namespace SLHDSA.SHAKE128s.Bridge.SharedExperiment.Native

/-- Denominator-cleared ownership includes the rare signer charge on every branch. -/
private theorem complete_charge_reserve_scalar :
  ∀ (a b M S C Nf Z : Nat) (weak : Bool),
    32 * a + 16 * b + 31 * M + 32 * S ≤ Z →
    C ≤ S →
    Nf ≤ Z →
    Z ≤ 16 * 2 ^ 128 →
    (weak = false → Nf ≤ M) →
    2 ^ 39 * (32 * a + 16 * b + 16 * C +
        16 * (if 1 ≤ S then 1 else 0) + 2 * (if 2 ≤ C then 1 else 0)) +
      (25 * 2 ^ 39 + 1) * Nf +
      (16 * 2 ^ 128 * 2 ^ 39) * (if weak then 1 else 0) ≤
    2 ^ 39 * Z +
      32 * (16 * 2 ^ 128 * 2 ^ 39) * (if weak then 1 else 0) := by
  intro a b M S C Nf Z weak hbudget hCS hNfZ hZR hnonweak
  have hsign : 16 * C + 16 * (if 1 ≤ S then 1 else 0) +
      2 * (if 2 ≤ C then 1 else 0) ≤ 32 * S := by
    split_ifs <;> omega
  have hbase : 32 * a + 16 * b + 16 * C +
      16 * (if 1 ≤ S then 1 else 0) + 2 * (if 2 ≤ C then 1 else 0) ≤
      32 * a + 16 * b + 32 * S := by omega
  have hcoef : 25 * 2 ^ 39 + 1 ≤ 31 * 2 ^ 39 := by norm_num
  cases weak with
  | false =>
      have hNfM := hnonweak rfl
      simp only [Bool.false_eq_true, ↓reduceIte, mul_zero, add_zero]
      calc
        _ ≤ 2 ^ 39 * (32 * a + 16 * b + 32 * S) + (31 * 2 ^ 39) * M :=
          Nat.add_le_add (Nat.mul_le_mul_left _ hbase) (Nat.mul_le_mul hcoef hNfM)
        _ = 2 ^ 39 * (32 * a + 16 * b + 31 * M + 32 * S) := by ring
        _ ≤ _ := Nat.mul_le_mul_left _ hbudget
  | true =>
      have hbaseZ : 32 * a + 16 * b + 16 * C +
          16 * (if 1 ≤ S then 1 else 0) + 2 * (if 2 ≤ C then 1 else 0) ≤ Z := by
        omega
      have hNfR : Nf ≤ 16 * 2 ^ 128 := hNfZ.trans hZR
      simp only [↓reduceIte, mul_one]
      calc
        _ ≤ 2 ^ 39 * Z + (31 * 2 ^ 39) * (16 * 2 ^ 128) +
            16 * 2 ^ 128 * 2 ^ 39 :=
          Nat.add_le_add_right
            (Nat.add_le_add (Nat.mul_le_mul_left _ hbaseZ)
              (Nat.mul_le_mul hcoef hNfR)) _
        _ = _ := by ring

/-- The fixed charge expression on finite cache cardinalities obeys the scalar reserve. -/
theorem complete_charge_numeric_bound
    (a b h M S C Nf Z : Nat) (weak : Bool)
    (hbudget : 32 * a + 16 * b + 31 * M + 32 * S ≤ Z)
    (hH : h ≤ Nf + C) (hCS : C ≤ S) (hNfZ : Nf ≤ Z)
    (hZR : Z ≤ 16 * 2 ^ 128) (hnonweak : weak = false → Nf ≤ M) :
    2 * (a : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞) +
      (b : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞) +
      (h : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞) +
      (((if 1 ≤ S then 1 else 0) : Nat) : ℝ≥0∞) /
        ((2 ^ 128 : Nat) : ℝ≥0∞) +
      (Nf : ℝ≥0∞) *
        (((9 * 2 ^ 99 : Nat) : ℝ≥0∞) / ((2 ^ 231 : Nat) : ℝ≥0∞) +
          ((16 * 2 ^ 128 : Nat) : ℝ≥0∞) / ((2 ^ 303 : Nat) : ℝ≥0∞)) +
      (((if 2 ≤ C then 1 else 0) : Nat) : ℝ≥0∞) /
        ((8 * 2 ^ 128 : Nat) : ℝ≥0∞) +
      (((if weak then 1 else 0) : Nat) : ℝ≥0∞) ≤
    (Z : ℝ≥0∞) / ((16 * 2 ^ 128 : Nat) : ℝ≥0∞) +
      32 * (((if weak then 1 else 0) : Nat) : ℝ≥0∞) := by
  have hs := complete_charge_reserve_scalar a b M S C Nf Z weak
    hbudget hCS hNfZ hZR hnonweak
  have hsReal :
      (2 ^ 39 : ℝ) * (32 * a + 16 * b + 16 * C +
          16 * ((if 1 ≤ S then 1 else 0) : Nat) +
          2 * ((if 2 ≤ C then 1 else 0) : Nat)) +
        (25 * 2 ^ 39 + 1) * Nf +
        (16 * 2 ^ 128 * 2 ^ 39) * ((if weak then 1 else 0) : Nat) ≤
      2 ^ 39 * Z +
        32 * (16 * 2 ^ 128 * 2 ^ 39) * ((if weak then 1 else 0) : Nat) := by
    exact_mod_cast hs
  have hHReal : (h : ℝ) ≤ Nf + C := by exact_mod_cast hH
  have hReal :
      2 * (a : ℝ) / ((2 ^ 128 : Nat) : ℝ) +
        (b : ℝ) / ((2 ^ 128 : Nat) : ℝ) +
        (h : ℝ) / ((2 ^ 128 : Nat) : ℝ) +
        (((if 1 ≤ S then 1 else 0) : Nat) : ℝ) / ((2 ^ 128 : Nat) : ℝ) +
        (Nf : ℝ) *
          (((9 * 2 ^ 99 : Nat) : ℝ) / ((2 ^ 231 : Nat) : ℝ) +
            ((16 * 2 ^ 128 : Nat) : ℝ) / ((2 ^ 303 : Nat) : ℝ)) +
        (((if 2 ≤ C then 1 else 0) : Nat) : ℝ) / ((8 * 2 ^ 128 : Nat) : ℝ) +
        (((if weak then 1 else 0) : Nat) : ℝ) ≤
      (Z : ℝ) / ((16 * 2 ^ 128 : Nat) : ℝ) +
        32 * (((if weak then 1 else 0) : Nat) : ℝ) := by
    have h303 := pow_add (2 : Nat) 128 175
    rw [h303]
    split_ifs at hsReal ⊢ <;> norm_num at hsReal ⊢ <;> nlinarith [hHReal]
  split_ifs at hReal ⊢ <;>
    simpa (disch := positivity) only [ENNReal.ofReal_add, ENNReal.ofReal_mul,
      ENNReal.ofReal_div_of_pos, ENNReal.ofReal_natCast, ENNReal.ofReal_ofNat,
      ENNReal.ofReal_one, ENNReal.ofReal_zero, Nat.cast_one, Nat.cast_zero]
      using ENNReal.ofReal_le_ofReal hReal

end SLHDSA.SHAKE128s.Bridge.SharedExperiment.Native
