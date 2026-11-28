/-
Copyright (c) 2026 aryaethn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aryaethn
-/
module

public import VCVio.CryptoFoundations.CoordinateFork.BlockTreeFinder
public import Mathlib.Data.Fin.VecNotation

/-!
# Regression checks for the multi-round block finder

`isTreeFinder_blockTreeFinder` is instantiated at values evaluated from its statement, so a change
of the error, of the cost or of the arity breaks a check.

* Two rounds of one coordinate each, over `Fin 5` with threshold `3` and over `Fin 3` with threshold
  `2`. The round errors are `2/5` and `1/3`, so the error of the finder is `1 - (3/5)(2/3) = 3/5`,
  below their sum `11/15`, and its cost is `3 · 2 = 6`.
* One round of two coordinates, over `Fin 3` with threshold `2` and over `Fin 4` with threshold
  `3`. The round branches `1 + 2 + 1 = 4` times, so the sum over the coordinates in the arity is
  read; the error is `1/3 + 2/4 = 5/6` and the cost is `4`.
* One round of one coordinate over `Fin 2` with threshold `4`, whose error `3/2` exceeds one. The
  error of the finder is then `1`, and the contract still holds.
-/

public section

open OracleComp Rewinding

open scoped ENNReal

namespace BlockTreeFinderTest

/-- The alphabet of round `0` is `Fin 5`, that of round `1` is `Fin 3`. -/
abbrev alph : (r : Fin 2) → Fin 1 → Type
  | 0, _ => Fin 5
  | 1, _ => Fin 3

instance : ∀ r i, Fintype (alph r i)
  | 0, _ => inferInstanceAs (Fintype (Fin 5))
  | 1, _ => inferInstanceAs (Fintype (Fin 3))

instance : ∀ r i, DecidableEq (alph r i)
  | 0, _ => inferInstanceAs (DecidableEq (Fin 5))
  | 1, _ => inferInstanceAs (DecidableEq (Fin 3))

instance : ∀ r i, Nonempty (alph r i)
  | 0, _ => inferInstanceAs (Nonempty (Fin 5))
  | 1, _ => inferInstanceAs (Nonempty (Fin 3))

noncomputable instance (r : Fin 2) : SampleableType ((i : Fin 1) → alph r i) :=
  SampleableType.piOfFintype (alph r)

/-- Thresholds `3` and `2`. -/
def k : (r : Fin 2) → Fin 1 → ℕ := fun r _ => ![3, 2] r

theorem card_alph_zero : Fintype.card (alph 0 0) = 5 := by decide

theorem card_alph_one : Fintype.card (alph 1 0) = 3 := by decide

/-- The round errors are `2/5` and `1/3`. -/
theorem blockError_zero : blockError (S := alph 0) (k 0) = 2 / 5 := by
  simp [blockError, k]

theorem blockError_one : blockError (S := alph 1) (k 1) = 1 / 3 := by
  simp [blockError, k]

/-- The error of the finder is `1 - (3/5)(2/3) = 3/5`. -/
theorem blockTreeError_eq : blockTreeError alph k = 3 / 5 := by
  rw [blockTreeError, Fin.prod_univ_two, blockError_zero, blockError_one]
  have h1 : (1 : ℝ≥0∞) - 2 / 5 = 3 / 5 := by
    rw [ENNReal.sub_eq_of_eq_add (by finiteness)]
    rw [ENNReal.div_add_div_same]
    norm_num
    exact (ENNReal.div_self (by norm_num) (by finiteness)).symm
  have h2 : (1 : ℝ≥0∞) - 1 / 3 = 2 / 3 := by
    rw [ENNReal.sub_eq_of_eq_add (by finiteness)]
    rw [ENNReal.div_add_div_same]
    norm_num
    exact (ENNReal.div_self (by norm_num) (by finiteness)).symm
  have h3 : (3 : ℝ≥0∞) / 5 * (2 / 3) = 2 / 5 := by
    rw [← ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness), ENNReal.toReal_mul,
      ENNReal.toReal_div, ENNReal.toReal_div, ENNReal.toReal_div]
    norm_num
  rw [h1, h2, h3, h1]

/-- The contract at these values: error `3/5`, cost `3 · 2 = 6`. -/
example : IsTreeFinder (fun r => blockArity (k r)) (blockNodeOk k)
    (blockTreeFinder 2 (fun _ => Fin 1) alph k) (3 / 5) 6 := by
  have h := isTreeFinder_blockTreeFinder 2 (fun _ => Fin 1) alph k
  have hcost : (∏ r, (blockArity (k r) : ℝ≥0∞)) = 6 := by
    rw [Fin.prod_univ_two]
    simp [blockArity, k]
    norm_num
  rwa [blockTreeError_eq, hcost] at h

/-- The error is below the sum `2/5 + 1/3 = 11/15` of the round errors. -/
example : blockTreeError alph k ≤ 2 / 5 + 1 / 3 := by
  have h := blockTreeError_le_sum alph k
  rwa [Fin.sum_univ_two, blockError_zero, blockError_one] at h

/-! ## One round of two coordinates -/

namespace TwoCoordinates

/-- The alphabet of coordinate `0` is `Fin 3`, that of coordinate `1` is `Fin 4`. -/
abbrev alph : (r : Fin 1) → Fin 2 → Type
  | _, 0 => Fin 3
  | _, 1 => Fin 4

instance : ∀ r i, Fintype (alph r i)
  | _, 0 => inferInstanceAs (Fintype (Fin 3))
  | _, 1 => inferInstanceAs (Fintype (Fin 4))

instance : ∀ r i, DecidableEq (alph r i)
  | _, 0 => inferInstanceAs (DecidableEq (Fin 3))
  | _, 1 => inferInstanceAs (DecidableEq (Fin 4))

instance : ∀ r i, Nonempty (alph r i)
  | _, 0 => inferInstanceAs (Nonempty (Fin 3))
  | _, 1 => inferInstanceAs (Nonempty (Fin 4))

noncomputable instance (r : Fin 1) : SampleableType ((i : Fin 2) → alph r i) :=
  SampleableType.piOfFintype (alph r)

/-- Thresholds `2` and `3`. -/
def k : (r : Fin 1) → Fin 2 → ℕ := fun _ => ![2, 3]

/-- The round branches `1 + 2 + 1 = 4` times. -/
theorem blockArity_k : blockArity (k 0) = 4 := by decide

/-- The round error is `1/3 + 2/4 = 5/6`. -/
theorem blockError_k : blockError (S := alph 0) (k 0) = 5 / 6 := by
  have h3 : Fintype.card (alph 0 0) = 3 := by decide
  have h4 : Fintype.card (alph 0 1) = 4 := by decide
  rw [blockError, Fin.sum_univ_two, h3, h4]
  simp only [k, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [← ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness), ENNReal.toReal_add
    (by finiteness) (by finiteness), ENNReal.toReal_div, ENNReal.toReal_div, ENNReal.toReal_div]
  norm_num

/-- The error of the finder is `1 - (1 - 5/6) = 5/6`. -/
theorem blockTreeError_eq : blockTreeError alph k = 5 / 6 := by
  rw [blockTreeError, Fin.prod_univ_one, blockError_k]
  exact ENNReal.sub_sub_cancel (by finiteness) (ENNReal.div_le_of_le_mul (by norm_num))

/-- The contract at these values: error `5/6`, cost `4`. -/
example : IsTreeFinder (fun r => blockArity (k r)) (blockNodeOk k)
    (blockTreeFinder 1 (fun _ => Fin 2) alph k) (5 / 6) 4 := by
  have h := isTreeFinder_blockTreeFinder 1 (fun _ => Fin 2) alph k
  rwa [blockTreeError_eq, Fin.prod_univ_one, blockArity_k, Nat.cast_ofNat] at h

end TwoCoordinates

/-! ## A round error above one -/

namespace LargeError

/-- One coordinate over `Fin 2`. -/
abbrev alph : (r : Fin 1) → Fin 1 → Type := fun _ _ => Fin 2

noncomputable instance (r : Fin 1) : SampleableType ((i : Fin 1) → alph r i) :=
  SampleableType.piOfFintype (alph r)

/-- Threshold `4`, above the size of the alphabet. -/
def k : (r : Fin 1) → Fin 1 → ℕ := fun _ _ => 4

/-- The round error is `3/2`, above one. -/
theorem one_lt_blockError : 1 < blockError (S := alph 0) (k 0) := by
  simp only [blockError, Finset.univ_unique, Finset.sum_singleton, k, Fintype.card_fin]
  rw [ENNReal.lt_div_iff_mul_lt (by norm_num) (by norm_num)]
  norm_num

/-- The error of the finder is `1`. -/
theorem blockTreeError_eq : blockTreeError alph k = 1 := by
  rw [blockTreeError, Fin.prod_univ_one, tsub_eq_zero_of_le one_lt_blockError.le, tsub_zero]

/-- The contract at error `1` and cost `4`. -/
example : IsTreeFinder (fun r => blockArity (k r)) (blockNodeOk k)
    (blockTreeFinder 1 (fun _ => Fin 1) alph k) 1 4 := by
  have h := isTreeFinder_blockTreeFinder 1 (fun _ => Fin 1) alph k
  rwa [blockTreeError_eq, Fin.prod_univ_one,
    show blockArity (k 0) = 4 by decide, Nat.cast_ofNat] at h

end LargeError

end BlockTreeFinderTest
