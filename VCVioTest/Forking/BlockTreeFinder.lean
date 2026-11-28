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

Two rounds of one coordinate each, over `Fin 5` with threshold `3` and over `Fin 3` with threshold
`2`. The round errors are `2/5` and `1/3`, so the error of the finder is `1 - (3/5)(2/3) = 3/5`,
and its cost is `3 · 2 = 6`. `isTreeFinder_blockTreeFinder` is instantiated with these values,
evaluated from its statement, so a change of the error, of the cost or of the arity breaks the
check.
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

theorem blockError_le_one : ∀ r, blockError (S := alph r) (k r) ≤ 1 := by
  intro r
  fin_cases r
  · rw [show ((⟨0, by decide⟩ : Fin 2)) = 0 from rfl, blockError_zero]
    exact ENNReal.div_le_of_le_mul (by norm_num)
  · rw [show ((⟨1, by decide⟩ : Fin 2)) = 1 from rfl, blockError_one]
    exact ENNReal.div_le_of_le_mul (by norm_num)

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
  have h := isTreeFinder_blockTreeFinder 2 (fun _ => Fin 1) alph k blockError_le_one
  have hcost : (∏ r, (blockArity (k r) : ℝ≥0∞)) = 6 := by
    rw [Fin.prod_univ_two]
    simp [blockArity, k]
    norm_num
  rwa [blockTreeError_eq, hcost] at h

end BlockTreeFinderTest
