/-
Copyright (c) 2026 aryaethn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aryaethn
-/
module

public import VCVio.CryptoFoundations.CoordinateFork.BlockFinder
public import Mathlib.Data.Fin.VecNotation

/-!
# Regression checks for the block finder

**The contract, pinned.** `isFinder_blockFinder` carries `[SampleableType ((i : ι) → S i)]`, whose
synthesis for a dependent `Pi` type is delicate. The check instantiates it at alphabets of different
sizes, `Fin 5` and `Fin 3`, with thresholds `(3, 2)`, and states the contract with error `11/15` and
cost `4`, both evaluated from the theorem's statement and strictly below the trivial bounds.

**A nonempty good set.** A table with seven accepted challenges, six of them good, checks the
good set that the success probability counts.

The one-alphabet contract is checked in `VCVioTest/Forking/CoordinateFinder.lean`.
-/

public section

open OracleComp Rewinding CoordinateWise

open scoped ENNReal

namespace BlockFinderTest

/-- The first coordinate ranges over `Fin 5`, the second over `Fin 3`. -/
abbrev alph : Fin 2 → Type
  | 0 => Fin 5
  | 1 => Fin 3

instance : ∀ u, DecidableEq (alph u)
  | 0 => inferInstanceAs (DecidableEq (Fin 5))
  | 1 => inferInstanceAs (DecidableEq (Fin 3))

instance : ∀ u, Fintype (alph u)
  | 0 => inferInstanceAs (Fintype (Fin 5))
  | 1 => inferInstanceAs (Fintype (Fin 3))

instance : ∀ u, Nonempty (alph u)
  | 0 => inferInstanceAs (Nonempty (Fin 5))
  | 1 => inferInstanceAs (Nonempty (Fin 3))

noncomputable instance : SampleableType ((u : Fin 2) → alph u) :=
  SampleableType.piOfFintype alph

/-- Thresholds `(3, 2)`. -/
def k : Fin 2 → ℕ := ![3, 2]

/-- The error of thresholds `(3, 2)` over `Fin 5` and `Fin 3` is `2/5 + 1/3 = 11/15`. -/
theorem kappa_eq : (∑ j, ((k j - 1 : ℕ) : ℝ≥0∞) / (Fintype.card (alph j) : ℝ≥0∞)) = 11 / 15 := by
  rw [Fin.sum_univ_two]
  have h5 : Fintype.card (alph 0) = 5 := by decide
  have h3 : Fintype.card (alph 1) = 3 := by decide
  simp only [k, h5, h3, Matrix.cons_val_zero, Matrix.cons_val_one]
  have h1 : ((3 - 1 : ℕ) : ℝ≥0∞) / ((5 : ℕ) : ℝ≥0∞) ≠ ⊤ := ENNReal.div_ne_top (by simp) (by simp)
  have h2 : ((2 - 1 : ℕ) : ℝ≥0∞) / ((3 : ℕ) : ℝ≥0∞) ≠ ⊤ := ENNReal.div_ne_top (by simp) (by simp)
  have h3' : (11 : ℝ≥0∞) / 15 ≠ ⊤ := ENNReal.div_ne_top (by simp) (by simp)
  rw [← ENNReal.toReal_eq_toReal_iff' (ENNReal.add_ne_top.mpr ⟨h1, h2⟩) h3',
    ENNReal.toReal_add h1 h2, ENNReal.toReal_div, ENNReal.toReal_div, ENNReal.toReal_div]
  norm_num

/-- The contract at alphabets of different sizes: error `11/15` and cost `1 + 2 + 1 = 4`, both
evaluated from the statement of `isFinder_blockFinder`. -/
example : IsFinder (fun ρ X => IsBlockSpecialSound k X ∧ ∀ c ∈ X, ρ c = true)
    (blockFinder (S := alph) k) (11 / 15) 4 := by
  have h := isFinder_blockFinder (S := alph) k
  have hcost : (1 + ∑ j, ((k j - 1 : ℕ) : ℝ≥0∞)) = 4 := by
    rw [Fin.sum_univ_two]
    simp only [k, Matrix.cons_val_zero, Matrix.cons_val_one]
    norm_num
  rwa [kappa_eq, hcost] at h

/-- A table with a nonempty good set: it accepts the six challenges with first coordinate below `3`
and second coordinate below `2`, and the challenge `(4, 2)`. The six are good; `(4, 2)` is not,
since its first column holds one accepted challenge and the threshold there is `3`. -/
def ρ (c : (u : Fin 2) → alph u) : Bool :=
  decide (((c 0 : Fin 5).val < 3 ∧ (c 1 : Fin 3).val < 2) ∨
    ((c 0 : Fin 5).val = 4 ∧ (c 1 : Fin 3).val = 2))

example : (Finset.univ.filter fun c : (u : Fin 2) → alph u => ρ c = true).card = 7 := by
  decide +kernel

example : (blockGoodSet k ρ).card = 6 := by
  decide +kernel

end BlockFinderTest
