/-
Copyright (c) 2026 aryaethn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aryaethn
-/
module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Fin.VecNotation
public import ToMathlib.Combinatorics.CoordinateWise

/-!
# Regression checks for the counting core with an alphabet per coordinate

The challenge has two coordinates, the first over `Fin 5` and the second over `Fin 3`, with
thresholds `(3, 2)`, so `κ = 2/5 + 1/3 = 11/15`. The acceptance function accepts the challenges
whose first coordinate is below `2`, so every column of the first coordinate holds `2 < 3` accepted
challenges and no challenge is good. The affine bound applies with a nonvacuous error, and the
accepted fraction `2/5` stays below the bound `κ`.
-/

public section

open CoordinateWise
open scoped ENNReal

namespace BlockCoordinateWiseTest

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

/-- Thresholds `(3, 2)`. -/
def k : Fin 2 → ℕ := ![3, 2]

/-- Accept the challenges whose first coordinate is below `2`. -/
def accept (c : (u : Fin 2) → alph u) : Prop := (c 0 : Fin 5).val < 2

instance : DecidablePred accept := fun c => inferInstanceAs (Decidable ((c 0 : Fin 5).val < 2))

/-- Every column of the first coordinate holds two accepted challenges. -/
theorem columnCount_accept_zero : ∀ c, columnCount accept 0 c = 2 := by
  decide +kernel

/-- No challenge is good: the first column holds two accepted challenges, and `k 0 = 3`. -/
theorem no_good : ∀ c : (u : Fin 2) → alph u,
    ¬ (accept c ∧ ∀ j, k j ≤ columnCount accept j c) := fun c h => by
  have h0 := h.2 0
  rw [columnCount_accept_zero] at h0
  simp [k] at h0

/-- Six of the fifteen challenges are accepted. -/
example : (Finset.univ.filter fun c : (u : Fin 2) → alph u => accept c).card = 6 := by
  decide +kernel

/-- The error of this instance is `κ = 2/5 + 1/3 = 11/15`. With the thresholds swapped it would be
`1/5 + 2/3 = 13/15`. -/
example : (∑ j : Fin 2, ((k j - 1 : ℕ) : ℝ≥0∞) / (Fintype.card (alph j) : ℝ≥0∞)) = 11 / 15 := by
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

end BlockCoordinateWiseTest

/--
info: 'CoordinateWise.div_card_filter_le_affine_pi' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CoordinateWise.div_card_filter_le_affine_pi

/--
info: 'CoordinateWise.card_filter_accept_le_affine_pi' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CoordinateWise.card_filter_accept_le_affine_pi
