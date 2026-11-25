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

**Non-vacuity.** `isFinder_blockFinder` carries `[SampleableType ((i : ι) → S i)]`, whose synthesis
for a dependent `Pi` type is delicate. The checks instantiate it at alphabets of different sizes,
`Fin 5` and `Fin 3`, with thresholds `(3, 2)`: error `2/5 + 1/3` and cost `4`, both strictly below
the trivial bounds.

**A nonempty good set.** A table with seven accepted challenges, six of them good, checks the
good set that the success probability counts.

**The homogeneous case.** With one alphabet and one threshold the contract of the block finder is
the one of `OracleComp.isFinder_coordFinder`: error `2/5` and cost `3` at two coordinates over
`Fin 5` with threshold `2`.
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

/-- The contract at alphabets of different sizes: error `2/5 + 1/3`, cost `1 + 2 + 1`. -/
example : IsFinder (fun ρ X => IsBlockSpecialSound k X ∧ ∀ c ∈ X, ρ c = true)
    (blockFinder (S := alph) k)
    (∑ j, ((k j - 1 : ℕ) : ℝ≥0∞) / (Fintype.card (alph j) : ℝ≥0∞))
    (1 + ∑ j, ((k j - 1 : ℕ) : ℝ≥0∞)) :=
  isFinder_blockFinder k

/-- With one alphabet and one threshold, the contract is the one of the homogeneous finder. -/
theorem isFinder_twoCoordinates :
    IsFinder (fun ρ X => IsBlockSpecialSound (fun _ : Fin 2 => 2) X ∧ ∀ c ∈ X, ρ c = true)
      (blockFinder (ι := Fin 2) (S := fun _ => Fin 5) (fun _ => 2)) (2 / 5) 3 := by
  have h := isFinder_blockFinder (ι := Fin 2) (S := fun _ => Fin 5) (fun _ => 2)
  simp only [Fintype.card_fin, Nat.cast_ofNat, show (2 - 1 : ℕ) = 1 from rfl, Nat.cast_one,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at h
  convert h using 1
  · rw [mul_one_div]
  · norm_num

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

/--
info: 'OracleComp.isFinder_blockFinder' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms OracleComp.isFinder_blockFinder

/--
info: 'OracleComp.runFinder_blockFinder' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms OracleComp.runFinder_blockFinder

/--
info: 'Rewinding.thresholdChildren_eq_blockChildren' depends on axioms: [propext, Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Rewinding.thresholdChildren_eq_blockChildren
