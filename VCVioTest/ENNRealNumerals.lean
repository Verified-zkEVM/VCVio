/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Mathlib.Tactic.Basify
public import Mathlib.Basic.ENNReal.BigOperators
public import Mathlib.Basic.ENNReal.Real
public import Mathlib.Data.Fintype.Card

/-!
# Numeral goals in `ℝ≥0∞`

`norm_num` and `simp` evaluate numeral arithmetic in a field, and `ℝ≥0∞` is not one: a probability
proof that has evaluated its program is left with `2 * (2⁻¹ * 2⁻¹) = 2⁻¹` or `2 / 4 = 2⁻¹`. The
recipe is Mathlib's `basify`, which moves the goal to `ℝ`, followed by `norm_num`. These examples
pin it on the shapes such proofs leave: each relation, nested products of inverses, divisions and
sums of halves, a cast of a natural; the shapes that need a `norm_num` or `simp` first, a power
of a cast and a finite sum, which `basify` treats as an atom; and a canary for the one shape the
current `basify` misreads, a numeral that `Nat.cast_ofNat` produced.
-/

public section

open scoped ENNReal

example : (2 : ℝ≥0∞) * (2⁻¹ * 2⁻¹) = 2⁻¹ := by
  basify
  norm_num

example : (2 : ℝ≥0∞)⁻¹ * 2⁻¹ + 2⁻¹ * 2⁻¹ = 2⁻¹ := by
  basify
  norm_num

example : (2 : ℝ≥0∞) / 4 = 2⁻¹ := by
  basify
  norm_num

example : (1 : ℝ≥0∞) / 2 + 1 / 2 = 1 := by
  basify
  norm_num

example : (3 : ℝ≥0∞) / 6 ≤ 1 / 2 := by
  basify
  norm_num

example : (1 : ℝ≥0∞) / 4 < 1 / 2 := by
  basify
  norm_num

example : (1 : ℝ≥0∞) / 2 ≠ 1 / 3 := by
  basify
  norm_num

example : ((2 : ℕ) : ℝ≥0∞)⁻¹ = 1 / 2 := by
  basify
  norm_num

example (n : ℕ) : (n : ℝ≥0∞) / 2 ≤ n := by
  basify
  norm_num

/-- An infinite side is cleared by `basify` alone. -/
example : (⊤ : ℝ≥0∞) + 1 = ⊤ := by basify

/-- A power of a cast: `norm_num` evaluates the semiring part first. -/
example : ((4 : ℕ) : ℝ≥0∞)⁻¹ * 2 ^ 2 = 1 := by
  norm_num
  basify
  norm_num

/-- A finite sum is an atom for `basify`; `simp` folds it first, and the cast of its
cardinality is an operation `basify` translates. -/
example : ∑ _ ∈ Finset.range 3, (2 : ℝ≥0∞)⁻¹ = 3 / 2 := by
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  basify
  norm_num

/-- A numeral that `Nat.cast_ofNat` produced, by `simp` or by `rw`, carries a `no_index`
annotation, and `basify`'s atom test reads the head of the annotated term, so it generalizes the
numeral instead of translating it. `ring_nf` rebuilds the numeral. The canary fails once `basify`
sees through the annotation, when the detour can go. -/
example : ((Fintype.card Bool : ℕ) : ℝ≥0∞) * (2⁻¹ * 2⁻¹) = 2⁻¹ := by
  simp only [Fintype.card_bool, Nat.cast_ofNat]
  fail_if_success (basify; norm_num; done)
  ring_nf
  basify
  norm_num
