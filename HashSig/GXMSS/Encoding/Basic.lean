/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Fin.Basic

/-!
# Bounded codewords and equal-sum incomparability

The global code law requires distinct codewords to have strict coordinates in both directions.
Equal natural-valued coordinate sums suffice for this property at any length and radix.
-/

public section

namespace GXMSS.Encoding

/-- A word of length `n` whose digits are natural numbers strictly below `radix`. -/
abbrev Codeword (n radix : ℕ) := Fin n → Fin radix

/-- Two words have a strictly smaller coordinate in each direction. -/
@[expose] def IncomparableWords {n radix : ℕ} (x y : Codeword n radix) : Prop :=
  (∃ i, x i < y i) ∧ (∃ j, y j < x j)

/-- Any two distinct members of a single global code have strict coordinates in both directions. -/
@[expose] def IncomparableCode {n radix : ℕ} (C : Set (Codeword n radix)) : Prop :=
  ∀ ⦃x⦄, x ∈ C → ∀ ⦃y⦄, y ∈ C → x ≠ y →
    (∃ i, x i < y i) ∧ (∃ j, y j < x j)

/-- Comparable words with equal natural-valued coordinate sums are equal. -/
theorem eq_of_sum_eq_of_le {n radix : ℕ} {x y : Codeword n radix}
    (hsum : ∑ i, (x i).val = ∑ i, (y i).val)
    (hle : ∀ i, x i ≤ y i) : x = y := by
  have hcoords : ∀ i ∈ Finset.univ, (x i).val = (y i).val :=
    (Finset.sum_eq_sum_iff_of_le fun i _ ↦ show (x i).val ≤ (y i).val from hle i).mp hsum
  funext i
  exact Fin.ext (hcoords i (Finset.mem_univ i))

/-- Distinct words with equal natural-valued digit sums are incomparable. -/
theorem incomparableWords_of_sum_eq {n radix : ℕ} {x y : Codeword n radix}
    (hne : x ≠ y) (hsum : ∑ i, (x i).val = ∑ i, (y i).val) :
    IncomparableWords x y := by
  have strict_coordinate : ∀ {a b : Codeword n radix},
      a ≠ b → (∑ i, (a i).val) = (∑ i, (b i).val) → ∃ i, a i < b i := by
    intro a b hab hsum'
    by_contra h
    have hle : ∀ i, b i ≤ a i := by
      intro i
      exact le_of_not_gt (fun hi ↦ h ⟨i, hi⟩)
    exact hab (eq_of_sum_eq_of_le hsum'.symm hle).symm
  exact ⟨strict_coordinate hne hsum, strict_coordinate hne.symm hsum.symm⟩

end GXMSS.Encoding
