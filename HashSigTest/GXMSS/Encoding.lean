/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import HashSig.GXMSS.Encoding.Basic
public import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FinCases

/-!
# Independently derived encoding convention probes

For length two and radix four, `(0, 3)` and `(1, 2)` both sum to three. Coordinate zero
increases and coordinate one decreases. The distinct pair `(0, 1)` and `(1, 2)` is comparable
and cannot belong to an incomparable code. Empty domains, empty alphabets, singleton alphabets,
and unattainable sums have their ordinary finite-function meanings.
-/

public section

namespace GXMSS.Encoding.Probe

/-- A probe-only sum slice for testing arbitrary radix boundaries. -/
@[expose] def sumSlice (n radix target : ℕ) : Set (Codeword n radix) :=
  {x | ∑ i, (x i).val = target}

theorem mem_sumSlice {n radix target : ℕ} {x : Codeword n radix} :
    x ∈ sumSlice n radix target ↔ ∑ i, (x i).val = target := Iff.rfl

/-- The nontrivial pair has the common target sum three. -/
theorem fixed_sum_pair_mem :
    (![0, 3] : Codeword 2 4) ∈ sumSlice 2 4 3 ∧
    (![1, 2] : Codeword 2 4) ∈ sumSlice 2 4 3 := by
  simp [sumSlice, Fin.sum_univ_two]

/-- Coordinate zero of the first word is strictly smaller: zero is below one. -/
theorem fixed_sum_pair_lt :
    (![0, 3] : Codeword 2 4) 0 < (![1, 2] : Codeword 2 4) 0 := by
  decide

/-- Coordinate one of the second word is strictly smaller: two is below three. -/
theorem fixed_sum_pair_reverse_lt :
    (![1, 2] : Codeword 2 4) 1 < (![0, 3] : Codeword 2 4) 1 := by
  decide

/-- The distinct sum-three words satisfy the direct two-word relation. -/
theorem fixed_sum_pair_incomparable :
    IncomparableWords (![0, 3] : Codeword 2 4) ![1, 2] := by
  apply incomparableWords_of_sum_eq
  · decide
  · simp [Fin.sum_univ_two]

/-- Equal words are not incomparable, even though their singleton code is incomparable. -/
theorem identical_pair_not_incomparable :
    ¬ IncomparableWords (![0, 3] : Codeword 2 4) ![0, 3] := by
  intro h
  obtain ⟨i, hi⟩ := h.1
  exact (lt_irrefl _) hi

/-- The comparable pair is distinct. -/
theorem comparable_pair_ne :
    (![0, 1] : Codeword 2 4) ≠ (![1, 2] : Codeword 2 4) := by
  decide

/-- Every coordinate of the first comparable word is below the second. -/
theorem comparable_pair_le :
    ∀ i, (![0, 1] : Codeword 2 4) i ≤ (![1, 2] : Codeword 2 4) i := by
  decide

/-- The coordinatewise comparable pair fails the direct two-word relation. -/
theorem comparable_pair_not_incomparable :
    ¬ IncomparableWords (![0, 1] : Codeword 2 4) ![1, 2] := by
  intro h
  obtain ⟨j, hj⟩ := h.2
  exact (not_lt_of_ge (comparable_pair_le j)) hj

/-- A set containing this comparable distinct pair fails the global incomparability law. -/
theorem comparable_pair_excluded :
    ¬ IncomparableCode ({![0, 1], ![1, 2]} : Set (Codeword 2 4)) := by
  intro h
  obtain ⟨j, hj⟩ := (h (by simp) (by simp) comparable_pair_ne).2
  exact (not_lt_of_ge (comparable_pair_le j)) hj

/-- An empty word has sum zero, even when its alphabet is empty. -/
theorem zero_length_zero_radix : sumSlice 0 0 0 = Set.univ := by
  ext x
  simp [sumSlice]

/-- No empty word has sum one. -/
theorem zero_length_impossible_sum : sumSlice 0 4 1 = ∅ := by
  ext x
  simp [sumSlice]

/-- A nonempty word cannot have digits in an empty alphabet. -/
theorem zero_radix_empty : sumSlice 1 0 0 = ∅ := by
  ext x
  exact Fin.elim0 (x 0)

/-- With a singleton alphabet, the length-two zero-sum code contains exactly the zero word. -/
theorem singleton_radix_code :
    sumSlice 2 1 0 = {(![0, 0] : Codeword 2 1)} := by
  ext x
  have hx : x = ![0, 0] := Subsingleton.elim _ _
  simp [sumSlice, hx]

/-- At length one, target two selects exactly the digit two. -/
theorem singleton_length_code :
    sumSlice 1 4 2 = {(![2] : Codeword 1 4)} := by
  ext x
  simp only [mem_sumSlice, Fin.sum_univ_one, Set.mem_singleton_iff]
  constructor
  · intro h
    funext i
    fin_cases i
    exact Fin.ext h
  · intro h
    simp [h]

/-- Two radix-four digits sum to at most six, so target seven is impossible. -/
theorem impossible_sum_code : sumSlice 2 4 7 = ∅ := by
  ext x
  simp only [mem_sumSlice, Fin.sum_univ_two, Set.mem_empty_iff_false, iff_false]
  have hzero := (x 0).isLt
  have hone := (x 1).isLt
  omega

end GXMSS.Encoding.Probe
