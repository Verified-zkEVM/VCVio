/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import ToMathlib.Data.List.GetD
public import Mathlib.Algebra.Order.Ring.Nat

/-!
# Checks for entries of a list at a guessed index

`List.ite_exists_mem_le_sum_getD` at the empty list and `q = 0`, at a list of `q` entries with
one satisfying entry, where both sides are `1`, and without its length hypothesis, where it
fails.
-/

public section

namespace VCVioTest.ListGetD

/-- At the empty list and `q = 0` the indicator is `0`. -/
example : (if ∃ x ∈ ([] : List ℕ), x = 1 then (1 : ℕ) else 0) ≤
    ∑ i : Fin (max 0 1), if ([] : List ℕ).getD i 5 = 1 then 1 else 0 :=
  List.ite_exists_mem_le_sum_getD (R := ℕ) le_rfl _ 5

/-- A list of `q = 3` entries with one entry satisfying `S`. -/
example : (if ∃ x ∈ [0, 1, 2], x = 1 then (1 : ℕ) else 0) ≤
    ∑ i : Fin (max 3 1), if [0, 1, 2].getD i 5 = 1 then 1 else 0 :=
  List.ite_exists_mem_le_sum_getD (R := ℕ) le_rfl _ 5

/-- Both sides of that instance are `1`: exactly one index of `Fin 3` reads the satisfying entry,
so a uniform guess catches it with probability exactly `1 / 3`. -/
example : (∑ i : Fin (max 3 1), if [0, 1, 2].getD i 5 = 1 then (1 : ℕ) else 0) = 1 := by
  decide

/-- The length hypothesis is needed: the only satisfying entry of `[0, 0, 1]` sits at index `2`,
past every index of `Fin (max 2 1)`. -/
example : ¬ ((if ∃ x ∈ [0, 0, 1], x = 1 then (1 : ℕ) else 0) ≤
    ∑ i : Fin (max 2 1), if [0, 0, 1].getD i 5 = 1 then 1 else 0) := by
  decide

end VCVioTest.ListGetD
