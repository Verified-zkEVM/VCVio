/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.ZeroLEOne
public import Mathlib.Data.Fintype.Fin
public import Mathlib.Data.Nat.Cast.Defs

/-!
# Entries of a list at a guessed index

A list of at most `q` entries is read through `List.getD` by the indices `Fin (max q 1)`, a
nonempty type even at `q = 0`. If some entry satisfies `S`, some such index reads an entry
satisfying `S`: the indicator that an entry satisfies `S` is at most the number of such indices
(`List.ite_exists_mem_le_sum_getD`). Divided by `max q 1`, this says that a uniformly guessed
index catches a satisfying entry with probability at least `1 / q`.
-/

public section

namespace List

/-- If some entry of a list of length at most `q` satisfies `S`, then some index below `max q 1`
reads an entry satisfying `S`: the indicator that an entry satisfies `S` is at most the number of
indices `i : Fin (max q 1)` at which `l.getD i d` satisfies `S`. -/
theorem ite_exists_mem_le_sum_getD {α R : Type*} [AddCommMonoidWithOne R] [PartialOrder R]
    [IsOrderedAddMonoid R] [ZeroLEOneClass R] {q : ℕ} {l : List α} (hl : l.length ≤ q)
    (S : α → Prop) [DecidablePred S] (d : α) :
    (if ∃ x ∈ l, S x then (1 : R) else 0) ≤
      ∑ i : Fin (max q 1), if S (l.getD i d) then (1 : R) else 0 := by
  have hnonneg : ∀ i : Fin (max q 1), (0 : R) ≤ if S (l.getD i d) then 1 else 0 :=
    fun i ↦ by split_ifs <;> simp
  split_ifs with h
  · obtain ⟨x, hx, hS⟩ := h
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hx
    refine le_of_eq_of_le ?_ (Finset.single_le_sum (fun i _ ↦ hnonneg i)
      (Finset.mem_univ (⟨j, by omega⟩ : Fin (max q 1))))
    simp [List.getElem?_eq_getElem hj, hS]
  · exact Finset.sum_nonneg fun i _ ↦ hnonneg i

end List
