/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module
public import Mathlib.Data.Fintype.Fin
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.List.FinRange
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.CharP.Defs
public import Mathlib.Data.Nat.Cast.Basic

/-!
# Counting predicates over lists, `Fin`, and arrays

`List.countP` as a sum over indices, the `Fin` form, and the `Array` corollary.
-/

public section

/-- Summing `1` over list indices that satisfy a predicate is just `countP` applied to `p`. -/
lemma List.countP_eq_sum_fin_ite {α : Type*} (xs : List α) (p : α → Bool) :
    (∑ i : Fin xs.length, if p xs[i] then 1 else 0) = xs.countP p := by
  simpa only [Finset.sum_boole, List.ofFn_getElem, Fin.getElem_fin, Nat.cast_id] using
    (List.countP_ofFn (fun i : Fin xs.length => xs[i.val]) p).symm

lemma List.countP_finRange_getElem {α : Type} (l : List α) (p : α → Bool) :
    (List.finRange l.length).countP (fun i => p l[↑i]) = l.countP p := by
  conv_rhs => rw [← List.map_getElem_finRange l]
  rw [List.countP_map]; rfl

lemma Fin.card_eq_countP_mem {n : ℕ} (s : Finset (Fin n)) :
    s.card = Fin.countP (· ∈ s) := by
  simp [Fin.countP_eq_countP_map_finRange, List.countP_eq_length_filter,
    ← List.toFinset_card_of_nodup ((List.nodup_finRange n).filter _)]

lemma Array.card_eq_countP {α : Type} (as : Array α)
    (p : α → Prop) [DecidablePred p] :
    ({i : Fin as.size | p as[↑i]} : Finset (Fin as.size)).card =
      as.countP (fun a => decide (p a)) := by
  simpa only [← Array.toList_ofFn, Array.ofFn_getElem, Array.countP_toList,
    Fin.getElem_fin, decide_eq_true_eq] using
    (List.countP_ofFn (fun i : Fin as.size => as[i.val]) (fun a => decide (p a))).symm

namespace List

/-- `countP` as a sum of indicators, the form that matches `Finset.card_filter`. -/
theorem countP_eq_sum_map {α : Type*} (l : List α) (p : α → Bool) :
    l.countP p = (l.map fun x => if p x then 1 else 0).sum := by
  induction l with
  | nil => simp
  | cons x xs ih =>
      rw [countP_cons, map_cons, sum_cons, ih]
      cases p x
      · simp
      · simp; omega

end List
