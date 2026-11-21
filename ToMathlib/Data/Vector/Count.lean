/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module
public import Mathlib.Data.Fintype.Card
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import ToMathlib.Data.List.Count

/-!
# Counting predicates over `Vector`

The number of indices of a core `Vector` at which a predicate holds, and the `count`
specialisation.
-/

public section

section VectorCounting

variable {α : Type}

lemma _root_.Vector.card_eq_countP {n : ℕ}
    (xs : Vector α n) (p : α → Prop) [DecidablePred p] :
    ({i : Fin n | p xs[↑i]} : Finset (Fin n)).card =
      xs.countP (fun a => decide (p a)) := by
  simpa only [← Vector.toList_ofFn, Vector.ofFn_getElem, Vector.countP_toList,
    Fin.getElem_fin, decide_eq_true_eq] using
    (List.countP_ofFn (fun i : Fin n => xs[i.val]) (fun a => decide (p a))).symm

lemma _root_.Vector.card_eq_count [DecidableEq α] {n : ℕ}
    (xs : Vector α n) (x : α) :
    ({i : Fin n | x = xs[↑i]} : Finset (Fin n)).card = xs.count x := by
  simpa only [← Vector.toList_ofFn, Vector.ofFn_getElem, Vector.count_toList,
    Fin.getElem_fin, eq_comm] using
    (List.count_ofFn (fun i : Fin n => xs[i.val]) x).symm

end VectorCounting
