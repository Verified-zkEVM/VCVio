/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module
public import Mathlib.Data.Vector.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import ToMathlib.Data.Vector.Count

/-!
# Lemmas about `List.Vector`

Injectivity of `cons`, `getElem` against `get`, `toList` as `ofFn`, and counting the
indices at which a predicate holds.
-/

public section

section List.Vector

open List (Vector)

-- mathlib?
lemma List.injective2_cons {α : Type*} : Function.Injective2 (List.cons (α := α)) := by
  simp [Function.Injective2]

lemma Vector.injective2_cons {α : Type*} {n : ℕ} :
    Function.Injective2 (Vector.cons : α → List.Vector α n → List.Vector α (n + 1)) := by
  simp [Function.Injective2, Vector.eq_cons_iff]

@[simp]
lemma Vector.getElem_eq_get {α n} (xs : List.Vector α n) (i : ℕ) (h : i < n) :
  xs[i]'h = xs.get ⟨i, h⟩ := rfl

lemma List.Vector.toList_eq_ofFn_get {α : Type} {n : ℕ}
    (xs : List.Vector α n) : xs.toList = List.ofFn xs.get := by
  rw [← List.Vector.toList_ofFn, List.Vector.ofFn_get]

end List.Vector

section ListVectorCounting

lemma List.Vector.card_eq_countP {α : Type} {n : ℕ}
    (xs : List.Vector α n) (p : α → Prop) [DecidablePred p] :
    ({i : Fin n | p (xs.get i)} : Finset (Fin n)).card =
      xs.toList.countP (fun a => decide (p a)) := by
  simpa only [decide_eq_true_eq] using (List.Vector.countP_toList (fun a => decide (p a)) xs).symm

lemma List.Vector.card_eq_count {α : Type} [DecidableEq α] {n : ℕ}
    (xs : List.Vector α n) (x : α) :
    ({i : Fin n | x = xs.get i} : Finset (Fin n)).card = xs.toList.count x := by
  simpa only [eq_comm] using (List.Vector.count_toList x xs).symm

end ListVectorCounting
