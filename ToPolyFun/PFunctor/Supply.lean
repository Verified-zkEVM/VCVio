/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import Mathlib.Data.PFunctor.Univariate.Basic
public import ToMathlib.Data.List.Set

/-!
# Positional answer supplies for a polynomial functor

A `Supply P` assigns to each position of a polynomial functor the list of answers to be handed out
there, in order. It is the structural content of a pre-sampled answer tape: a program run against
a supply consumes answers positionally, and falls back on a live source once a position's list is
exhausted.

The operations come in two families. `takeAt` truncates a position's list, so everything past the
cut is *discarded* and a rerun draws fresh answers there. `setAt` instead substitutes a single
answer in place, so a rerun is presented exactly the same supply apart from that one position —
`takeAt_setAt` records that the two agree strictly before the substituted answer, and
`setAt_eq_addValues_drop` factors the substitution through truncate-append-restore, exhibiting the
restored tail as precisely what `takeAt` throws away.

This file depends only on `PFunctor` and is written to be moved upstream into PolyFun unchanged;
`OracleSpec.QuerySeed` is definitionally an instance of it.
-/

@[expose] public section

universe uA uB

namespace PFunctor

/-- A positional answer supply for `P`: for each position, the answers to be handed out there, in
order. -/
def Supply (P : PFunctor.{uA, uB}) : Type max uA uB :=
  (a : P.A) → List (P.B a)

namespace Supply

variable {P : PFunctor.{uA, uB}}

instance : EmptyCollection (Supply P) := ⟨fun _ => []⟩

@[ext]
protected lemma ext {s t : Supply P} (h : ∀ a, s a = t a) : s = t := funext h

@[simp] lemma empty_apply (a : P.A) : (∅ : Supply P) a = [] := rfl

variable [DecidableEq P.A]

/-- Replace the answers at position `a`. -/
def update (s : Supply P) (a : P.A) (xs : List (P.B a)) : Supply P :=
  Function.update s a xs

/-- Keep only the first `n` answers at position `a`, discarding the rest. -/
def takeAt (s : Supply P) (a : P.A) (n : ℕ) : Supply P :=
  Function.update s a ((s a).take n)

/-- Append answers at position `a`. -/
def addValues (s : Supply P) {a : P.A} (us : List (P.B a)) : Supply P :=
  Function.update s a (s a ++ us)

/-- Replace the `n`-th answer at position `a`, leaving every other answer — and every other
position — untouched. An out-of-range `n` leaves the supply unchanged. -/
def setAt (s : Supply P) (a : P.A) (n : ℕ) (u : P.B a) : Supply P :=
  Function.update s a ((s a).set n u)

/-- Consume one answer from position `a`, when there is one. -/
def pop (s : Supply P) (a : P.A) : Option (P.B a × Supply P) :=
  match s a with
  | [] => none
  | u :: us => some (u, Function.update s a us)

/-! ### Basic evaluation -/

@[simp] lemma update_apply_self (s : Supply P) (a : P.A) (xs : List (P.B a)) :
    s.update a xs a = xs := by simp [update]

@[simp] lemma update_apply_of_ne (s : Supply P) (a : P.A) (xs : List (P.B a)) {b : P.A}
    (hb : b ≠ a) : s.update a xs b = s b := by simp [update, Function.update_of_ne hb]

@[simp] lemma takeAt_apply_self (s : Supply P) (a : P.A) (n : ℕ) :
    s.takeAt a n a = (s a).take n := by simp [takeAt]

@[simp] lemma takeAt_apply_of_ne (s : Supply P) (a : P.A) (n : ℕ) {b : P.A} (hb : b ≠ a) :
    s.takeAt a n b = s b := by simp [takeAt, Function.update_of_ne hb]

@[simp] lemma addValues_apply_self (s : Supply P) {a : P.A} (us : List (P.B a)) :
    s.addValues us a = s a ++ us := by simp [addValues]

@[simp] lemma addValues_apply_of_ne (s : Supply P) {a : P.A} (us : List (P.B a)) {b : P.A}
    (hb : b ≠ a) : s.addValues us b = s b := by simp [addValues, Function.update_of_ne hb]

@[simp] lemma setAt_apply_self (s : Supply P) (a : P.A) (n : ℕ) (u : P.B a) :
    s.setAt a n u a = (s a).set n u := by simp [setAt]

@[simp] lemma setAt_apply_of_ne (s : Supply P) (a : P.A) (n : ℕ) (u : P.B a) {b : P.A}
    (hb : b ≠ a) : s.setAt a n u b = s b := by simp [setAt, Function.update_of_ne hb]

lemma length_setAt (s : Supply P) (a : P.A) (n : ℕ) (u : P.B a) :
    (s.setAt a n u a).length = (s a).length := by simp

/-! ### Point substitution -/

/-- Substituting at position `n` does not change the truncation at `n`: the two supplies present
the same answers strictly before the substituted one. -/
@[simp] lemma takeAt_setAt (s : Supply P) (a : P.A) (n : ℕ) (u : P.B a) :
    (s.setAt a n u).takeAt a n = s.takeAt a n := by
  ext b; by_cases hb : b = a
  · subst hb; simp [List.take_set_self]
  · simp [hb]

/-- The substituted position carries the new answer. -/
lemma getElem?_setAt_self (s : Supply P) (a : P.A) {n : ℕ} (u : P.B a)
    (hn : n < (s a).length) : (s.setAt a n u a)[n]? = some u := by
  simpa using List.getElem?_set_self hn

/-- Only the last substitution at a position survives, so the supplies obtained by varying one
answer form a family indexed by the replacement alone. -/
@[simp] lemma setAt_setAt (s : Supply P) (a : P.A) (n : ℕ) (u u' : P.B a) :
    (s.setAt a n u).setAt a n u' = s.setAt a n u' := by
  ext b; by_cases hb : b = a
  · subst hb; simp [List.set_set]
  · simp [hb]

/-- A supply is the member of its own substitution family at its current answer. -/
lemma setAt_getElem_self (s : Supply P) (a : P.A) {n : ℕ} (hn : n < (s a).length) :
    s.setAt a n (s a)[n] = s := by
  ext b; by_cases hb : b = a
  · subst hb; simp [List.set_getElem_self]
  · simp [hb]

/-- Substitution factors through truncate, append, restore. The final `addValues` restores exactly
the tail that `takeAt` discards, which is the difference between substituting an answer and
rewinding to it. -/
lemma setAt_eq_addValues_drop (s : Supply P) (a : P.A) {n : ℕ} (u : P.B a)
    (hn : n < (s a).length) :
    s.setAt a n u = ((s.takeAt a n).addValues [u]).addValues ((s a).drop (n + 1)) := by
  ext b; by_cases hb : b = a
  · subst hb
    simp only [setAt_apply_self, addValues_apply_self, takeAt_apply_self]
    rw [List.set_eq_take_append_cons_drop]
    simp [hn]
  · simp [hb]

end Supply

end PFunctor
