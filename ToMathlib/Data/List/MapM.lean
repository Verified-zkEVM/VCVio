/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module

public import Mathlib.Data.List.Forall2

/-!
# `List.mapM` in the `Option` monad

`List.mapM f l` with `f : α → Option β` succeeds with `l'` exactly when `f` succeeds at every
entry of `l` with the matching entry of `l'`, and so succeeds at all exactly when `f` succeeds at
every entry of `l`.
-/

public section

namespace List

variable {α β : Type*}

/-- In the `Option` monad, `l.mapM f` returns `some l'` exactly when `f` sends the entries of `l`
to the matching entries of `l'`. -/
theorem mapM_eq_some_iff_forall₂ {f : α → Option β} :
    ∀ {l : List α} {l' : List β}, l.mapM f = some l' ↔ Forall₂ (fun a b ↦ f a = some b) l l'
  | [], l' => by cases l' <;> simp
  | a :: l, l' => by
    rw [mapM_cons]
    cases l' with
    | nil =>
      simp only [forall₂_nil_right_iff, reduceCtorEq, iff_false]
      cases f a <;> cases l.mapM f <;> simp
    | cons b l' =>
      rw [forall₂_cons, ← mapM_eq_some_iff_forall₂ (l := l)]
      cases f a <;> cases l.mapM f <;> simp

/-- In the `Option` monad, `l.mapM f` succeeds exactly when `f` succeeds at every entry of `l`. -/
theorem isSome_mapM_iff {f : α → Option β} :
    ∀ {l : List α}, (l.mapM f).isSome ↔ ∀ a ∈ l, (f a).isSome
  | [] => by simp
  | a :: l => by
    rw [mapM_cons, forall_mem_cons, ← isSome_mapM_iff (l := l)]
    cases f a <;> cases l.mapM f <;> simp

end List
