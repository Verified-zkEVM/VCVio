/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module

public import Batteries.Data.List.Lemmas
public import Mathlib.Data.List.Forall2

/-!
# `List.mapM` in the `Option` monad

`List.mapM f l` with `f : α → Option β` succeeds with `l'` exactly when `f` succeeds at every
entry of `l` with the matching entry of `l'`, and so succeeds at all exactly when `f` succeeds at
every entry of `l`. Entrywise success is the equation `l.map f = l'.map some`.
-/

public section

namespace List

variable {α β : Type*}

/-- `f` sends the entries of `l` to the matching entries of `vs` exactly when `l.map f` is
`vs.map some`. -/
theorem forall₂_apply_eq_some_iff {f : α → Option β} {l : List α} {vs : List β} :
    Forall₂ (fun a b ↦ f a = some b) l vs ↔ l.map f = vs.map some := by
  rw [← forall₂_eq_eq_eq, forall₂_map_left_iff, forall₂_map_right_iff]

end List
