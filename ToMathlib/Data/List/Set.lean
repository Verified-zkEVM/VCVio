/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import Mathlib.Data.List.Basic

/-!
# Replacing a single list entry leaves the rest alone

`List.set` changes one position. These lemmas isolate the two halves that surround it: everything
strictly before the replaced index, and everything strictly after. Together with
`List.getElem?_set_self` they say that `l.set n a` differs from `l` at position `n` and nowhere
else, which is the form a point substitution on a query seed consumes.
-/

@[expose] public section

namespace List

variable {α : Type*}

/-- Replacing an entry does not disturb the entries before it. -/
theorem take_set_self : ∀ (l : List α) (n : ℕ) (a : α), (l.set n a).take n = l.take n
  | [], _, _ => by simp
  | _ :: _, 0, _ => by simp
  | x :: l, n + 1, a => by simp [List.set, take_set_self l n a]

/-- Replacing an entry does not disturb the entries after it. -/
theorem drop_set_self : ∀ (l : List α) (n : ℕ) (a : α), (l.set n a).drop (n + 1) = l.drop (n + 1)
  | [], _, _ => by simp
  | _ :: _, 0, _ => by simp
  | x :: l, n + 1, a => by simp [List.set, drop_set_self l n a]

end List
