/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module
public import Mathlib.Init

/-!
# Optional sequencing with absent results

Discarding an absent optional result still makes the whole computation absent.
These constructor equations normalize optional sequencing with `simp` and `grind`.
-/

public section

namespace Option

universe u

variable {α β : Type u}

/-- An absent first computation remains absent when keeping its result. -/
@[simp, grind norm]
lemma none_seqLeft (x : Option β) : (none : Option α) <* x = none := rfl

/-- Keeping the first result requires the second computation to return. -/
@[simp, grind norm]
lemma seqLeft_none (x : Option α) : x <* (none : Option β) = none := by
  cases x <;> rfl

/-- An absent first computation remains absent when keeping the second result. -/
@[simp, grind norm]
lemma none_seqRight (x : Option β) : (none : Option α) *> x = none := rfl

/-- An absent second computation makes the whole optional sequence absent. -/
@[simp, grind norm]
lemma seqRight_none (x : Option α) : x *> (none : Option β) = none := by
  cases x <;> rfl

end Option
