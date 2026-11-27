/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Mathlib.Algebra.NeZero
public import Mathlib.Data.Nat.Init

/-!
# Nonzero maxima of natural numbers

`max a b` is nonzero when `b` is, so `Fin (max q 1)` is nonempty for every `q`.
-/

public section

/-- `max a b` is nonzero when `b` is, so `Fin (max q 1)` is nonempty for every `q`. -/
instance Nat.neZero_max_right (a b : ℕ) [NeZero b] : NeZero (max a b) :=
  ⟨by have := NeZero.ne b; omega⟩
