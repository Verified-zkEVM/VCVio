/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module
public import PolyFun.Control.Monad.Algebra

/-!
# Ordered algebra equations for concrete constructors

Constructor equations let simplification use ordered algebra laws after monad operations have
reduced to their concrete representation.
-/

public section

namespace MAlgOrdered

/-- A successful optional computation evaluates its postcondition. -/
@[simp]
theorem wp_some {l : Type} [CompleteLattice l] [MAlgOrdered Option l]
    {α : Type} (a : α) (post : α → l) : wp (some a) post = post a :=
  wp_pure a post

end MAlgOrdered
