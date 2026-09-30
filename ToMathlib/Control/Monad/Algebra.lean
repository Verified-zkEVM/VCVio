/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import PolyFun.Control.Monad.ExactWP

/-!
# Exact weakest-precondition equations for concrete constructors

Constructor equations let simplification use the exact weakest-precondition laws after monad
operations have reduced to their concrete representation: `simp` rewrites `pure a : Option α` to
`some a` before it reaches the enclosing `wp`.
-/

public section

open Std.Internal.Do

namespace ExactWPMonad

/-- A successful optional computation evaluates its postcondition. -/
@[simp]
theorem wp_some {Pred : Type} {EPred : Type} [Assertion Pred] [Assertion EPred]
    [WPMonad Option Pred EPred] [ExactWPMonad Option Pred EPred]
    {α : Type} (a : α) (post : α → Pred) (epost : EPred) : wp (some a) post epost = post a :=
  wp_pure a post epost

end ExactWPMonad
