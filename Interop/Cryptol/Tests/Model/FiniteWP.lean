/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

import Interop.Cryptol.Model.Operational
import PolyFun.Control.Monad.ExactWP

/-!
# Exact weakest preconditions for finite executions

The v4.35 exact-WP API describes the total, budgeted runner. Its postcondition
sees either a terminal outcome or an exact residual. Accepting a residual is
a partial-correctness policy and does not establish unbounded termination.
No WP instance is installed for the lazy denotational model.
-/

public section

open Interop.Cryptol Std.WP

example {a : ClosedTy} (fuel : Nat) (state : MachineState a)
    (post : Outcome a ⊕ MachineState a → Prop) :
    wp (pure (state.run fuel) : Id _) post estack⟨⟩ = post (state.run fuel) :=
  ExactWPMonad.wp_pure _ _ _

example {a : ClosedTy} (state : MachineState a) :
    wp (pure (state.run 0) : Id _)
      (Sum.elim (fun _ => False) (fun _ => True)) estack⟨⟩ = True := rfl

example {a : ClosedTy} (state : MachineState a) :
    wp (pure (state.run 0) : Id _)
      (Sum.elim (fun _ => True) (fun _ => False)) estack⟨⟩ = False := rfl
