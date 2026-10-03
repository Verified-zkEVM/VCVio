/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import PolyFun.Control.Monad.Support.WP
public import VCVio.OracleComp.Support

/-!
# `Prop`-valued weakest preconditions for `OracleComp`

The necessary reading of `OracleComp spec` is PolyFun's demonic support interpretation
`MonadAttach.toWPMonadDemonic`: core's `wp oa post` holds when every possible output of `oa`
satisfies `post`. It needs no probability interpretation. `wp_iff_forall_support` states it
against the support; `OracleComp.Necessary.instWP` installs it as the global instance of
`OracleComp`, and the relational `Anchored` instance in `VCVio/ProgramLogic/Relational/Basic.lean`
anchors the coupling logic to it.

It is the `Prop`-valued companion of the `ℝ≥0∞`-valued expectation interpretation in
`VCVio/ProgramLogic/Unary/HoareTriple.lean`. The lemma below names the construction in its
statement, so it does not depend on the reading that a scope selects.
-/

@[expose] public section

universe u

open Std.WP

namespace OracleComp.ProgramLogic.PropLogic

variable {ι : Type u} {spec : OracleSpec ι}
variable {α : Type}

/-- The necessary weakest precondition holds exactly when every possible output satisfies the
postcondition. -/
theorem wp_iff_forall_support (oa : OracleComp spec α) (post : α → Prop) :
    (letI := MonadAttach.toWPMonadDemonic (m := OracleComp spec);
      Std.WP.wp oa post Lean.Order.bot) ↔ ∀ x ∈ support oa, post x :=
  Iff.rfl

end OracleComp.ProgramLogic.PropLogic
