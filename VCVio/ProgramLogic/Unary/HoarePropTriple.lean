/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import PolyFun.Control.Monad.Support.WP
public import VCVio.OracleComp.Support

/-!
# Qualitative `Prop`-valued weakest preconditions for `OracleComp`

The qualitative reading of `OracleComp spec` is PolyFun's demonic support interpretation
`MonadAttach.toWPMonadDemonic`: core's `wp oa post` holds when every structurally possible
output of `oa` satisfies `post`. It needs no probability interpretation. `wp_iff_forall_support`
states it against the support; `OracleComp.Necessary` installs it as a scoped instance, and the
relational `Anchored` instance in `VCVio/ProgramLogic/Relational/Basic.lean` anchors the
coupling logic to it.

This is the qualitative companion of the quantitative `ℝ≥0∞` interpretation in
`VCVio/ProgramLogic/Unary/HoareTriple.lean`. It is a named construction rather than a global
instance: core's weakest-precondition carrier is an output parameter, so a global `Prop`
interpretation would capture every `wp` on `OracleComp`.
-/

@[expose] public section

universe u

open Std.WP

namespace OracleComp.ProgramLogic.PropLogic

variable {ι : Type u} {spec : OracleSpec ι}
variable {α : Type}

/-- Support-based characterization of the qualitative weakest precondition for `OracleComp`. -/
theorem wp_iff_forall_support (oa : OracleComp spec α) (post : α → Prop) :
    (letI := MonadAttach.toWPMonadDemonic (m := OracleComp spec);
      Std.WP.wp oa post Lean.Order.bot) ↔ ∀ x ∈ support oa, post x :=
  Iff.rfl

end OracleComp.ProgramLogic.PropLogic
