/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import PolyFun.Control.Monad.Algebra.WP
public import PolyFun.Control.Monad.Support.WP
public import Std.Internal.Do.ExceptPost
public import VCVio.ProgramLogic.Unary.HoarePropTriple

/-!
# Structural weakest preconditions

The qualitative core `WPMonad` interpretation quantifies over every structurally
reachable output of `OracleComp spec`, independently of a probability interpretation.
Enable it with `open scoped OracleComp.Qualitative`.

`wp_eq_mAlgOrdered_wp_prop` identifies this interpretation with the existing support
algebra. Probability-one coherence additionally needs the uniform, finite-support
assumptions stated in `Unary/WP/Coherence.lean`.
-/

@[expose] public section

universe u

open Std.Internal.Do

namespace OracleComp.Qualitative

variable {ι : Type u} {spec : OracleSpec ι}
variable {α β : Type}

/-- Core weakest preconditions for all structurally reachable outputs.
Enable with `open scoped OracleComp.Qualitative`. -/
noncomputable scoped instance instWP :
    Std.Internal.Do.WPMonad (OracleComp spec) Prop Std.Internal.Do.EPost.Nil :=
  MonadAttach.toWPMonadDemonic

/-! ## Agreement with the structural assertion algebra

The direct core WP interpretation and the `Prop`-valued ordered algebra both quantify
over operationally possible outputs. Their public equations relate the two interfaces.
-/

theorem wp_eq_mAlgOrdered_wp_prop (oa : OracleComp spec α) (post : α → Prop) :
    Std.Internal.Do.wp oa post Lean.Order.bot =
      MAlgOrdered.wp (m := OracleComp spec) (l := Prop) oa post := by
  rw [MonadAttach.toWPMonadDemonic_wp]
  exact propext (MonadAttach.wp_iff_allOutputs oa post).symm

/-- Structural weakest preconditions hold precisely on every possible output. -/
theorem wp_iff_forall_support (oa : OracleComp spec α) (post : α → Prop) :
    Std.Internal.Do.wp oa post Lean.Order.bot ↔ ∀ a ∈ support oa, post a := by
  rw [wp_eq_mAlgOrdered_wp_prop]
  exact OracleComp.ProgramLogic.PropLogic.wp_iff_forall_support oa post

end OracleComp.Qualitative
