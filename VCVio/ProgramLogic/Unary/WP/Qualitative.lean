/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import PolyFun.Control.Monad.Algebra.WP
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

/-- Qualitative `Std.Internal.Do.WP` interpretation of `OracleComp spec` valued in `Prop`.

The `wpTrans` is the existing `Prop`-valued `MAlgOrdered.wp` (i.e.
`∀ x ∈ support oa, post x`); the `EPost.Nil` argument is ignored since
`OracleComp` has no first-class exception slot. The three `WP` axioms
reduce to the existing `MAlgOrdered.{wp_pure, wp_bind, wp_mono}`
specialised at `l := Prop`.

This is a `scoped instance` rather than a normal `instance` because
`Std.Internal.Do.WP`'s `Pred` is an `outParam`; making it scoped means it only
participates in synthesis when the user `open`s this namespace,
sidestepping the conflict with the default `ℝ≥0∞` carrier. -/
noncomputable scoped instance instWP :
    Std.Internal.Do.WPMonad (OracleComp spec) Prop Std.Internal.Do.EPost.Nil :=
  MAlgOrdered.toWPMonad

/-! ## Definitional alignment with `MAlgOrdered.wp` (Prop)

The keystone lemma confirms `Std.Internal.Do.wp` agrees with the `Prop`-valued
`MAlgOrdered.wp` on the nose, so every existing qualitative `wp_*`
theorem in `HoarePropTriple.lean` (and the support-style lemma
`wp_iff_forall_support`) transports for free when the user rewrites
`Std.Internal.Do.wp _ _ _ ↦ MAlgOrdered.wp (l := Prop) _ _`. -/

theorem wp_eq_mAlgOrdered_wp_prop (oa : OracleComp spec α) (post : α → Prop) :
    Std.Internal.Do.wp oa post Lean.Order.bot =
      MAlgOrdered.wp (m := OracleComp spec) (l := Prop) oa post := rfl

end OracleComp.Qualitative
