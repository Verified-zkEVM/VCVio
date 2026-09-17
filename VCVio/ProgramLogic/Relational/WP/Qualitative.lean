/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import ToMathlib.Control.Monad.RelWP
public import VCVio.ProgramLogic.Relational.Basic

/-!
# Qualitative relational weakest preconditions

`OracleComp.Rel.Qualitative` supplies a scoped interpretation of pairs of computations
by `CouplingPost`. This is probabilistic coupling, with the probability assumptions
in each declaration; it is distinct from unary structural reachability.

Use `open scoped OracleComp.Rel.Qualitative` to select this carrier.
-/

@[expose] public section

universe u

open Std.Internal.Do

namespace OracleComp.Rel.Qualitative

variable {ι₁ ι₂ : Type u}
variable {spec₁ : OracleSpec ι₁} {spec₂ : OracleSpec ι₂}
variable [IsUniformSpec spec₁] [IsUniformSpec spec₂]
variable {α β : Type}

/-- Qualitative `VCVio.ProgramLogic.RelWP` interpretation of pairs of `OracleComp`
programs valued in `Prop`.

The `rwpTrans` is the existing `Prop`-valued `MAlgRelOrdered.rwp` (i.e.
`CouplingPost`); the two `EPost.Nil` arguments are ignored since
neither side of an `OracleComp` pair has a first-class exception slot.
The three `RelWP` axioms reduce to the existing
`MAlgRelOrdered.{rwp_pure, rwp_bind_le, rwp_mono}` lemmas specialised
at `l := Prop`.

This is a `scoped instance` rather than a normal `instance` because
`VCVio.ProgramLogic.RelWP`'s `Pred` is an `outParam`; making it scoped means it
only participates in synthesis when the user `open`s this namespace,
sidestepping the conflict with the default `ℝ≥0∞` carrier. -/
noncomputable scoped instance instRelWP :
    VCVio.ProgramLogic.RelWP (OracleComp spec₁) (OracleComp spec₂) Prop
      Std.Internal.Do.EPost.Nil Std.Internal.Do.EPost.Nil where
  rwpTrans oa ob post _epost₁ _epost₂ :=
    OracleComp.ProgramLogic.Relational.CouplingPost oa ob post
  rwp_trans_pure a b post _epost₁ _epost₂ :=
    (MAlgRelOrdered.rwp_pure (m₁ := OracleComp spec₁) (m₂ := OracleComp spec₂) (l := Prop)
      a b post).symm.le
  rwp_trans_bind_le oa ob f g post _epost₁ _epost₂ :=
    MAlgRelOrdered.rwp_bind_le (m₁ := OracleComp spec₁) (m₂ := OracleComp spec₂) (l := Prop)
      oa ob f g post
  rwp_trans_monotone _oa _ob _post _post' _epost₁ _epost₁' _epost₂ _epost₂'
      _h₁ _h₂ hpost :=
    MAlgRelOrdered.rwp_mono (m₁ := OracleComp spec₁) (m₂ := OracleComp spec₂)
      (l := Prop) hpost

/-! ## Definitional alignment with `CouplingPost`

The keystone lemma confirms `VCVio.ProgramLogic.rwp` agrees with `CouplingPost` on
the nose, so every existing pRHL theorem in
`VCVio/ProgramLogic/Relational/Basic.lean` transports for free when the
user rewrites `VCVio.ProgramLogic.rwp _ _ _ _ _ ↦ CouplingPost _ _ _`. -/

theorem rwp_eq_couplingPost (oa : OracleComp spec₁ α) (ob : OracleComp spec₂ β)
    (post : α → β → Prop) :
    VCVio.ProgramLogic.rwp oa ob post Lean.Order.bot Lean.Order.bot =
      OracleComp.ProgramLogic.Relational.CouplingPost oa ob post := rfl

/-- `VCVio.ProgramLogic.RelTriple` agrees with the qualitative `RelTriple`
propositionally. With `pre := True` and the two exception slots set to
`Lean.Order.bot`, the new triple is exactly the existing one. -/
theorem relTriple_iff_relTriple_basic
    (oa : OracleComp spec₁ α) (ob : OracleComp spec₂ β)
    (R : OracleComp.ProgramLogic.Relational.RelPost α β) :
    VCVio.ProgramLogic.RelTriple True oa ob R Lean.Order.bot Lean.Order.bot ↔
      OracleComp.ProgramLogic.Relational.RelTriple oa ob R :=
  Iff.rfl

end OracleComp.Rel.Qualitative
