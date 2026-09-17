/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import ToMathlib.Control.Monad.RelWP
public import VCVio.ProgramLogic.Relational.Quantitative
public import VCVio.ProgramLogic.Unary.WP.Quantitative

/-!
# Quantitative relational weakest preconditions

The local relational WP interface interprets pairs of oracle computations through `eRelWP`.
It shares core's assertion lattices and exception-postcondition types. Its coupling
semantics and asymmetric bind rules belong to VCVio's relational logic.

Enable the quantitative carrier with `open scoped OracleComp.Rel.Quantitative`.
The qualitative and probability-bounded carriers have separate scopes.
-/

@[expose] public section

open VCVio.ProgramLogic
open ENNReal Std.Internal.Do OracleComp.Quantitative

universe u

namespace OracleComp.Rel.Quantitative

variable {ι₁ ι₂ : Type u}
variable {spec₁ : OracleSpec ι₁} {spec₂ : OracleSpec ι₂}
variable [IsUniformSpec spec₁] [IsUniformSpec spec₂]
variable {α β γ δ : Type}

/-- Quantitative `VCVio.ProgramLogic.RelWP` interpretation of pairs of `OracleComp`
programs valued in `ℝ≥0∞`.

The `rwpTrans` is the existing `eRelWP` (the supremum over couplings
of expected values); the two `EPost.Nil` arguments are ignored since
neither side of an `OracleComp` pair has a first-class exception slot.
The three `RelWP` axioms reduce to the existing `eRelWP_pure`,
`eRelWP_bind_le`, `eRelWP_mono` lemmas. -/
noncomputable scoped instance instRelWP :
    VCVio.ProgramLogic.RelWP (OracleComp spec₁) (OracleComp spec₂) ℝ≥0∞
      Std.Internal.Do.EPost.Nil Std.Internal.Do.EPost.Nil where
  rwpTrans oa ob post _epost₁ _epost₂ :=
    OracleComp.ProgramLogic.Relational.eRelWP oa ob post
  rwp_trans_pure a b := by
    intro post _epost₁ _epost₂
    exact OracleComp.ProgramLogic.Relational.eRelWP_pure_le
      (spec₁ := spec₁) (spec₂ := spec₂) a b post
  rwp_trans_bind_le {α β γ δ} oa ob f g := by
    intro post _epost₁ _epost₂
    exact OracleComp.ProgramLogic.Relational.eRelWP_bind_le
      (spec₁ := spec₁) (spec₂ := spec₂) oa ob f g post
  rwp_trans_monotone {α β} oa ob post post' _epost₁ _epost₁' _epost₂ _epost₂' := by
    intro _h₁ _h₂ hpost
    exact OracleComp.ProgramLogic.Relational.eRelWP_mono
      (spec₁ := spec₁) (spec₂ := spec₂) hpost

/-! ## Definitional alignment with `eRelWP`

The keystone lemma confirms `VCVio.ProgramLogic.rwp` agrees with `eRelWP` on the
nose, so every existing eRHL theorem in
`VCVio/ProgramLogic/Relational/Quantitative.lean` transports for free
when the user rewrites `VCVio.ProgramLogic.rwp _ _ _ _ _ ↦ eRelWP _ _ _`. -/

theorem rwp_eq_eRelWP (oa : OracleComp spec₁ α) (ob : OracleComp spec₂ β)
    (post : α → β → ℝ≥0∞) :
    VCVio.ProgramLogic.rwp oa ob post Lean.Order.bot Lean.Order.bot =
      OracleComp.ProgramLogic.Relational.eRelWP oa ob post := rfl

/-- `VCVio.ProgramLogic.RelTriple` agrees with the raw quantitative lower-bound form. -/
theorem relTriple_iff_eRelWP_le
    (pre : ℝ≥0∞) (oa : OracleComp spec₁ α) (ob : OracleComp spec₂ β)
    (post : α → β → ℝ≥0∞) :
    VCVio.ProgramLogic.RelTriple pre oa ob post Lean.Order.bot Lean.Order.bot ↔
      pre ≤ OracleComp.ProgramLogic.Relational.eRelWP oa ob post :=
  Iff.rfl

/-! ## Quantitative `RelTriple` rules -/

/-- Pure rule for the quantitative `VCVio.ProgramLogic.RelTriple` carrier. -/
theorem relTriple_pure (a : α) (b : β) (post : α → β → ℝ≥0∞) :
    VCVio.ProgramLogic.RelTriple (post a b)
      (pure a : OracleComp spec₁ α) (pure b : OracleComp spec₂ β) post
      Lean.Order.bot Lean.Order.bot :=
  OracleComp.ProgramLogic.Relational.eRelWP_pure_le a b post

/-- Consequence rule for the quantitative `VCVio.ProgramLogic.RelTriple` carrier. -/
theorem relTriple_conseq {pre pre' : ℝ≥0∞}
    {oa : OracleComp spec₁ α} {ob : OracleComp spec₂ β}
    {post post' : α → β → ℝ≥0∞}
    (hpre : pre' ≤ pre) (hpost : ∀ a b, post a b ≤ post' a b)
    (h : VCVio.ProgramLogic.RelTriple pre oa ob post Lean.Order.bot Lean.Order.bot) :
    VCVio.ProgramLogic.RelTriple pre' oa ob post' Lean.Order.bot Lean.Order.bot :=
  OracleComp.ProgramLogic.Relational.eRelWP_conseq hpre hpost h

/-- Bind rule for the quantitative `VCVio.ProgramLogic.RelTriple` carrier. -/
theorem relTriple_bind
    {pre : ℝ≥0∞}
    {oa : OracleComp spec₁ α} {ob : OracleComp spec₂ β}
    {fa : α → OracleComp spec₁ γ} {fb : β → OracleComp spec₂ δ}
    {cut : α → β → ℝ≥0∞} {post : γ → δ → ℝ≥0∞}
    (hxy : VCVio.ProgramLogic.RelTriple pre oa ob cut Lean.Order.bot Lean.Order.bot)
    (hfg : ∀ a b, VCVio.ProgramLogic.RelTriple (cut a b) (fa a) (fb b) post
      Lean.Order.bot Lean.Order.bot) :
    VCVio.ProgramLogic.RelTriple pre (oa >>= fa) (ob >>= fb) post
      Lean.Order.bot Lean.Order.bot :=
  OracleComp.ProgramLogic.Relational.eRelWP_bind_rule hxy hfg

/-- Uniform sampling under a bijection for the quantitative
`VCVio.ProgramLogic.RelTriple` carrier. -/
theorem relTriple_uniformSample_bij [SampleableType α]
    {f : α → α} (hf : Function.Bijective f) (post : α → α → ℝ≥0∞)
    {pre : ℝ≥0∞}
    (hpre : pre ≤ ∑' a : α, Pr[= a | ($ᵗ α : ProbComp α)] * post a (f a)) :
    VCVio.ProgramLogic.RelTriple pre ($ᵗ α : ProbComp α) ($ᵗ α : ProbComp α) post
      Lean.Order.bot Lean.Order.bot :=
  OracleComp.ProgramLogic.Relational.eRelWP_uniformSample_bij hf post hpre

/-- Identity coupling for uniform sampling under the quantitative
`VCVio.ProgramLogic.RelTriple` carrier. -/
theorem relTriple_uniformSample_refl [SampleableType α]
    (post : α → α → ℝ≥0∞) :
    VCVio.ProgramLogic.RelTriple
      (∑' a : α, Pr[= a | ($ᵗ α : ProbComp α)] * post a a)
      ($ᵗ α : ProbComp α) ($ᵗ α : ProbComp α) post
      Lean.Order.bot Lean.Order.bot :=
  relTriple_uniformSample_bij Function.bijective_id post le_rfl

/-- Oracle query under a bijection for the quantitative
`VCVio.ProgramLogic.RelTriple` carrier. -/
theorem relTriple_query_bij (t : spec₁.Domain)
    {f : spec₁.Range t → spec₁.Range t}
    (hf : Function.Bijective f)
    (post : spec₁.Range t → spec₁.Range t → ℝ≥0∞)
    {pre : ℝ≥0∞}
    (hpre : pre ≤ ∑' a : spec₁.Range t,
        Pr[= a |
          (liftM (HasQuery.query (spec := spec₁) (m := OracleComp spec₁) t) :
            OracleComp spec₁ (spec₁.Range t))] * post a (f a)) :
    VCVio.ProgramLogic.RelTriple pre
      (liftM (HasQuery.query (spec := spec₁) (m := OracleComp spec₁) t) :
        OracleComp spec₁ (spec₁.Range t))
      (liftM (HasQuery.query (spec := spec₁) (m := OracleComp spec₁) t) :
        OracleComp spec₁ (spec₁.Range t)) post
      Lean.Order.bot Lean.Order.bot :=
  OracleComp.ProgramLogic.Relational.eRelWP_query_bij t hf post hpre

/-- Identity coupling for oracle queries under the quantitative
`VCVio.ProgramLogic.RelTriple` carrier. -/
theorem relTriple_query_refl (t : spec₁.Domain)
    (post : spec₁.Range t → spec₁.Range t → ℝ≥0∞) :
    VCVio.ProgramLogic.RelTriple
      (∑' a : spec₁.Range t,
        Pr[= a |
          (liftM (HasQuery.query (spec := spec₁) (m := OracleComp spec₁) t) :
            OracleComp spec₁ (spec₁.Range t))] * post a a)
      (liftM (HasQuery.query (spec := spec₁) (m := OracleComp spec₁) t) :
        OracleComp spec₁ (spec₁.Range t))
      (liftM (HasQuery.query (spec := spec₁) (m := OracleComp spec₁) t) :
        OracleComp spec₁ (spec₁.Range t)) post
      Lean.Order.bot Lean.Order.bot :=
  relTriple_query_bij t Function.bijective_id post le_rfl

end OracleComp.Rel.Quantitative
