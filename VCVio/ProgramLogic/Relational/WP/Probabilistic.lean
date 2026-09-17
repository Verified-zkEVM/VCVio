/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import ToMathlib.Control.Monad.RelWP
public import VCVio.ProgramLogic.Unary.WP.Probabilistic
public import VCVio.ProgramLogic.Relational.Quantitative

/-!
# Probability-bounded relational weakest preconditions

`OracleComp.Rel.Probabilistic` supplies a scoped interpretation of `eRelWP` in
`Prob`, Mathlib's interval `Set.Iic (1 : ℝ≥0∞)`. A coupling expectation of a
probability-valued postcondition stays below one.

Use `open scoped OracleComp.Rel.Probabilistic` to select this carrier.
-/

@[expose] public section

universe u

open VCVio.ProgramLogic
open ENNReal Std.Internal.Do OracleComp.Quantitative

namespace OracleComp.Rel.Probabilistic

variable {ι₁ ι₂ : Type u}
variable {spec₁ : OracleSpec ι₁} {spec₂ : OracleSpec ι₂}
variable [IsUniformSpec spec₁] [IsUniformSpec spec₂]
variable {α β γ δ : Type}

/-! ## Bound: `eRelWP` on a `Prob`-valued post is always `≤ 1`

The relational expectation of a `Prob`-valued postcondition is bounded
by `1`: any coupling has total mass `≤ 1`, and pointwise the
postcondition is `≤ 1`. -/

private lemma eRelWP_le_one_of_post_le_one
    (oa : OracleComp spec₁ α) (ob : OracleComp spec₂ β)
    (post : α → β → ℝ≥0∞) (hpost : ∀ a b, post a b ≤ 1) :
    OracleComp.ProgramLogic.Relational.eRelWP oa ob post ≤ 1 := by
  unfold OracleComp.ProgramLogic.Relational.eRelWP
  refine iSup_le fun c => ?_
  calc ∑' z : α × β, Pr[= z | c.1] * post z.1 z.2
      ≤ ∑' z : α × β, Pr[= z | c.1] :=
        ENNReal.tsum_le_tsum fun z => by simpa using mul_le_mul' le_rfl (hpost z.1 z.2)
    _ ≤ 1 := tsum_probOutput_le_one

/-- The underlying `ℝ≥0∞`-valued relational WP, packaged for use inside
the `Prob` constructor. -/
noncomputable def rwpVal
    (oa : OracleComp spec₁ α) (ob : OracleComp spec₂ β)
    (post : α → β → Prob) : ℝ≥0∞ :=
  OracleComp.ProgramLogic.Relational.eRelWP oa ob (fun a b => (post a b).val)

private theorem rwpVal_le_one (oa : OracleComp spec₁ α) (ob : OracleComp spec₂ β)
    (post : α → β → Prob) : rwpVal oa ob post ≤ 1 :=
  eRelWP_le_one_of_post_le_one oa ob _ (fun a b => (post a b).val_le_one)

/-- Probabilistic `VCVio.ProgramLogic.RelWP` interpretation of pairs of
`OracleComp` programs valued in `Prob = [0, 1] ⊆ ℝ≥0∞`.

The `rwpTrans` is the existing quantitative `eRelWP` evaluated on
`Prob`-valued postconditions and packaged into `Prob` via the `≤ 1`
bound. The two `EPost.Nil` arguments are ignored since neither side of
an `OracleComp` pair has a first-class exception slot.

This is a `scoped instance` rather than a normal `instance`: only one
`VCVio.ProgramLogic.RelWP (OracleComp spec₁) (OracleComp spec₂) _ _ _` instance
can be visible at a time (`Pred` is an `outParam`), and the default is
the quantitative `ℝ≥0∞` carrier. Open `OracleComp.Rel.Probabilistic`
to switch into the probabilistic carrier. -/
noncomputable scoped instance instRelWP_prob :
    VCVio.ProgramLogic.RelWP (OracleComp spec₁) (OracleComp spec₂) Prob
      Std.Internal.Do.EPost.Nil Std.Internal.Do.EPost.Nil where
  rwpTrans oa ob post _epost₁ _epost₂ :=
    ⟨rwpVal oa ob post, by exact rwpVal_le_one oa ob post⟩
  rwp_trans_pure a b := by
    intro post _epost₁ _epost₂
    change (post a b).val ≤ rwpVal (pure a : OracleComp spec₁ _) (pure b : OracleComp spec₂ _) post
    rw [rwpVal, OracleComp.ProgramLogic.Relational.eRelWP_pure]
  rwp_trans_bind_le {α β γ δ} oa ob f g := by
    intro post _epost₁ _epost₂
    change OracleComp.ProgramLogic.Relational.eRelWP oa ob (fun a b =>
      OracleComp.ProgramLogic.Relational.eRelWP (f a) (g b) (fun x y => (post x y).val)) ≤
        OracleComp.ProgramLogic.Relational.eRelWP (oa >>= f) (ob >>= g)
          (fun x y => (post x y).val)
    exact OracleComp.ProgramLogic.Relational.eRelWP_bind_le
      (spec₁ := spec₁) (spec₂ := spec₂) oa ob f g (fun x y => (post x y).val)
  rwp_trans_monotone {α β} oa ob post post' _epost₁ _epost₁' _epost₂ _epost₂' := by
    intro _h₁ _h₂ hpost
    change rwpVal oa ob post ≤ rwpVal oa ob post'
    exact OracleComp.ProgramLogic.Relational.eRelWP_mono
      (spec₁ := spec₁) (spec₂ := spec₂)
      (fun a b => (show (post a b).val ≤ (post' a b).val from hpost a b))

/-! ## Definitional alignment with `eRelWP` (Prob)

The keystone lemma confirms that the underlying `ℝ≥0∞` value of
`VCVio.ProgramLogic.rwp` agrees with the quantitative `eRelWP` on the nose, so
quantitative theorems still apply after coercing through `.val`. -/

theorem rwp_val_eq_eRelWP
    (oa : OracleComp spec₁ α) (ob : OracleComp spec₂ β) (post : α → β → Prob) :
    (VCVio.ProgramLogic.rwp oa ob post Lean.Order.bot Lean.Order.bot).val =
      OracleComp.ProgramLogic.Relational.eRelWP oa ob (fun a b => (post a b).val) := rfl

end OracleComp.Rel.Probabilistic
