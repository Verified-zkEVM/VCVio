/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import VCVio.ProgramLogic.Relational.WP.Probabilistic
public import VCVio.ProgramLogic.Relational.WP.Qualitative

/-!
# Coherence of relational assertion carriers

The qualitative coupling, probability-bounded coupling expectation, and quantitative
`eRelWP` interpretations agree under the assumptions in each theorem. Statements use
the underlying semantics so carrier selection remains local to each consumer.
-/

@[expose] public section

universe u

open ENNReal OracleComp.ProgramLogic.Relational

namespace OracleComp.Rel.WP.Coherence

variable {ι₁ ι₂ : Type u}
variable {spec₁ : OracleSpec ι₁} {spec₂ : OracleSpec ι₂}
variable [IsUniformSpec spec₁] [IsUniformSpec spec₂]
variable {α β : Type}

/-! ## Bound: `eRelWP` on an indicator post is always `≤ 1`

The relational expectation of an indicator post is bounded by `1`,
since the indicator itself is `≤ 1` pointwise and any coupling has
total mass `≤ 1`. -/

theorem eRelWP_indicator_le_one
    (oa : OracleComp spec₁ α) (ob : OracleComp spec₂ β) (R : RelPost α β) :
    eRelWP oa ob (RelPost.indicator R) ≤ 1 := by
  unfold eRelWP
  refine iSup_le fun c => ?_
  calc ∑' z : α × β, Pr[= z | c.1] * RelPost.indicator R z.1 z.2
      ≤ ∑' z : α × β, Pr[= z | c.1] * 1 := by
        gcongr with z
        simp only [RelPost.indicator]; split_ifs <;> simp
    _ = ∑' z : α × β, Pr[= z | c.1] := by simp
    _ ≤ 1 := tsum_probOutput_le_one

/-! ## Probabilistic ↔ Quantitative

The probabilistic `VCVio.ProgramLogic.rwp` agrees with the quantitative `eRelWP`
under `Subtype.val`; that statement lives in
`…/WP/Probabilistic.lean` as
`OracleComp.Rel.Probabilistic.rwp_val_eq_eRelWP`. We do not restate it
here because pulling `OracleComp.Rel.Probabilistic.instRelWP_prob`
into scope to talk about `VCVio.ProgramLogic.rwp` requires
`open OracleComp.Rel.Probabilistic`, which then occludes the
qualitative tier discussed below. -/

/-! ## Qualitative ↔ Quantitative (coupling-existence vs total mass)

For an `OracleComp` pair, the support-based `Prop`-valued relational
WP (`CouplingPost`) holds iff the quantitative `eRelWP` on the
indicator post equals `1`. -/

/-- Qualitative ↔ Quantitative coherence: a `Prop`-valued relation
holds along some coupling iff the indicator of that relation has
quantitative `eRelWP` equal to `1`.

This is the relational analogue of
`OracleComp.WP.Coherence.wp_qual_iff_wp_prob_indicator_eq_one` in
the unary file, and it reduces to the existing
`relTriple'_iff_couplingPost` bridge plus the upper bound
`eRelWP_indicator_le_one`. -/
theorem couplingPost_iff_eRelWP_indicator_eq_one
    (oa : OracleComp spec₁ α) (ob : OracleComp spec₂ β) (R : RelPost α β) :
    CouplingPost oa ob R ↔ eRelWP oa ob (RelPost.indicator R) = 1 := by
  constructor
  · intro h
    exact le_antisymm (eRelWP_indicator_le_one oa ob R) (relTriple'_iff_couplingPost.mpr h)
  · exact fun h => relTriple'_iff_couplingPost.mp h.ge

/-- Convenience: rewrites the `couplingPost_iff_eRelWP_indicator_eq_one`
bridge as a `RelTriple'` equivalence. The `RelTriple'` form is the
eRHL-style triple with `pre = 1`. -/
theorem couplingPost_iff_relTriple'
    (oa : OracleComp spec₁ α) (ob : OracleComp spec₂ β) (R : RelPost α β) :
    CouplingPost oa ob R ↔ RelTriple' oa ob R :=
  relTriple'_iff_couplingPost.symm

end OracleComp.Rel.WP.Coherence
