/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import VCVio.ProgramLogic.Unary.HoareTriple
public import VCVio.ProgramLogic.Unary.SimulateQ
public import VCVio.OracleComp.Constructions.SampleableType.Measure

/-!
# `vcgen` rules for the quantitative reading of oracle computations

The expectation interpretation is the global core instance of `OracleComp spec`
(`OracleComp.Quantitative.instWP`), so a triple `⦃ r ⦄ oa ⦃ post ⦄` states the lower bound
`r ≤ wp⟦oa⟧ post`. With the indicator postcondition of an event it is a lower bound on the event:
`le_prEvent_iff_triple` states `r ≤ Pr{let x ← oa}[p x]` as `⦃ r ⦄ oa ⦃ predInd p ⦄`, and
`le_wp_iff_triple` reads any lower bound on an expectation, including the nested expectations of
an event's normal form, as a triple.

## Rules

Oracle computations are lossless, so a lower bound that holds for every outcome of a query or a
uniform draw holds in expectation. The registered rules state exactly that, with core's indexed
infimum `Lean.Order.iInf`, which `vcgen` splits into one verification condition per outcome:

* `Spec.query`, `Spec.monadLift_query`: an oracle query;
* `Spec.uniformSample`: a uniform draw `$ᵗ β`.

These rules establish probability-one events and lower bounds that hold on every path. They lose
the averaging of a fractional event: the exact values of queries and draws are sums, which
`vcgen` does not split, and are computed by `simp` on the normal form of `Pr{…}[…]`
(`wp_monadLift_query_uniform`, `SampleableType.prEvent_uniformSample`).

The remaining rules are applied explicitly rather than registered:

* `Spec.ofSupport` bounds an opaque sub-program on its support; `vcgen [Spec.ofSupport keygen]`
  exposes the support hypothesis in each verification condition.
* `triple_const_mul` scales a lower-bound triple, the quantitative frame rule for composing an
  adversary's success bound with a later draw: `vcgen [triple_const_mul 2⁻¹ hadv]`.
* `Spec.uniformSample_sum` and `Spec.query_uniform` are the exact rules, averages over the
  outcomes; they end `vcgen`'s descent, so they serve for the last draw of a program.

The verification conditions are inequalities in `ℝ≥0∞`; `simp` reads core's order as `≤`
(`Lean.Order.rel_eq_le`) and an indicator reaching `1` as its proposition
(`one_le_propInd_iff`).

`OracleComp.Quantitative.Dispatch` registers the expectation reading at a priority above every
reading a file opens, for per-call use (`open scoped OracleComp.Quantitative.Dispatch in vcgen`).
Upper bounds have their own reading, `OracleComp.Upper` (`VCVio.ProgramLogic.Unary.WP.Upper`).
-/

public section

universe u u'

open ENNReal Std.WP
open scoped OracleComp.Quantitative

namespace OracleComp.ProgramLogic

variable {ι : Type u} {spec : OracleSpec ι} [OracleSpec.IsMeasureSpec spec] {α : Type}

/-- A lower bound on an event is a triple with the event's indicator as postcondition. -/
theorem le_prEvent_iff_triple (oa : OracleComp spec α) (p : α → Prop) (r : ℝ≥0∞) :
    r ≤ Pr{let x ← oa}[p x] ↔ ⦃ r ⦄ oa ⦃ predInd p ⦄ := by
  rw [Triple.iff]
  exact Iff.rfl

/-- A lower bound on an expectation is a triple. -/
theorem le_wp_iff_triple (oa : OracleComp spec α) (g : α → ℝ≥0∞) (r : ℝ≥0∞) :
    r ≤ wp⟦oa⟧ g ↔ ⦃ r ⦄ oa ⦃ g ⦄ := by
  rw [Triple.iff]
  exact Iff.rfl

/-- Scaling a lower-bound triple by a constant. -/
theorem triple_const_mul {oa : OracleComp spec α} {r : ℝ≥0∞} {g : α → ℝ≥0∞} (c : ℝ≥0∞)
    (h : ⦃ r ⦄ oa ⦃ g ⦄) : ⦃ c * r ⦄ oa ⦃ fun a => c * g a ⦄ := by
  rw [← le_wp_iff_triple] at h ⊢
  rw [ExpectationWP.wp_const_mul]
  exact mul_le_mul_right h c

/-- A lower bound at every output of a lossless computation bounds its expectation. -/
theorem iInf_le_wp (oa : OracleComp spec α) (g : α → ℝ≥0∞) : ⨅ x, g x ≤ wp⟦oa⟧ g :=
  le_wp_of_forall_le oa (prEvent_true_eq_one oa) fun x => iInf_le g x

end OracleComp.ProgramLogic

namespace OracleComp.Quantitative

open OracleComp.ProgramLogic

variable {ι : Type u} {spec : OracleSpec ι} [OracleSpec.IsMeasureSpec spec] {α : Type}

/-- A lower bound on every answer to a lifted primitive query bounds its expectation. This is
the form `vcgen` reaches from `liftM (OracleSpec.query t)`. -/
@[spec]
theorem Spec.monadLift_query (t : spec.Domain) (post : spec.Range t → ℝ≥0∞)
    {epost : EStack⟨⟩} :
    Triple (MonadLift.monadLift (liftM (OracleSpec.query t) : OracleQuery spec (spec.Range t)) :
      OracleComp spec (spec.Range t)) (Lean.Order.iInf post) post epost := by
  rw [MAlgOrdered.iInf_eq_iInf]
  exact ⟨iInf_le_wp _ post⟩

/-- A lower bound on every value of a uniform draw bounds its expectation. -/
@[spec]
theorem Spec.uniformSample (β : Type) [SampleableType β] (post : β → ℝ≥0∞)
    {epost : EStack⟨⟩} : Triple ($ᵗ β) (Lean.Order.iInf post) post epost := by
  rw [MAlgOrdered.iInf_eq_iInf]
  exact ⟨iInf_le_wp _ post⟩

/-- A lower bound on every value of a uniform index `$[0..n]` bounds its expectation. -/
@[spec]
theorem Spec.uniformFin (n : ℕ) (post : Fin (n + 1) → ℝ≥0∞) {epost : EStack⟨⟩} :
    ⦃ Lean.Order.iInf post ⦄ ($[0..n]) ⦃ post; epost ⦄ := by
  rw [MAlgOrdered.iInf_eq_iInf]
  exact ⟨iInf_le_wp _ post⟩

/-- The exact rule for a uniform draw from a finite type: the average of the postcondition. Not
registered: `vcgen` does not split the sum, so it serves as the last step of a program. -/
theorem Spec.uniformSample_sum (β : Type) [SampleableType β] [Fintype β] (post : β → ℝ≥0∞)
    {epost : EStack⟨⟩} :
    Triple ($ᵗ β) ((∑ x, post x) / Fintype.card β) post epost :=
  ⟨(SampleableType.wp_uniformSample_eq_sum post).ge⟩

/-- A lower bound on every possible output bounds the expectation. Not registered, since it
applies to every program; `vcgen [Spec.ofSupport oa]` splits the infimum over the support of
`oa`, leaving each verification condition with its support hypothesis. -/
theorem Spec.ofSupport (oa : OracleComp spec α) (post : α → ℝ≥0∞) {epost : EStack⟨⟩} :
    Triple oa (Lean.Order.iInf fun a : {a // a ∈ support oa} => post a.1) post epost := by
  rw [MAlgOrdered.iInf_eq_iInf]
  refine ⟨le_trans (le_of_eq ?_) (wp_mono_of_support oa fun x hx =>
    iInf_le (fun a : {a // a ∈ support oa} => post a.1) ⟨x, hx⟩)⟩
  rw [ExpectationWP.wp_const_of_oracle]

end OracleComp.Quantitative

namespace OracleComp.Quantitative

variable {ι : Type u} {spec : OracleSpec ι} [OracleSpec.IsUniformMeasureSpec spec]

/-- The exact rule for a query with uniform answers: the average of the postcondition over the
answers. Not registered, for the reason given at `Spec.uniformSample_sum`. -/
theorem Spec.query_uniform (t : spec.Domain) [Fintype (spec.Range t)]
    (post : spec.Range t → ℝ≥0∞) {epost : EStack⟨⟩} :
    Triple (HasQuery.query t : OracleComp spec (spec.Range t))
      (∑ u, (Fintype.card (spec.Range t) : ℝ≥0∞)⁻¹ * post u) post epost :=
  ⟨(OracleComp.ProgramLogic.wp_query_uniform t post).ge⟩

/-- Lifting between uniform oracle worlds keeps the expectation. The precondition is the
expectation of the lifted program, so `vcgen` continues into it. -/
@[spec]
theorem Spec.liftComp {τ : Type u'} {superSpec : OracleSpec τ}
    [OracleSpec.IsUniformMeasureSpec superSpec] [spec ⊂ₒ superSpec] [spec ˡ⊂ₒ superSpec]
    {α : Type} (oa : OracleComp spec α) (post : α → ℝ≥0∞) {epost : EStack⟨⟩} :
    ⦃ wp oa post epost ⦄ liftComp oa superSpec ⦃ post; epost ⦄ :=
  ⟨(OracleComp.ProgramLogic.wp_liftComp oa post).ge⟩

/-- `Spec.liftComp` for the lift written as `liftM oa`. -/
@[spec]
theorem Spec.monadLift_liftComp {τ : Type u'} {superSpec : OracleSpec τ}
    [OracleSpec.IsUniformMeasureSpec superSpec] [spec ⊂ₒ superSpec] [spec ˡ⊂ₒ superSpec]
    {α : Type} (oa : OracleComp spec α) (post : α → ℝ≥0∞) {epost : EStack⟨⟩} :
    ⦃ wp oa post epost ⦄ (MonadLift.monadLift oa : OracleComp superSpec α) ⦃ post; epost ⦄ :=
  Spec.liftComp oa post

end OracleComp.Quantitative

namespace OracleComp.Quantitative.Dispatch

variable {ι : Type u} {spec : OracleSpec ι} [OracleSpec.IsMeasureSpec spec]

/-- The expectation reading at the priority of a per-call scope, above every reading a file opens:
`open scoped OracleComp.Quantitative.Dispatch in vcgen`. -/
noncomputable scoped instance (priority := 1200) instWP :
    Std.WP.WPMonad (OracleComp spec) ℝ≥0∞ EStack⟨⟩ :=
  OracleComp.Quantitative.instWP

/-- The per-call expectation reading as a direct `WP` instance, which outranks direct instances
of other readings. -/
noncomputable scoped instance (priority := 1200) wpInst {α : Type} :
    Std.WP.WP (OracleComp spec α) α ℝ≥0∞ EStack⟨⟩ :=
  (OracleComp.Quantitative.instWP (spec := spec)).toWP α

end OracleComp.Quantitative.Dispatch
