/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import VCVio.ProgramLogic.Unary.SimulateQ
public import VCVio.ProgramLogic.Unary.WP.NecessarySpecs

/-!
# Core `vcgen` rules for the lower reading

Under the lower reading (`open scoped OracleComp.Lower`), a triple `⦃ r ⦄ oa ⦃ post ⦄` states the
lower bound `r ≤ wp oa post` on the expectation of `post`. These `@[spec]` rules let core's
`vcgen` step through the primitives of oracle computations in that reading.

## Exact rules

The registered rules are exact: their precondition is the expectation of the postcondition.

* `Spec.query`, `Spec.monadLift_query`: a query integrates the postcondition against its answer
  measure.
* `Spec.uniformSample`: a uniform draw averages the postcondition, `(∑' x, post x) / Nat.card β`
  (`wp_uniformSample_eq_tsum`); `$[0..n]` reaches the query rule through the unfolding of
  `ProbComp.uniformFin`.
* `Spec.liftComp`, `Spec.monadLift_liftComp`: lifting along an inclusion of uniform specifications
  keeps the expectation, and `vcgen` continues into the lifted program.

An exact rule keeps the value of a fractional event, but `vcgen` does not descend under the
integral or sum it produces: a draw followed by more program leaves the verification condition
`r ≤ ∫⁻ u, wp (rest u) post ∂μ`, whose inner expectations the `wp` equations of
`VCVio.ProgramLogic.Unary.HoareTriple` compute.

## Pointwise rules

A lower bound that holds at every answer holds in expectation, because answer measures are
probability measures. The pointwise rules state that with core's indexed infimum
`Lean.Order.iInf`, which `vcgen` splits into one verification condition per answer, so it descends
through every draw; they lose the averaging of a fractional event and serve for bounds that hold
on every path, such as events of probability one. They are registered, above the exact rules, in
the scope `OracleComp.Lower.Pointwise`: `open scoped OracleComp.Lower.Pointwise in vcgen`.

`Spec.ofSupport` bounds an opaque sub-program on its support. It fits every program, so it is
not registered; `vcgen [Spec.ofSupport keygen]` splits the infimum over the support of `keygen`.
-/

public section

universe u u'

open ENNReal MeasureTheory Std.WP
open scoped OracleComp.Lower

namespace OracleComp.Lower

open OracleComp.ProgramLogic

section exact

variable {ι : Type u} {spec : OracleSpec ι} [OracleSpec.AnswerMeasure spec]

/-- A lifted primitive query integrates the postcondition against its answer measure. This is
the form `vcgen` reaches from `liftM (OracleSpec.query t)`. -/
@[spec]
theorem Spec.monadLift_query (t : spec.Domain) (post : spec.Range t → ℝ≥0∞)
    {epost : EStack⟨⟩} :
    ⦃ ∫⁻ u, post u ∂OracleSpec.AnswerMeasure.toMeasure t ⦄
      (MonadLift.monadLift (liftM (OracleSpec.query t) : OracleQuery spec (spec.Range t)) :
        OracleComp spec (spec.Range t))
    ⦃ post; epost ⦄ :=
  ⟨(wp_liftM_query t post).ge⟩

/-- A query integrates the postcondition against its answer measure. -/
@[spec]
theorem Spec.query (t : spec.Domain) (post : spec.Range t → ℝ≥0∞) {epost : EStack⟨⟩} :
    ⦃ ∫⁻ u, post u ∂OracleSpec.AnswerMeasure.toMeasure t ⦄
      (HasQuery.query t : OracleComp spec (spec.Range t))
    ⦃ post; epost ⦄ :=
  ⟨(wp_HasQuery_query t post).ge⟩

/-- The expectation of a uniform draw is the average of the postcondition. -/
theorem wp_uniformSample_eq_tsum (β : Type) [SampleableType β] (post : β → ℝ≥0∞) :
    OracleComp.ProgramLogic.wp ($ᵗ β) post = (∑' x, post x) / Nat.card β := by
  let : MeasurableSpace β := ⊤
  rw [wp_eq_lintegral _ _ Measurable.of_discrete, SampleableType.evalDist_uniformSample,
    ProbabilityTheory.uniformOn, ProbabilityTheory.cond, Measure.restrict_univ,
    lintegral_smul_measure, lintegral_count, Measure.count_univ, ENat.card_eq_coe_natCard,
    ENNReal.div_eq_inv_mul, smul_eq_mul]
  rfl

/-- A uniform draw averages the postcondition. -/
@[spec]
theorem Spec.uniformSample (β : Type) [SampleableType β] (post : β → ℝ≥0∞)
    {epost : EStack⟨⟩} :
    ⦃ (∑' x, post x) / Nat.card β ⦄ ($ᵗ β) ⦃ post; epost ⦄ :=
  ⟨(wp_uniformSample_eq_tsum β post).ge⟩

end exact

section liftComp

variable {ι : Type u} {spec : OracleSpec ι} {α : Type}
  [OracleSpec.UniformAnswerMeasure spec]
  {τ : Type u'} {superSpec : OracleSpec τ} [OracleSpec.UniformAnswerMeasure superSpec]
  [spec ⊂ₒ superSpec] [spec ˡ⊂ₒ superSpec]

/-- Lifting along an inclusion of uniform specifications keeps the expectation. The precondition
is the expectation of the lifted program, so `vcgen` continues into it. -/
@[spec]
theorem Spec.liftComp (oa : OracleComp spec α) (post : α → ℝ≥0∞) {epost : EStack⟨⟩} :
    ⦃ wp oa post epost ⦄ liftComp oa superSpec ⦃ post; epost ⦄ :=
  ⟨(wp_liftComp (superSpec := superSpec) oa post).ge⟩

/-- `Spec.liftComp` for the lift written as `liftM oa`. -/
@[spec]
theorem Spec.monadLift_liftComp (oa : OracleComp spec α) (post : α → ℝ≥0∞)
    {epost : EStack⟨⟩} :
    ⦃ wp oa post epost ⦄ (MonadLift.monadLift oa : OracleComp superSpec α) ⦃ post; epost ⦄ :=
  Spec.liftComp oa post

end liftComp

section pointwise

variable {ι : Type u} {spec : OracleSpec ι} [OracleSpec.AnswerMeasure spec] {α : Type}

/-- A lower bound at every output bounds the expectation. -/
theorem iInf_le_wp (oa : OracleComp spec α) (post : α → ℝ≥0∞) :
    ⨅ x, post x ≤ OracleComp.ProgramLogic.wp oa post :=
  (wp_const oa _).symm.trans_le (wp_mono oa fun x => iInf_le post x)

/-- A lower bound at every answer of a lifted primitive query bounds its expectation. -/
theorem Spec.monadLift_query_iInf (t : spec.Domain) (post : spec.Range t → ℝ≥0∞)
    {epost : EStack⟨⟩} :
    ⦃ Lean.Order.iInf post ⦄
      (MonadLift.monadLift (liftM (OracleSpec.query t) : OracleQuery spec (spec.Range t)) :
        OracleComp spec (spec.Range t))
    ⦃ post; epost ⦄ := by
  rw [MAlgOrdered.iInf_eq_iInf]
  exact ⟨iInf_le_wp _ post⟩

/-- A lower bound at every answer of a query bounds its expectation. -/
theorem Spec.query_iInf (t : spec.Domain) (post : spec.Range t → ℝ≥0∞) {epost : EStack⟨⟩} :
    ⦃ Lean.Order.iInf post ⦄ (HasQuery.query t : OracleComp spec (spec.Range t))
    ⦃ post; epost ⦄ := by
  rw [MAlgOrdered.iInf_eq_iInf]
  exact ⟨iInf_le_wp _ post⟩

/-- A lower bound at every value of a uniform draw bounds its expectation. -/
theorem Spec.uniformSample_iInf (β : Type) [SampleableType β] (post : β → ℝ≥0∞)
    {epost : EStack⟨⟩} :
    ⦃ Lean.Order.iInf post ⦄ ($ᵗ β) ⦃ post; epost ⦄ := by
  rw [MAlgOrdered.iInf_eq_iInf]
  exact ⟨iInf_le_wp _ post⟩

/-- The expectation of `oa.replicate n` is at least its smallest value on a list of `n` possible
outputs of `oa`. -/
theorem Spec.replicate_iInf (n : ℕ) (oa : OracleComp spec α) (post : List α → ℝ≥0∞)
    {epost : EStack⟨⟩} :
    ⦃ Lean.Order.iInf fun xs : {xs : List α // xs.length = n ∧ ∀ x ∈ xs, x ∈ support oa} =>
        post xs.1 ⦄ oa.replicate n ⦃ post; epost ⦄ := by
  rw [MAlgOrdered.iInf_eq_iInf]
  refine ⟨(wp_const (oa.replicate n) _).symm.trans_le
    (wp_mono_of_support (oa.replicate n) fun xs hxs => ?_)⟩
  exact iInf_le (fun xs : {xs : List α // xs.length = n ∧ ∀ x ∈ xs, x ∈ support oa} =>
    post xs.1) ⟨xs, by rwa [support_replicate] at hxs⟩

/-- A lower bound at every possible output bounds the expectation. Not registered, since it fits
every program; `vcgen [Spec.ofSupport oa]` splits the infimum over the support of `oa`. -/
theorem Spec.ofSupport (oa : OracleComp spec α) (post : α → ℝ≥0∞) {epost : EStack⟨⟩} :
    ⦃ Lean.Order.iInf fun a : {a // a ∈ support oa} => post a.1 ⦄ oa ⦃ post; epost ⦄ := by
  rw [MAlgOrdered.iInf_eq_iInf]
  exact ⟨(wp_const oa _).symm.trans_le (wp_mono_of_support oa fun x hx =>
    iInf_le (fun a : {a // a ∈ support oa} => post a.1) ⟨x, hx⟩)⟩

end pointwise

end OracleComp.Lower

-- The pointwise rules of the lower reading, above its exact rules:
-- `open scoped OracleComp.Lower.Pointwise in vcgen` descends through every draw.
scoped[OracleComp.Lower.Pointwise] attribute [spec high] OracleComp.Lower.Spec.monadLift_query_iInf
  OracleComp.Lower.Spec.query_iInf OracleComp.Lower.Spec.uniformSample_iInf
  OracleComp.Lower.Spec.replicate_iInf
