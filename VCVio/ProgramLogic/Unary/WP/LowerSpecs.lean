/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import VCVio.ProgramLogic.Unary.HoareTriple
public import VCVio.ProgramLogic.Unary.SimulateQ
public import VCVio.OracleComp.Constructions.SampleableType.Measure
public import VCVio.EvalDist.Monad.Except
public import VCVio.ProgramLogic.Unary.WP.Readback
public import VCVio.OracleComp.Constructions.Replicate

/-!
# `vcgen` rules for the quantitative reading of oracle computations

The expectation interpretation is the scoped core instance of `OracleComp spec`
(`OracleComp.Lower.instWP`, under `open scoped OracleComp.Lower`), so a triple `⦃ r ⦄ oa ⦃ post ⦄`
states the lower bound `r ≤ wp⟦oa⟧ post`. With the indicator postcondition of an event it is a lower
bound on the event: `le_prEvent_iff_triple` states `r ≤ Pr{let x ← oa}[p x]` as `⦃ r ⦄ oa ⦃ predInd
p ⦄`, and `le_wp_iff_triple` reads any lower bound on an expectation, including the nested
expectations of an event's normal form, as a triple.

## Rules

Oracle computations are lossless, so a lower bound that holds for every outcome of a query or a
uniform draw holds in expectation. The registered rules state exactly that, with core's indexed
infimum `Lean.Order.iInf`, which `vcgen` splits into one verification condition per outcome:

* `Spec.query` and `Spec.monadLift_query` (with the global `HasQuery.query` unfold): an oracle
  query;
* `Spec.uniformSample`, `Spec.uniformFin`: uniform draws;
* `Spec.replicate`: a replicated draw, over the lists of possible outputs;
* `Spec.liftComp`, `Spec.monadLift_liftComp`: lifts between specifications with uniform answers.

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

`OracleComp.Lower.Dispatch` registers the expectation reading at a priority above every
reading a file opens, for per-call use (`open scoped OracleComp.Lower.Dispatch in vcgen`).
Upper bounds have their own reading, `OracleComp.Upper` (`VCVio.ProgramLogic.Unary.WP.Upper`).
-/

public section

universe u u'

open ENNReal Std.WP
open scoped OracleComp.Lower

namespace OracleComp.ProgramLogic

variable {ι : Type u} {spec : OracleSpec ι} [OracleSpec.AnswerMeasure spec] {α : Type}

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

/-- A lower bound on an expectation is a core triple of the expectation interpretation of its
monad, for every monad with one. -/
theorem _root_.ExpectationWP.le_wp_iff_triple {m : Type → Type u'} [Monad m] {EPred : Type}
    [Assertion EPred] [ExpectationWP m EPred] {α : Type} (mx : m α) (g : α → ℝ≥0∞) (r : ℝ≥0∞) :
    r ≤ wp⟦mx⟧ g ↔ @Std.WP.Triple ℝ≥0∞ EPred (m α) α _ _ mx
      (@Std.WP.instWPOfWPMonad _ ENNReal _ _ _ _ _ (ExpectationWP.toWPMonad (m := m))) r g
      Lean.Order.bot := by
  let : WPMonad m ℝ≥0∞ EPred := ExpectationWP.toWPMonad (m := m)
  rw [Triple.iff, Lean.Order.rel_eq_le]

/-- Scaling a lower-bound triple by a constant. -/
theorem triple_const_mul {oa : OracleComp spec α} {r : ℝ≥0∞} {g : α → ℝ≥0∞} (c : ℝ≥0∞)
    (h : ⦃ r ⦄ oa ⦃ g ⦄) : ⦃ c * r ⦄ oa ⦃ fun a => c * g a ⦄ := by
  rw [← le_wp_iff_triple] at h ⊢
  rw [ExpectationWP.wp_const_mul]
  exact mul_le_mul_right h c

/-- Adding a constant to a lower-bound triple: the frame rule of the lower-bound reading, for
composing a sub-program's bound with a budget the rest of the program keeps. -/
theorem triple_add_frame {oa : OracleComp spec α} {r : ℝ≥0∞} {g : α → ℝ≥0∞} (c : ℝ≥0∞)
    (h : ⦃ r ⦄ oa ⦃ g ⦄) : ⦃ c + r ⦄ oa ⦃ fun a => c + g a ⦄ := by
  rw [← le_wp_iff_triple] at h ⊢
  rw [ExpectationWP.wp_add, ExpectationWP.wp_const_of_oracle]
  exact add_le_add le_rfl h

/-- A lower bound at every output of a lossless computation bounds its expectation. -/
theorem iInf_le_wp (oa : OracleComp spec α) (g : α → ℝ≥0∞) : ⨅ x, g x ≤ wp⟦oa⟧ g :=
  le_wp_of_forall_le oa (prEvent_true_eq_one oa) fun x => iInf_le g x

end OracleComp.ProgramLogic

namespace OracleComp.Lower

open OracleComp.ProgramLogic

variable {ι : Type u} {spec : OracleSpec ι} [OracleSpec.AnswerMeasure spec] {α : Type}

/-- A lower bound on every answer to a lifted primitive query bounds its expectation. This is
the form `vcgen` reaches from `liftM (OracleSpec.query t)`. -/
@[spec]
theorem Spec.monadLift_query (t : spec.Domain) (post : spec.Range t → ℝ≥0∞)
    {epost : EStack⟨⟩} :
    Triple (MonadLift.monadLift (liftM (OracleSpec.query t) : OracleQuery spec (spec.Range t)) :
      OracleComp spec (spec.Range t)) (Lean.Order.iInf post) post epost := by
  rw [MAlgOrdered.iInf_eq_iInf]
  exact ⟨iInf_le_wp _ post⟩

/-- The rule for the `query t` spelling itself, stated on `OracleComp spec`. It applies where the
program's answer type was elaborated to its reduced form (a concrete specification's `Bool` rather
than `spec.Range t`), on which the generic `HasQuery.instOfMonadLift_query` unfold cannot be
unified: here the specification is fixed by the monad before the answer type is compared. -/
@[spec]
theorem Spec.query (t : spec.Domain) (post : spec.Range t → ℝ≥0∞) {epost : EStack⟨⟩} :
    Triple (query t : OracleComp spec (spec.Range t)) (Lean.Order.iInf post) post epost := by
  rw [HasQuery.instOfMonadLift_query]
  exact Spec.monadLift_query t post

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

/-- A lower bound at every output satisfying a predicate that holds on the support bounds the
expectation: `Spec.ofSupport` with the support replaced by a fact about it, such as the
conclusion of a triple of the necessary reading. Not registered, for the reason given at
`Spec.ofSupport`; `vcgen [Spec.ofNecessary oa q h]` splits the infimum over the outputs
satisfying `q`. -/
theorem Spec.ofNecessary (oa : OracleComp spec α) (q : α → Prop) (h : ∀ a ∈ support oa, q a)
    (post : α → ℝ≥0∞) {epost : EStack⟨⟩} :
    Triple oa (Lean.Order.iInf fun a : {a // q a} => post a.1) post epost := by
  rw [MAlgOrdered.iInf_eq_iInf]
  refine ⟨le_trans (le_of_eq ?_) (wp_mono_of_support oa fun x hx =>
    iInf_le (fun a : {a // q a} => post a.1) ⟨x, h x hx⟩)⟩
  rw [ExpectationWP.wp_const_of_oracle]

/-- `Spec.ofNecessary` for a stateful program: a fact about every value-state pair reachable
from a state, in the form `triple_stateT_iff_forall_support` reads a triple of the necessary
reading, gives the lower bound at every such pair. -/
theorem Spec.ofNecessary_stateT {σ : Type} (mx : StateT σ (OracleComp spec) α)
    (Q : σ → α → σ → Prop) (h : ∀ s, ∀ z ∈ support (mx.run s), Q s z.1 z.2)
    (post : α → σ → ℝ≥0∞) {epost : EStack⟨⟩} :
    Triple mx (fun s => Lean.Order.iInf fun z : {z : α × σ // Q s z.1 z.2} => post z.1.1 z.1.2)
      post epost :=
  ⟨fun s => by
    rw [StateT.wp_apply_eq, MAlgOrdered.iInf_eq_iInf]
    exact le_trans (le_of_eq (ExpectationWP.wp_const_of_oracle _ _).symm)
      (wp_mono_of_support _ fun z hz => iInf_le (fun z : {z : α × σ // Q s z.1 z.2} =>
        post z.1.1 z.1.2) ⟨z, h s z hz⟩)⟩

/-- The expectation of `oa.replicate n` is at least its smallest value on a list of `n` possible
outputs of `oa`. -/
@[spec]
theorem Spec.replicate (n : ℕ) (oa : OracleComp spec α) (post : List α → ℝ≥0∞)
    {epost : EStack⟨⟩} :
    ⦃ Lean.Order.iInf fun xs : {xs : List α // xs.length = n ∧ ∀ x ∈ xs, x ∈ support oa} =>
        post xs.1 ⦄ oa.replicate n ⦃ post; epost ⦄ := by
  rw [MAlgOrdered.iInf_eq_iInf]
  refine ⟨le_trans (le_of_eq ?_) (wp_mono_of_support (oa.replicate n) fun xs hxs =>
    iInf_le (fun xs : {xs : List α // xs.length = n ∧ ∀ x ∈ xs, x ∈ support oa} => post xs.1)
      ⟨xs, by rwa [support_replicate] at hxs⟩)⟩
  rw [ExpectationWP.wp_const_of_oracle]

/-- A lower bound on an expectation over an optional oracle computation is a triple of core's
`OptionT` lift of the lower-bound reading; the reading's bottom charges a failure `0`. Stated as
a lemma, so that `vcgen` sees the stack's own rules without unfolding the lifted expectation. -/
theorem OptionT.le_wp_iff_triple (mx : OptionT (OracleComp spec) α) (g : α → ℝ≥0∞) (r : ℝ≥0∞) :
    r ≤ wp⟦mx⟧ g ↔ ⦃ r ⦄ mx ⦃ g ⦄ := by
  rw [_root_.OptionT.wp_eq_run, Triple.iff]
  simp only [Std.WP.OptionT.wp_apply_eq, Lean.Order.rel_eq_le, ExpectationWP.bot_snd]
  refine Iff.of_eq (congrArg (r ≤ ·) (ExpectationWP.wp_congr _ fun o => ?_))
  cases o <;> simp [Lean.Order.pushOption, ExpectationWP.bot_fst, Lean.Order.bot_apply,
    ExpectationWP.bot_eq_zero]

/-- A lower bound on an expectation over an exceptional oracle computation is a triple of core's
`ExceptT` lift of the lower-bound reading; the reading's bottom charges an exception `0`. -/
theorem ExceptT.le_wp_iff_triple {E : Type} (mx : ExceptT E (OracleComp spec) α) (g : α → ℝ≥0∞)
    (r : ℝ≥0∞) :
    r ≤ wp⟦mx⟧ g ↔ ⦃ r ⦄ mx ⦃ g ⦄ := by
  rw [_root_.ExceptT.wp_eq_run, Triple.iff]
  simp only [Std.WP.ExceptT.wp_apply_eq, Lean.Order.rel_eq_le, ExpectationWP.bot_snd]
  refine Iff.of_eq (congrArg (r ≤ ·) (ExpectationWP.wp_congr _ fun e => ?_))
  cases e <;> simp [Lean.Order.pushExcept, Except.toOption, ExpectationWP.bot_fst,
    Lean.Order.bot_apply, ExpectationWP.bot_eq_zero]

/-- Lifting along a measure-preserving inclusion keeps the expectation. The precondition is the
expectation of the lifted program, so `vcgen` continues into it. -/
@[spec]
theorem Spec.liftComp {τ : Type u'} {superSpec : OracleSpec τ} [OracleSpec.AnswerMeasure superSpec]
    [spec ⊂ₒ superSpec] [OracleSpec.SubSpec.PreservesAnswerMeasure spec superSpec]
    {α : Type} (oa : OracleComp spec α) (post : α → ℝ≥0∞) {epost : EStack⟨⟩} :
    ⦃ wp oa post epost ⦄ liftComp oa superSpec ⦃ post; epost ⦄ :=
  ⟨(OracleComp.ProgramLogic.wp_liftComp oa post).ge⟩

/-- `Spec.liftComp` for the lift written as `liftM oa`. -/
@[spec]
theorem Spec.monadLift_liftComp {τ : Type u'} {superSpec : OracleSpec τ}
    [OracleSpec.AnswerMeasure superSpec] [spec ⊂ₒ superSpec]
    [OracleSpec.SubSpec.PreservesAnswerMeasure spec superSpec]
    {α : Type} (oa : OracleComp spec α) (post : α → ℝ≥0∞) {epost : EStack⟨⟩} :
    ⦃ wp oa post epost ⦄ (MonadLift.monadLift oa : OracleComp superSpec α) ⦃ post; epost ⦄ :=
  Spec.liftComp oa post

/-! The readback of this reading's verification conditions; the sets are registered in
`VCVio.ProgramLogic.Unary.WP.Readback`. -/
attribute [lower_readback] Lean.Order.rel_eq_le binderNameHint Lean.Order.pushOption
  Lean.Order.pushExcept ExpectationWP.bot_fst ExpectationWP.bot_snd Lean.Order.bot_apply
  ExpectationWP.bot_eq_zero predInd_apply one_le_propInd_iff le_refl

end OracleComp.Lower

namespace OracleComp.Lower

variable {ι : Type u} {spec : OracleSpec ι} [OracleSpec.UniformAnswerMeasure spec]

/-- The exact rule for a query with uniform answers: the average of the postcondition over the
answers. Not registered, for the reason given at `Spec.uniformSample_sum`. -/
theorem Spec.query_uniform (t : spec.Domain) [Fintype (spec.Range t)]
    (post : spec.Range t → ℝ≥0∞) {epost : EStack⟨⟩} :
    Triple (HasQuery.query t : OracleComp spec (spec.Range t))
      (∑ u, (Fintype.card (spec.Range t) : ℝ≥0∞)⁻¹ * post u) post epost :=
  ⟨(OracleComp.ProgramLogic.wp_query_uniform t post).ge⟩

end OracleComp.Lower

namespace OracleComp.Lower.Dispatch

variable {ι : Type u} {spec : OracleSpec ι} [OracleSpec.AnswerMeasure spec]

/-- The expectation reading at the priority of a per-call scope, above every reading a file opens:
`open scoped OracleComp.Lower.Dispatch in vcgen`. -/
noncomputable scoped instance (priority := 1200) instWP :
    Std.WP.WPMonad (OracleComp spec) ℝ≥0∞ EStack⟨⟩ :=
  OracleComp.Lower.instWP

/-- The per-call expectation reading as a direct `WP` instance, which outranks direct instances
of other readings. -/
noncomputable scoped instance (priority := 1200) wpInst {α : Type} :
    Std.WP.WP (OracleComp spec α) α ℝ≥0∞ EStack⟨⟩ :=
  (OracleComp.Lower.instWP (spec := spec)).toWP α

end OracleComp.Lower.Dispatch
