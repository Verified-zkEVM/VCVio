/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import VCVio.ProgramLogic.Unary.WP.LowerSpecs
public import VCVio.OracleComp.Constructions.Replicate
public import VCVio.EvalDist.Monad.Except

/-!
# Upper bounds as core triples

A core triple `⦃ pre ⦄ x ⦃ post ⦄` states `pre ⊑ wp x post epost`. Under the lower-bound reading of
`OracleComp spec` (`OracleComp.Lower`) that is a lower bound, `pre ≤ wp⟦x⟧ post`. The expectation
interpretation is exact, so PolyFun's `ExactWPMonad.dual` is the same interpretation over the order
duals `ℝ≥0∞ᵒᵈ` and `EStack⟨⟩ᵒᵈ`, where `⊑` is `≥`: a triple of that reading states `wp⟦x⟧ post ≤
pre`, an upper bound. `open scoped OracleComp.Upper` selects it, and core's `vcgen` then decomposes
upper bounds with the same `@[spec]` catalogue, transformer rules, and loop invariants as lower
bounds.

## Stating an upper bound

`wp_le_iff_triple` states `wp⟦oa⟧ g ≤ ε` as `⦃ toDual ε ⦄ oa ⦃ fun a => toDual (g a) ⦄`, and
`prEvent_le_iff_triple` states `Pr{let x ← oa}[p x] ≤ ε` on the event's `predInd` normal form.
The normal form of an inline program nests one expectation per draw; `simp only [toDual_wp]`
moves the inner expectations into the reading, where `vcgen` steps through them.

The precondition of an upper-bound triple is written `toDual ε`: core's triple elaborates its
precondition before looking up the interpretation, so a precondition of type `ℝ≥0∞` fixes the
assertion type to `ℝ≥0∞`, for which this scope has no interpretation.

## Rules

The registered rules bound the expectation of a query or a uniform draw by its largest value, with
core's indexed infimum `Lean.Order.iInf` of the dual, which `vcgen` splits into one verification
condition per outcome: `Spec.query` and `Spec.monadLift_query` (with the global `HasQuery.query`
unfold), `Spec.uniformSample`, `Spec.uniformFin`, `Spec.replicate`, and the lifts `Spec.liftComp`
and `Spec.monadLift_liftComp`. They prove events of probability zero and bounds that hold on every
path.

The averaging rules state the exact expectation of a finite uniform draw or a uniform query as a
sum: `Spec.uniformSample_avg`, `Spec.query_avg`, `Spec.monadLift_query_avg`. They are applied
explicitly, as in `vcgen [Spec.uniformSample_avg]`, and override the registered rule for the
program they match. `vcgen` does not split the sum, so the continuation of the draw stays inside
the verification condition, where the exact `wp` laws of `simp` compute it.

`Spec.ofSupport` bounds an opaque sub-program by its largest value on its support.
`triple_add_frame` and `triple_const_mul` add a constant to, or scale, an upper-bound triple.

## Budgets

A bound that accumulates across steps, such as a union bound over the queries of an adversary, is
a potential carried in an invariant: the bad event's indicator plus the budget of the remaining
steps. A loop invariant (`Spec.foldlM_list`, `Spec.forIn_list`) or a ranked handler invariant
(`OracleComp.ProgramLogic.simulateQ_triple_ranked`) turns the union bound into one verification
condition per step, the step's averaging inequality, and an entry condition comparing the initial
budget with `ε`.

## Verification conditions

The verification conditions are entailments `pre ⊑ post a` of the dual carrier. `rel_iff`
reads one as `ofDual (post a) ≤ ofDual pre` in `ℝ≥0∞`, `ofDual_toDual` cancels the
conversions, `ofDual_wp` returns a residual expectation of the dual reading to `wp⟦·⟧`, and
Mathlib's `ofDual_add`, `ofDual_mul`, … carry `ofDual` through arithmetic
written in the dual carrier. Apply these with `simp only` before other simplification: the default
`simp` set distributes `toDual` over arithmetic (`toDual_add`) before it compares the two
sides. `prvcgen` (`VCVio.ProgramLogic.Tactics.PrVCGen`) applies them to the conditions it leaves.

An assertion of this reading has type `ℝ≥0∞ᵒᵈ`. A term elaborated in `ℝ≥0∞` and placed there by
unfolding `OrderDual` (a type ascription `(x : ℝ≥0∞)`) type-checks, but `simp` matches its
subterms against the wrong carrier and leaves such conditions unsimplified: write `toDual x`, or
leave the arithmetic unascribed so that it elaborates in `ℝ≥0∞ᵒᵈ`.

`OracleComp.Upper.Dispatch` registers the same reading at a priority above every reading a file
opens, for per-call use (`open scoped OracleComp.Upper.Dispatch in vcgen`).
-/

public section

universe u u'

open ENNReal Std.WP OrderDual

namespace OracleComp.Upper

variable {ι : Type u} {spec : OracleSpec ι} [OracleSpec.AnswerMeasure spec] {α : Type}

open scoped OracleComp.Lower in
/-- Core weakest preconditions of the expectation over the order duals: a triple states an upper
bound on the expectation. Opening the scope selects it over the global necessary reading. -/
noncomputable scoped instance (priority := 1100) instWP :
    Std.WP.WPMonad (OracleComp spec) ℝ≥0∞ᵒᵈ EStack⟨⟩ᵒᵈ :=
  ExactWPMonad.dual

/-- The upper-bound reading as a direct `WP` instance on programs, at the scope's priority, so
that no direct instance of another scope outranks it while this one is open. -/
noncomputable scoped instance (priority := 1100) wpInst :
    Std.WP.WP (OracleComp spec α) α ℝ≥0∞ᵒᵈ EStack⟨⟩ᵒᵈ :=
  (instWP (spec := spec)).toWP α

/-! ## The interpretation -/

/-- The weakest precondition of the upper-bound reading is the expectation of the postcondition,
read in `ℝ≥0∞`. -/
theorem wp_eq (oa : OracleComp spec α) (post : α → ℝ≥0∞ᵒᵈ) (epost : EStack⟨⟩ᵒᵈ) :
    wp oa post epost = toDual (wp⟦oa⟧ fun a => ofDual (post a)) :=
  rfl

/-- A residual weakest precondition of the upper-bound reading, read in `ℝ≥0∞`, is an
expectation. -/
theorem ofDual_wp (oa : OracleComp spec α) (post : α → ℝ≥0∞ᵒᵈ) (epost : EStack⟨⟩ᵒᵈ) :
    ofDual (wp oa post epost) = wp⟦oa⟧ fun a => ofDual (post a) :=
  rfl

/-- An expectation moved into the upper-bound reading. `simp only [toDual_wp]` turns the nested
expectations of an event's normal form into weakest preconditions that `vcgen` steps through. -/
theorem toDual_wp (oa : OracleComp spec α) (g : α → ℝ≥0∞) :
    toDual (wp⟦oa⟧ g) = wp oa (fun a => toDual (g a)) Lean.Order.bot :=
  rfl

/-- A triple of the upper-bound reading is an upper bound on the expectation. -/
theorem triple_iff (oa : OracleComp spec α) (pre : ℝ≥0∞ᵒᵈ) (post : α → ℝ≥0∞ᵒᵈ)
    (epost : EStack⟨⟩ᵒᵈ) :
    Triple oa pre post epost ↔ wp⟦oa⟧ (fun a => ofDual (post a)) ≤ ofDual pre :=
  Triple.iff

/-- An upper bound on an expectation is a triple of the upper-bound reading. -/
theorem wp_le_iff_triple (oa : OracleComp spec α) (g : α → ℝ≥0∞) (ε : ℝ≥0∞) :
    wp⟦oa⟧ g ≤ ε ↔ ⦃ toDual ε ⦄ oa ⦃ fun a => toDual (g a) ⦄ :=
  (triple_iff oa _ _ _).symm

/-- An upper bound on an event is a triple of the upper-bound reading with the event's indicator
as postcondition. -/
theorem prEvent_le_iff_triple (oa : OracleComp spec α) (p : α → Prop) (ε : ℝ≥0∞) :
    Pr{let x ← oa}[p x] ≤ ε ↔ ⦃ toDual ε ⦄ oa ⦃ fun x => toDual (predInd p x) ⦄ :=
  (triple_iff oa _ _ _).symm


/-! ## Verification conditions -/

/-- The entailment of the dual carrier is the reversed order of `ℝ≥0∞`. -/
theorem rel_iff (a b : ℝ≥0∞ᵒᵈ) : Lean.Order.PartialOrder.rel a b ↔ ofDual b ≤ ofDual a :=
  Iff.rfl

/-- An upper bound on an expectation over an optional oracle computation is a triple of core's
`OptionT` lift of the upper-bound reading, with a failure worth `0`. -/
theorem OptionT.wp_le_iff_triple (mx : OptionT (OracleComp spec) α) (g : α → ℝ≥0∞)
    (ε : ℝ≥0∞) :
    wp⟦mx⟧ g ≤ ε ↔
      ⦃ toDual ε ⦄ mx ⦃ fun a => toDual (g a); (fun _ => toDual 0, Lean.Order.bot) ⦄ := by
  rw [_root_.OptionT.wp_eq_run, Triple.iff]
  simp only [Std.WP.OptionT.wp_apply_eq, rel_iff, ofDual_toDual, ofDual_wp]
  exact Iff.of_eq (congrArg (· ≤ ε) (ExpectationWP.wp_congr _ fun o => by cases o <;> rfl))

/-- An upper bound on an expectation over an exceptional oracle computation is a triple of core's
`ExceptT` lift of the upper-bound reading, with an exception worth `0`. -/
theorem ExceptT.wp_le_iff_triple {E : Type} (mx : ExceptT E (OracleComp spec) α)
    (g : α → ℝ≥0∞) (ε : ℝ≥0∞) :
    wp⟦mx⟧ g ≤ ε ↔
      ⦃ toDual ε ⦄ mx ⦃ fun a => toDual (g a); (fun _ => toDual 0, Lean.Order.bot) ⦄ := by
  rw [_root_.ExceptT.wp_eq_run, Triple.iff]
  simp only [Std.WP.ExceptT.wp_apply_eq, rel_iff, ofDual_toDual, ofDual_wp]
  exact Iff.of_eq (congrArg (· ≤ ε) (ExpectationWP.wp_congr _ fun r => by cases r <;> rfl))

/-- Core's `OptionT` lift of the upper-bound reading, with a failure worth `0`, is the dual of
the expectation over the optional computation. -/
theorem OptionT.wp_eq (mx : OptionT (OracleComp spec) α) (post : α → ℝ≥0∞ᵒᵈ) :
    wp mx post (fun _ => toDual 0, Lean.Order.bot) =
      toDual (wp⟦mx⟧ fun a => ofDual (post a)) := by
  rw [_root_.OptionT.wp_eq_run]
  simp only [Std.WP.OptionT.wp_apply_eq, OracleComp.Upper.wp_eq]
  exact congrArg toDual (ExpectationWP.wp_congr _ fun o => by cases o <;> rfl)

/-- Core's `ExceptT` lift of the upper-bound reading, with an exception worth `0`, is the dual
of the expectation over the exceptional computation. -/
theorem ExceptT.wp_eq {E : Type} (mx : ExceptT E (OracleComp spec) α) (post : α → ℝ≥0∞ᵒᵈ) :
    wp mx post (fun _ => toDual 0, Lean.Order.bot) =
      toDual (wp⟦mx⟧ fun a => ofDual (post a)) := by
  rw [_root_.ExceptT.wp_eq_run]
  simp only [Std.WP.ExceptT.wp_apply_eq, OracleComp.Upper.wp_eq]
  exact congrArg toDual (ExpectationWP.wp_congr _ fun r => by cases r <;> rfl)

/-- Mathlib's order on the dual carrier is the reversed order of `ℝ≥0∞`. -/
theorem le_iff_ofDual (a b : ℝ≥0∞ᵒᵈ) : a ≤ b ↔ ofDual b ≤ ofDual a :=
  Iff.rfl

/-! The readback of this reading's verification conditions; the sets are registered in
`VCVio.ProgramLogic.Unary.WP.Readback`. -/
attribute [upper_readback] rel_iff le_iff_ofDual ofDual_toDual ofDual_wp binderNameHint
  Lean.Order.pushOption Lean.Order.pushExcept predInd_apply propInd_le_one ofDual_add ofDual_mul
  ofDual_div ofDual_inv ofDual_zero ofDual_one ofDual_natCast ofDual_ofNat le_refl

/-- Core's indexed infimum on the dual carrier is the supremum in `ℝ≥0∞`: the largest value. -/
theorem iInf_eq {κ : Type _} (f : κ → ℝ≥0∞ᵒᵈ) :
    Lean.Order.iInf f = toDual (⨆ i, ofDual (f i)) :=
  Lean.Order.PartialOrder.rel_antisymm
    (show (⨆ i, ofDual (f i)) ≤ ofDual (Lean.Order.iInf f) from
      iSup_le fun i => Lean.Order.iInf_le f i)
    (Lean.Order.le_iInf f _ fun i => le_iSup (fun i => ofDual (f i)) i)

/-! ## Rules -/

/-- An expectation is at most the largest value of its observation. -/
theorem wp_le_iSup (oa : OracleComp spec α) (g : α → ℝ≥0∞) : wp⟦oa⟧ g ≤ ⨆ x, g x :=
  OracleComp.ProgramLogic.wp_le_const_of_support oa fun x _ => le_iSup g x

/-- The expectation of a lifted primitive query is at most the value of its largest answer. This
is the form `vcgen` reaches from `liftM (OracleSpec.query t)`. -/
@[spec]
theorem Spec.monadLift_query (t : spec.Domain) (post : spec.Range t → ℝ≥0∞ᵒᵈ)
    {epost : EStack⟨⟩ᵒᵈ} :
    Triple (MonadLift.monadLift (liftM (OracleSpec.query t) : OracleQuery spec (spec.Range t)) :
      OracleComp spec (spec.Range t)) (Lean.Order.iInf post) post epost := by
  rw [triple_iff, iInf_eq, ofDual_toDual]
  exact wp_le_iSup _ _

/-- The rule for the `query t` spelling itself, stated on `OracleComp spec`. It applies where the
program's answer type was elaborated to its reduced form (a concrete specification's `Bool` rather
than `spec.Range t`), on which the generic `HasQuery.instOfMonadLift_query` unfold cannot be
unified: here the specification is fixed by the monad before the answer type is compared. -/
@[spec]
theorem Spec.query (t : spec.Domain) (post : spec.Range t → ℝ≥0∞ᵒᵈ) {epost : EStack⟨⟩ᵒᵈ} :
    Triple (query t : OracleComp spec (spec.Range t)) (Lean.Order.iInf post) post epost := by
  rw [HasQuery.instOfMonadLift_query]
  exact Spec.monadLift_query t post

/-- An opaque sub-program's expectation is at most the largest value on its support. Not
registered, since it applies to every program; `vcgen [Spec.ofSupport oa]` splits the supremum
over the support of `oa`, leaving each verification condition with its support hypothesis. -/
theorem Spec.ofSupport (oa : OracleComp spec α) (post : α → ℝ≥0∞ᵒᵈ) {epost : EStack⟨⟩ᵒᵈ} :
    Triple oa (Lean.Order.iInf fun a : {a // a ∈ support oa} => post a.1) post epost := by
  rw [triple_iff, iInf_eq, ofDual_toDual]
  exact OracleComp.ProgramLogic.wp_le_const_of_support oa fun x hx =>
    le_iSup (fun a : {a // a ∈ support oa} => ofDual (post a.1)) ⟨x, hx⟩

/-- An opaque sub-program's expectation is at most the largest value on the outputs satisfying a
predicate that holds on its support: `Spec.ofSupport` with the support replaced by a fact about
it, such as the conclusion of a triple of the necessary reading. Not registered, for the reason
given at `Spec.ofSupport`; `vcgen [Spec.ofNecessary oa q h]` splits the supremum over the
outputs satisfying `q`. -/
theorem Spec.ofNecessary (oa : OracleComp spec α) (q : α → Prop) (h : ∀ a ∈ support oa, q a)
    (post : α → ℝ≥0∞ᵒᵈ) {epost : EStack⟨⟩ᵒᵈ} :
    Triple oa (Lean.Order.iInf fun a : {a // q a} => post a.1) post epost := by
  rw [triple_iff, iInf_eq, ofDual_toDual]
  exact OracleComp.ProgramLogic.wp_le_const_of_support oa fun x hx =>
    le_iSup (fun a : {a // q a} => ofDual (post a.1)) ⟨x, h x hx⟩

/-- `Spec.ofNecessary` for a stateful program: a fact about every value-state pair reachable
from a state, in the form `triple_stateT_iff_forall_support` reads a triple of the necessary
reading, gives the upper bound at every such pair. -/
theorem Spec.ofNecessary_stateT {σ : Type} (mx : StateT σ (OracleComp spec) α)
    (Q : σ → α → σ → Prop) (h : ∀ s, ∀ z ∈ support (mx.run s), Q s z.1 z.2)
    (post : α → σ → ℝ≥0∞ᵒᵈ) {epost : EStack⟨⟩ᵒᵈ} :
    Triple mx (fun s => Lean.Order.iInf fun z : {z : α × σ // Q s z.1 z.2} => post z.1.1 z.1.2)
      post epost :=
  ⟨fun s => by
    rw [rel_iff, StateT.wp_apply_eq, ofDual_wp, iInf_eq, ofDual_toDual]
    exact OracleComp.ProgramLogic.wp_le_const_of_support _ fun z hz =>
      le_iSup (fun z : {z : α × σ // Q s z.1 z.2} => ofDual (post z.1.1 z.1.2)) ⟨z, h s z hz⟩⟩

/-- An opaque sub-program's expectation, as its own upper bound. Not registered, since it applies
to every program; `vcgen [Spec.ofWp oa]` leaves the expectation of `oa` in the verification
condition, for a hypothesis on it to bound, where `Spec.ofSupport` takes the largest value and
`Spec.uniformSample_avg` needs the finite average. -/
theorem Spec.ofWp (oa : OracleComp spec α) (post : α → ℝ≥0∞ᵒᵈ) {epost : EStack⟨⟩ᵒᵈ} :
    Triple oa (toDual (wp⟦oa⟧ fun a => ofDual (post a))) post epost := by
  rw [triple_iff, ofDual_toDual]

/-- The bad-event rule for a bind: the first draw's bad event is charged in full, and off it,
on the support, every continuation meets the bound. Not registered, since the event is a
proof-side choice: `vcgen [Spec.bind_of_bad mx f bad]`. -/
theorem Spec.bind_of_bad {β : Type} (oa : OracleComp spec α) (f : α → OracleComp spec β)
    (bad : α → Prop)
    {ε : ℝ≥0∞} (post : β → ℝ≥0∞ᵒᵈ) {epost : EStack⟨⟩ᵒᵈ} (hle : ∀ b, ofDual (post b) ≤ 1)
    (hgood : ∀ a ∈ support oa, ¬bad a → Triple (f a) (toDual ε) post epost) :
    Triple (oa >>= f) (toDual (Pr{let a ← oa}[bad a] + ε)) post epost := by
  rw [triple_iff, ofDual_toDual, ExpectationWP.wp_bind]
  refine wp_le_prEvent_add_of_support oa bad _ (fun a ha hbad => ?_) fun a _ => ?_
  · exact (triple_iff _ _ _ _).1 (hgood a ha hbad) |>.trans_eq (ofDual_toDual _)
  · calc wp⟦f a⟧ (fun b => ofDual (post b)) ≤ wp⟦f a⟧ (fun _ => 1) := ExpectationWP.wp_mono _ hle
      _ ≤ 1 := by
        rw [wp_const]
        exact mul_le_of_le_one_right' (prEvent_le_one _)

/-- The expectation of `oa.replicate n` is at most its largest value on a list of `n` possible
outputs of `oa`. -/
@[spec]
theorem Spec.replicate (n : ℕ) (oa : OracleComp spec α) (post : List α → ℝ≥0∞ᵒᵈ)
    {epost : EStack⟨⟩ᵒᵈ} :
    ⦃ Lean.Order.iInf fun xs : {xs : List α // xs.length = n ∧ ∀ x ∈ xs, x ∈ support oa} =>
        post xs.1 ⦄ oa.replicate n ⦃ post; epost ⦄ := by
  rw [triple_iff, iInf_eq, ofDual_toDual]
  refine OracleComp.ProgramLogic.wp_le_const_of_support (oa.replicate n) fun xs hxs => ?_
  rw [support_replicate] at hxs
  exact le_iSup (fun xs : {xs : List α // xs.length = n ∧ ∀ x ∈ xs, x ∈ support oa} =>
    ofDual (post xs.1)) ⟨xs, hxs⟩

/-- Adding a constant to an upper-bound triple: the frame rule of the upper-bound reading, for
composing a sub-program's bound with a budget that the rest of the program spends. -/
theorem triple_add_frame {oa : OracleComp spec α} {ε : ℝ≥0∞} {post : α → ℝ≥0∞ᵒᵈ} (c : ℝ≥0∞)
    (h : ⦃ toDual ε ⦄ oa ⦃ post ⦄) :
    ⦃ toDual (c + ε) ⦄ oa ⦃ fun a => toDual (c + ofDual (post a)) ⦄ := by
  rw [triple_iff] at h ⊢
  simp only [ofDual_toDual] at h ⊢
  rw [ExpectationWP.wp_add]
  exact add_le_add (OracleComp.ProgramLogic.wp_le_const_of_support oa fun _ _ => le_rfl) h

/-- Lifting along a measure-preserving inclusion keeps the expectation. The precondition is the
upper-bound weakest precondition of the lifted program, so `vcgen` continues into it. -/
@[spec]
theorem Spec.liftComp {τ : Type u'} {superSpec : OracleSpec τ} [OracleSpec.AnswerMeasure superSpec]
    [spec ⊂ₒ superSpec] [OracleSpec.SubSpec.PreservesAnswerMeasure spec superSpec]
    {α : Type} (oa : OracleComp spec α) (post : α → ℝ≥0∞ᵒᵈ) {epost : EStack⟨⟩ᵒᵈ} :
    ⦃ wp oa post epost ⦄ liftComp oa superSpec ⦃ post; epost ⦄ := by
  rw [triple_iff, ofDual_wp]
  exact (OracleComp.ProgramLogic.wp_liftComp oa _).le

/-- `Spec.liftComp` for the lift written as `liftM oa`. -/
@[spec]
theorem Spec.monadLift_liftComp {τ : Type u'} {superSpec : OracleSpec τ}
    [OracleSpec.AnswerMeasure superSpec] [spec ⊂ₒ superSpec]
    [OracleSpec.SubSpec.PreservesAnswerMeasure spec superSpec]
    {α : Type} (oa : OracleComp spec α) (post : α → ℝ≥0∞ᵒᵈ) {epost : EStack⟨⟩ᵒᵈ} :
    ⦃ wp oa post epost ⦄ (MonadLift.monadLift oa : OracleComp superSpec α) ⦃ post; epost ⦄ :=
  Spec.liftComp oa post

/-- Scaling an upper-bound triple by a constant. -/
theorem triple_const_mul {oa : OracleComp spec α} {ε : ℝ≥0∞} {post : α → ℝ≥0∞ᵒᵈ} (c : ℝ≥0∞)
    (h : ⦃ toDual ε ⦄ oa ⦃ post ⦄) :
    ⦃ toDual (c * ε) ⦄ oa ⦃ fun a => toDual (c * ofDual (post a)) ⦄ := by
  rw [triple_iff] at h ⊢
  simp only [ofDual_toDual] at h ⊢
  rw [ExpectationWP.wp_const_mul]
  exact mul_le_mul_right h c

end OracleComp.Upper

namespace OracleComp.Upper

/-- The expectation of a uniform draw is at most its largest value. -/
@[spec]
theorem Spec.uniformSample (β : Type) [SampleableType β] (post : β → ℝ≥0∞ᵒᵈ)
    {epost : EStack⟨⟩ᵒᵈ} : Triple ($ᵗ β) (Lean.Order.iInf post) post epost := by
  rw [triple_iff, iInf_eq, ofDual_toDual]
  exact wp_le_iSup _ _

/-- The expectation of a uniform index `$[0..n]` is at most its largest value. -/
@[spec]
theorem Spec.uniformFin (n : ℕ) (post : Fin (n + 1) → ℝ≥0∞ᵒᵈ) {epost : EStack⟨⟩ᵒᵈ} :
    Triple ($[0..n]) (Lean.Order.iInf post) post epost := by
  rw [triple_iff, iInf_eq, ofDual_toDual]
  exact wp_le_iSup _ _

/-- The exact rule for a uniform draw from a finite type: the average of the postcondition. Not
registered: `vcgen` does not split the sum, so the continuation stays inside the verification
condition. -/
theorem Spec.uniformSample_avg (β : Type) [SampleableType β] [Fintype β] (post : β → ℝ≥0∞ᵒᵈ)
    {epost : EStack⟨⟩ᵒᵈ} :
    Triple ($ᵗ β) (toDual ((∑ x, ofDual (post x)) / Fintype.card β)) post epost := by
  rw [triple_iff, ofDual_toDual, SampleableType.wp_uniformSample_eq_sum]

variable {ι : Type u} {spec : OracleSpec ι} [OracleSpec.UniformAnswerMeasure spec]

/-- The exact rule for a query with uniform answers: the average of the postcondition over the
answers. Not registered, for the reason given at `Spec.uniformSample_avg`. -/
theorem Spec.query_avg (t : spec.Domain) [Fintype (spec.Range t)]
    (post : spec.Range t → ℝ≥0∞ᵒᵈ) {epost : EStack⟨⟩ᵒᵈ} :
    Triple (HasQuery.query t : OracleComp spec (spec.Range t))
      (toDual (∑ u, (Fintype.card (spec.Range t) : ℝ≥0∞)⁻¹ * ofDual (post u))) post epost :=
  (triple_iff _ _ _ _).2 (OracleComp.ProgramLogic.wp_query_uniform t _).le

/-- `Spec.query_avg` for a lifted primitive query, the form `vcgen` reaches inside a handler. -/
theorem Spec.monadLift_query_avg (t : spec.Domain) [Fintype (spec.Range t)]
    (post : spec.Range t → ℝ≥0∞ᵒᵈ) {epost : EStack⟨⟩ᵒᵈ} :
    Triple (MonadLift.monadLift (liftM (OracleSpec.query t) : OracleQuery spec (spec.Range t)) :
        OracleComp spec (spec.Range t))
      (toDual (∑ u, (Fintype.card (spec.Range t) : ℝ≥0∞)⁻¹ * ofDual (post u))) post epost :=
  (triple_iff _ _ _ _).2 (OracleComp.ProgramLogic.wp_query_uniform t _).le

end OracleComp.Upper

namespace OracleComp.Upper.Dispatch

variable {ι : Type u} {spec : OracleSpec ι} [OracleSpec.AnswerMeasure spec]

/-- The upper-bound reading at the priority of a per-call scope, above every reading a file
opens: `open scoped OracleComp.Upper.Dispatch in vcgen`. -/
noncomputable scoped instance (priority := 1200) instWP :
    Std.WP.WPMonad (OracleComp spec) ℝ≥0∞ᵒᵈ EStack⟨⟩ᵒᵈ :=
  OracleComp.Upper.instWP

/-- The per-call upper-bound reading as a direct `WP` instance, which outranks direct instances
of other readings (`ExpectationWP.Lower.wpInst`). -/
noncomputable scoped instance (priority := 1200) wpInst {α : Type} :
    Std.WP.WP (OracleComp spec α) α ℝ≥0∞ᵒᵈ EStack⟨⟩ᵒᵈ :=
  (OracleComp.Upper.instWP (spec := spec)).toWP α

end OracleComp.Upper.Dispatch
