/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.Control.Monad.ExactWP
public import VCVio.ProgramLogic.Unary.WP.LowerSpecs
public import VCVio.OracleComp.Constructions.SampleableType.Measure

/-!
# The upper reading: upper bounds as core triples

Under the lower reading of `OracleComp spec` (`OracleComp.Lower`), a core triple
`⦃ pre ⦄ oa ⦃ post ⦄` states `pre ≤ wp oa post`. That interpretation is exact, so PolyFun's
`ExactWPMonad.dual` is the same interpretation over the order duals `ℝ≥0∞ᵒᵈ` and `EStack⟨⟩ᵒᵈ`,
where `⊑` is `≥`: a triple of the dual reading states `wp oa post ≤ pre`, an upper bound.
`open scoped OracleComp.Upper` selects it (at priority 1200, above the readings at 1100), and
core's `vcgen` then decomposes upper bounds with the same transformer rules, `@[spec]` rules
and loop invariants as lower bounds.

## Stating an upper bound

`prEvent_le_iff_triple` reads `Pr{let x ← oa}[p x] ≤ ε` as
`⦃ toDual ε ⦄ oa ⦃ fun x => toDual (propInd (p x)) ⦄`, and `wp_le_iff_triple` does the same for
an expectation. For a stateful program, `triple_stateT_iff` reads a triple as a bound from every
initial state and `prEvent_run_le_of_triple` reads off the event bound from one state. A
precondition is written `toDual ε`: core elaborates the precondition before it looks up the
interpretation, and a precondition of type `ℝ≥0∞` selects the lower reading.

## Rules

* Registered, bounding by the largest outcome (core's indexed infimum `Lean.Order.iInf` of the
  dual, which `vcgen` splits into one condition per outcome): `Spec.query`,
  `Spec.monadLift_query`, `Spec.uniformSample`, `Spec.replicate`, and the lifts
  `Spec.liftComp`, `Spec.monadLift_liftComp`.
* Averaging, applied explicitly (`vcgen [Spec.uniformSample_avg]`): `Spec.uniformSample_avg`,
  `Spec.query_avg`, `Spec.monadLift_query_avg`.
* Opaque sub-programs: `Spec.ofSupport`, `Spec.ofNecessary`, `Spec.ofWp`.
* Bad events: `Spec.bind_of_bad` charges a first draw's bad event in full, and
  `Spec.uniformSample_bind_of_bad` charges a uniform draw `d / |β|`.
* Frames: `triple_add_frame`, `triple_const_mul`.
* Budgets: the ranked simulation rules and the union bound over queries are in
  `VCVio.ProgramLogic.Library.T1.UpperRanked`.

## Verification conditions

The conditions are entailments of the dual carrier. `rel_iff` reads one as an inequality in
`ℝ≥0∞`, `ofDual_toDual` cancels the conversions and `ofDual_wp` returns a residual weakest
precondition to `OracleComp.ProgramLogic.wp`. `upper_readback` applies these, with core's
`StateT.wp_apply_eq` and Mathlib's `ofDual` arithmetic lemmas, before other simplification: the
default `simp` set distributes `toDual` over arithmetic before it compares the two sides.

With `VCVio.ProgramLogic.Tactics` imported, a bare `vcgen` on an upper triple is routed to
VCVio's `ℝ≥0∞` pipeline; `vcgen [rules]` or `vcgen (errorOnMissingSpec := true)` reaches core's.
-/

@[expose] public section

universe u u'

open ENNReal Std.WP OrderDual OracleSpec OracleComp

namespace OracleComp.Upper

variable {ι : Type u} {spec : OracleSpec ι} [AnswerMeasure spec] {α β : Type}

open scoped OracleComp.Lower in
/-- Core weakest preconditions of the expectation over the order duals: a triple states an upper
bound on the expectation. -/
noncomputable scoped instance (priority := 1200) instWP :
    Std.WP.WPMonad (OracleComp spec) ℝ≥0∞ᵒᵈ EStack⟨⟩ᵒᵈ :=
  ExactWPMonad.dual

/-- The upper reading as a direct `WP` instance on programs, at the scope's priority. -/
noncomputable scoped instance (priority := 1200) wpInst :
    Std.WP.WP (OracleComp spec α) α ℝ≥0∞ᵒᵈ EStack⟨⟩ᵒᵈ :=
  (instWP (spec := spec)).toWP α

open scoped OracleComp.Upper

/-! ## Reading triples back -/

/-- The weakest precondition of the upper reading is the expectation, read in `ℝ≥0∞`. -/
theorem wp_eq (oa : OracleComp spec α) (post : α → ℝ≥0∞ᵒᵈ) (epost : EStack⟨⟩ᵒᵈ) :
    wp oa post epost = toDual (ProgramLogic.wp oa fun a => ofDual (post a)) :=
  rfl

/-- A residual weakest precondition of the upper reading, read in `ℝ≥0∞`, is an expectation. -/
theorem ofDual_wp (oa : OracleComp spec α) (post : α → ℝ≥0∞ᵒᵈ) (epost : EStack⟨⟩ᵒᵈ) :
    ofDual (wp oa post epost) = ProgramLogic.wp oa fun a => ofDual (post a) :=
  rfl

/-- An expectation moved into the upper reading, where `vcgen` steps through it. -/
theorem toDual_wp (oa : OracleComp spec α) (g : α → ℝ≥0∞) :
    toDual (ProgramLogic.wp oa g) = wp oa (fun a => toDual (g a)) Lean.Order.bot :=
  rfl

/-- A triple of the upper reading is an upper bound on the expectation. -/
theorem triple_iff (oa : OracleComp spec α) (pre : ℝ≥0∞ᵒᵈ) (post : α → ℝ≥0∞ᵒᵈ)
    (epost : EStack⟨⟩ᵒᵈ) :
    Triple oa pre post epost ↔ ProgramLogic.wp oa (fun a => ofDual (post a)) ≤ ofDual pre :=
  Triple.iff

/-- An upper bound on an expectation is a triple of the upper reading. -/
theorem wp_le_iff_triple (oa : OracleComp spec α) (g : α → ℝ≥0∞) (ε : ℝ≥0∞) :
    ProgramLogic.wp oa g ≤ ε ↔ ⦃ toDual ε ⦄ oa ⦃ fun a => toDual (g a) ⦄ :=
  (triple_iff oa _ _ _).symm

/-- An upper bound on an event is a triple with the event's indicator as postcondition:
`rw [prEvent_le_iff_triple]` turns a plain `Pr[E] ≤ ε` goal into a `vcgen` goal. -/
theorem prEvent_le_iff_triple (oa : OracleComp spec α) (p : α → Prop) (ε : ℝ≥0∞) :
    Pr{let x ← oa}[p x] ≤ ε ↔
      ⦃ toDual ε ⦄ oa ⦃ fun x => toDual (ProgramLogic.propInd (p x)) ⦄ := by
  rw [ProgramLogic.prEvent_eq_wp_propInd]
  exact (triple_iff oa _ _ _).symm

/-- An upper bound on the event of a `Prop`-valued computation, the form of a multi-draw event
`Pr{let a ← oa; let x ← ob a}[p a x]`, is a triple with the indicator as postcondition. -/
theorem prEvent_le_iff_triple' (mx : OracleComp spec Prop) (ε : ℝ≥0∞) :
    prEvent mx ≤ ε ↔ ⦃ toDual ε ⦄ mx ⦃ fun P => toDual (ProgramLogic.propInd P) ⦄ := by
  rw [ProgramLogic.prEvent_eq_wp]
  exact (triple_iff mx _ _ _).symm

/-- A stateful triple of the upper reading bounds the expectation from every initial state. -/
theorem triple_stateT_iff {σ : Type} (mx : StateT σ (OracleComp spec) α)
    (pre : σ → ℝ≥0∞ᵒᵈ) (post : α → σ → ℝ≥0∞ᵒᵈ) (epost : EStack⟨⟩ᵒᵈ) :
    Triple mx pre post epost ↔
      ∀ s, ProgramLogic.wp (mx.run s) (fun z => ofDual (post z.1 z.2)) ≤ ofDual (pre s) :=
  Triple.iff.trans (forall_congr' fun _ => Iff.rfl)

/-- The event bound of a stateful triple of the upper reading, read from one initial state. -/
theorem prEvent_run_le_of_triple {σ : Type} {mx : StateT σ (OracleComp spec) α}
    {pre : σ → ℝ≥0∞ᵒᵈ} {p : α → σ → Prop}
    (h : ⦃ pre ⦄ mx ⦃ fun a s => toDual (ProgramLogic.propInd (p a s)) ⦄) (s : σ) :
    Pr{let z ← mx.run s}[p z.1 z.2] ≤ ofDual (pre s) := by
  rw [ProgramLogic.prEvent_eq_wp_propInd]
  exact (triple_stateT_iff mx _ _ _).1 h s

/-- The entailment of the dual carrier is the reversed order of `ℝ≥0∞`. -/
theorem rel_iff (a b : ℝ≥0∞ᵒᵈ) : Lean.Order.PartialOrder.rel a b ↔ ofDual b ≤ ofDual a :=
  Iff.rfl

/-- Core's indexed infimum on the dual carrier is the supremum in `ℝ≥0∞`. -/
theorem iInf_eq {κ : Type _} (f : κ → ℝ≥0∞ᵒᵈ) :
    Lean.Order.iInf f = toDual (⨆ i, ofDual (f i)) :=
  Lean.Order.PartialOrder.rel_antisymm
    (show (⨆ i, ofDual (f i)) ≤ ofDual (Lean.Order.iInf f) from
      iSup_le fun i => Lean.Order.iInf_le f i)
    (Lean.Order.le_iInf f _ fun i => le_iSup (fun i => ofDual (f i)) i)

/-- Readback of the upper reading's verification conditions into `ℝ≥0∞`. -/
macro "upper_readback" : tactic => `(tactic| simp only [OracleComp.Upper.rel_iff,
  OrderDual.ofDual_toDual, OracleComp.Upper.ofDual_wp, binderNameHint, StateT.wp_apply_eq,
  _root_.ofDual_add, _root_.ofDual_mul, _root_.ofDual_div, _root_.ofDual_inv,
  _root_.ofDual_zero, _root_.ofDual_one, _root_.ofDual_natCast, _root_.ofDual_ofNat,
  OracleComp.ProgramLogic.wp_pure,
  OracleComp.ProgramLogic.propInd_le_one, le_refl] at *)

/-! ## Rules -/

/-- An expectation is at most the largest value of its observation. -/
theorem wp_le_iSup (oa : OracleComp spec α) (g : α → ℝ≥0∞) :
    ProgramLogic.wp oa g ≤ ⨆ x, g x :=
  ProgramLogic.wp_le_const_of_support oa fun x _ => le_iSup g x

/-- A lifted primitive query is at most its largest answer's value (the form `vcgen` reaches
from `liftM (OracleSpec.query t)`). -/
@[spec]
theorem Spec.monadLift_query (t : spec.Domain) (post : spec.Range t → ℝ≥0∞ᵒᵈ)
    {epost : EStack⟨⟩ᵒᵈ} :
    Triple (MonadLift.monadLift (liftM (OracleSpec.query t) : OracleQuery spec (spec.Range t)) :
      OracleComp spec (spec.Range t)) (Lean.Order.iInf post) post epost := by
  rw [triple_iff, iInf_eq, ofDual_toDual]
  exact wp_le_iSup _ _

/-- A query is at most its largest answer's value. -/
@[spec]
theorem Spec.query (t : spec.Domain) (post : spec.Range t → ℝ≥0∞ᵒᵈ) {epost : EStack⟨⟩ᵒᵈ} :
    Triple (query t : OracleComp spec (spec.Range t)) (Lean.Order.iInf post) post epost := by
  rw [HasQuery.instOfMonadLift_query]
  exact Spec.monadLift_query t post

/-- A uniform draw is at most its largest value. -/
@[spec]
theorem Spec.uniformSample (β : Type) [SampleableType β] (post : β → ℝ≥0∞ᵒᵈ)
    {epost : EStack⟨⟩ᵒᵈ} : Triple ($ᵗ β) (Lean.Order.iInf post) post epost := by
  rw [triple_iff, iInf_eq, ofDual_toDual]
  exact wp_le_iSup _ _

/-- `oa.replicate n` is at most its largest value on a list of `n` possible outputs of `oa`. -/
@[spec]
theorem Spec.replicate (n : ℕ) (oa : OracleComp spec α) (post : List α → ℝ≥0∞ᵒᵈ)
    {epost : EStack⟨⟩ᵒᵈ} :
    ⦃ Lean.Order.iInf fun xs : {xs : List α // xs.length = n ∧ ∀ x ∈ xs, x ∈ support oa} =>
        post xs.1 ⦄ oa.replicate n ⦃ post; epost ⦄ := by
  rw [triple_iff, iInf_eq, ofDual_toDual]
  refine ProgramLogic.wp_le_const_of_support (oa.replicate n) fun xs hxs => ?_
  rw [support_replicate] at hxs
  exact le_iSup (fun xs : {xs : List α // xs.length = n ∧ ∀ x ∈ xs, x ∈ support oa} =>
    ofDual (post xs.1)) ⟨xs, hxs⟩

/-- An opaque sub-program is at most its largest value on its support. Not registered:
`vcgen [Spec.ofSupport oa]`. -/
theorem Spec.ofSupport (oa : OracleComp spec α) (post : α → ℝ≥0∞ᵒᵈ) {epost : EStack⟨⟩ᵒᵈ} :
    Triple oa (Lean.Order.iInf fun a : {a // a ∈ support oa} => post a.1) post epost := by
  rw [triple_iff, iInf_eq, ofDual_toDual]
  exact ProgramLogic.wp_le_const_of_support oa fun x hx =>
    le_iSup (fun a : {a // a ∈ support oa} => ofDual (post a.1)) ⟨x, hx⟩

/-- An opaque sub-program is at most its largest value on the outputs satisfying a predicate
true on its support. Not registered: `vcgen [Spec.ofNecessary oa q h]`. -/
theorem Spec.ofNecessary (oa : OracleComp spec α) (q : α → Prop) (h : ∀ a ∈ support oa, q a)
    (post : α → ℝ≥0∞ᵒᵈ) {epost : EStack⟨⟩ᵒᵈ} :
    Triple oa (Lean.Order.iInf fun a : {a // q a} => post a.1) post epost := by
  rw [triple_iff, iInf_eq, ofDual_toDual]
  exact ProgramLogic.wp_le_const_of_support oa fun x hx =>
    le_iSup (fun a : {a // q a} => ofDual (post a.1)) ⟨x, h x hx⟩

/-- An opaque sub-program's expectation, as its own upper bound, for a hypothesis to bound.
Not registered: `vcgen [Spec.ofWp oa]`. -/
theorem Spec.ofWp (oa : OracleComp spec α) (post : α → ℝ≥0∞ᵒᵈ) {epost : EStack⟨⟩ᵒᵈ} :
    Triple oa (toDual (ProgramLogic.wp oa fun a => ofDual (post a))) post epost := by
  rw [triple_iff, ofDual_toDual]

/-- **Bad-event bind rule.** The first draw's bad event is charged in full, and off it every
continuation meets the bound `ε`. Not registered: `vcgen [Spec.bind_of_bad oa f bad]`. -/
theorem Spec.bind_of_bad (oa : OracleComp spec α) (f : α → OracleComp spec β) (bad : α → Prop)
    {ε : ℝ≥0∞} (post : β → ℝ≥0∞ᵒᵈ) {epost : EStack⟨⟩ᵒᵈ} (hle : ∀ b, ofDual (post b) ≤ 1)
    (hgood : ∀ a ∈ support oa, ¬bad a → Triple (f a) (toDual ε) post epost) :
    Triple (oa >>= f) (toDual (Pr{let a ← oa}[bad a] + ε)) post epost := by
  rw [triple_iff, ofDual_toDual, ProgramLogic.wp_bind, ProgramLogic.prEvent_eq_wp_propInd,
    ← ProgramLogic.wp_const oa ε, ← ProgramLogic.wp_add]
  refine ProgramLogic.wp_mono_of_support oa fun a ha => ?_
  by_cases hb : bad a
  · calc ProgramLogic.wp (f a) (fun b => ofDual (post b))
        ≤ ProgramLogic.wp (f a) fun _ => 1 := ProgramLogic.wp_mono _ hle
      _ = 1 := ProgramLogic.wp_const _ 1
      _ ≤ ProgramLogic.propInd (bad a) + ε := by simp [ProgramLogic.propInd, hb]
  · exact ((triple_iff _ _ _ _).1 (hgood a ha hb)).trans le_add_self

/-- **Fresh uniform draw rule.** A uniform draw that is bad on at most `d` values is charged
`d / |β|`, and off it every continuation meets the bound `ε`. -/
theorem Spec.uniformSample_bind_of_bad [SampleableType β] [Fintype β] {γ : Type}
    (f : β → ProbComp γ) (bad : β → Prop) [DecidablePred bad] {d : ℕ}
    (hd : (Finset.univ.filter bad).card ≤ d) {ε : ℝ≥0∞} (post : γ → ℝ≥0∞ᵒᵈ)
    {epost : EStack⟨⟩ᵒᵈ} (hle : ∀ c, ofDual (post c) ≤ 1)
    (hgood : ∀ b, ¬bad b → Triple (f b) (toDual ε) post epost) :
    Triple (($ᵗ β : ProbComp β) >>= f) (toDual (d / Fintype.card β + ε)) post epost := by
  have h := (triple_iff _ _ _ _).1 (Spec.bind_of_bad ($ᵗ β) f bad post hle fun b _ => hgood b)
  rw [ofDual_toDual, SampleableType.prEvent_uniformSample] at h
  rw [triple_iff, ofDual_toDual]
  exact h.trans (add_le_add (ENNReal.div_le_div_right (by exact_mod_cast hd) _) le_rfl)

/-- Adding a constant to an upper-bound triple: the frame rule of the upper reading. -/
theorem triple_add_frame {oa : OracleComp spec α} {ε : ℝ≥0∞} {post : α → ℝ≥0∞ᵒᵈ} (c : ℝ≥0∞)
    (h : ⦃ toDual ε ⦄ oa ⦃ post ⦄) :
    ⦃ toDual (c + ε) ⦄ oa ⦃ fun a => toDual (c + ofDual (post a)) ⦄ := by
  rw [triple_iff] at h ⊢
  simp only [ofDual_toDual] at h ⊢
  rw [ProgramLogic.wp_add]
  exact add_le_add (ProgramLogic.wp_le_const_of_support oa fun _ _ => le_rfl) h

/-- Scaling an upper-bound triple by a constant. -/
theorem triple_const_mul {oa : OracleComp spec α} {ε : ℝ≥0∞} {post : α → ℝ≥0∞ᵒᵈ} (c : ℝ≥0∞)
    (h : ⦃ toDual ε ⦄ oa ⦃ post ⦄) :
    ⦃ toDual (c * ε) ⦄ oa ⦃ fun a => toDual (c * ofDual (post a)) ⦄ := by
  rw [triple_iff] at h ⊢
  simp only [ofDual_toDual] at h ⊢
  rw [ProgramLogic.wp_mul_const]
  exact mul_le_mul_right h c

/-- The exact rule of a finite uniform draw: the average of the postcondition. Not registered:
`vcgen` does not split the sum, so the continuation stays in the verification condition. -/
theorem Spec.uniformSample_avg (β : Type) [SampleableType β] [Fintype β] (post : β → ℝ≥0∞ᵒᵈ)
    {epost : EStack⟨⟩ᵒᵈ} :
    Triple ($ᵗ β) (toDual ((∑ x, ofDual (post x)) / Fintype.card β)) post epost := by
  rw [triple_iff, ofDual_toDual, OracleComp.Lower.wp_uniformSample_eq_tsum, tsum_fintype,
    Nat.card_eq_fintype_card]

end OracleComp.Upper

namespace OracleComp.Upper

open scoped OracleComp.Upper

section uniform

variable {ι : Type u} {spec : OracleSpec ι} [UniformAnswerMeasure spec] {α : Type}

/-- The exact rule of a query with uniform answers: the average over the answers. -/
theorem Spec.query_avg (t : spec.Domain) [Fintype (spec.Range t)]
    (post : spec.Range t → ℝ≥0∞ᵒᵈ) {epost : EStack⟨⟩ᵒᵈ} :
    Triple (HasQuery.query t : OracleComp spec (spec.Range t))
      (toDual (∑ u, (Fintype.card (spec.Range t) : ℝ≥0∞)⁻¹ * ofDual (post u))) post epost :=
  (triple_iff _ _ _ _).2 (ProgramLogic.wp_query_uniform t _).le

/-- `Spec.query_avg` for a lifted primitive query, the form `vcgen` reaches inside a handler. -/
theorem Spec.monadLift_query_avg (t : spec.Domain) [Fintype (spec.Range t)]
    (post : spec.Range t → ℝ≥0∞ᵒᵈ) {epost : EStack⟨⟩ᵒᵈ} :
    Triple (MonadLift.monadLift (liftM (OracleSpec.query t) : OracleQuery spec (spec.Range t)) :
        OracleComp spec (spec.Range t))
      (toDual (∑ u, (Fintype.card (spec.Range t) : ℝ≥0∞)⁻¹ * ofDual (post u))) post epost :=
  (triple_iff _ _ _ _).2 (ProgramLogic.wp_query_uniform t _).le

variable {τ : Type u'} {superSpec : OracleSpec τ} [UniformAnswerMeasure superSpec]
  [spec ⊂ₒ superSpec] [spec ˡ⊂ₒ superSpec]

/-- Lifting along an inclusion of uniform specifications keeps the expectation; the
precondition is the lifted program's weakest precondition, so `vcgen` continues into it. -/
@[spec]
theorem Spec.liftComp (oa : OracleComp spec α) (post : α → ℝ≥0∞ᵒᵈ) {epost : EStack⟨⟩ᵒᵈ} :
    ⦃ wp oa post epost ⦄ liftComp oa superSpec ⦃ post; epost ⦄ := by
  rw [triple_iff, ofDual_wp]
  exact (ProgramLogic.wp_liftComp oa _).le

/-- `Spec.liftComp` for the lift written as `liftM oa`. -/
@[spec]
theorem Spec.monadLift_liftComp (oa : OracleComp spec α) (post : α → ℝ≥0∞ᵒᵈ)
    {epost : EStack⟨⟩ᵒᵈ} :
    ⦃ wp oa post epost ⦄ (MonadLift.monadLift oa : OracleComp superSpec α) ⦃ post; epost ⦄ :=
  Spec.liftComp oa post

end uniform

end OracleComp.Upper
