/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import VCVio.ProgramLogic.Unary.HoareTriple
public import VCVio.ProgramLogic.Unary.WP.Necessary
public import VCVio.OracleComp.Constructions.SampleableType.Basic
public import VCVio.OracleComp.Constructions.Replicate
public import VCVio.OracleComp.Coercions.SubSpec.Basic
public import VCVio.EvalDist.Monad.Option
public import VCVio.EvalDist.Monad.Except

/-!
# The angelic reading of oracle computations

The angelic interpretation of `OracleComp spec` (PolyFun's `MonadAttach.toWPMonadAngelic`) reads
`wp oa post ⊥` as "some structurally reachable output of `oa` satisfies `post`". Under
`open scoped OracleComp.Possible` a triple `⦃ True ⦄ oa ⦃ p ⦄` states that `p` is possible, and
core's `vcgen` decomposes it. Like the structural reading it needs no probability interpretation.

## Bridges

* `exists_mem_support_iff_triple`: `(∃ x ∈ support oa, p x) ↔ ⦃ True ⦄ oa ⦃ p ⦄`, with no
  assumption;
* `prEvent_pos_iff_triple_of_fullSupport`: a positive probability, when every answer of every
  query has positive mass; `prEvent_pos_iff_triple` under uniform answers;
* `pos_wp_iff_of_fullSupport` and `pos_wp_eq_wp`: positivity of an expectation, the form the nested
  expectations of an event's normal form take.

A possible outcome of positive probability needs answers of positive mass: without them a
structurally reachable output can carry no mass.

## Rules and the witness pattern

The registered rules state that a query or a uniform draw can return any value, with the
precondition `∃ u, post u`. `vcgen` does not split an existential, so each draw leaves a
verification condition `∃ u, wp (rest u) post ⊥`. It is proved by naming the witness and
continuing with the rest of the program, as in

```
refine ⟨w, ?_⟩
rw [OracleComp.Possible.wp_iff_triple]
open scoped OracleComp.Possible in vcgen
```

or with `prvcgen` (`VCVio.ProgramLogic.Tactics.PrVCGen`), which recognizes the remaining angelic
weakest precondition. The angelic reading is not conjunctive: core's `Triple.and` does not apply.

`OracleComp.Possible.Dispatch` registers the same reading at a priority above every reading a file
opens, for per-call use (`open scoped OracleComp.Possible.Dispatch in vcgen`).
-/

public section

universe u u'

open ENNReal Std.WP

/-- An indicator is positive exactly when its proposition holds: the verification condition a
positivity bridge leaves at an indicator postcondition. -/
theorem propInd_pos_iff {P : Prop} : 0 < propInd P ↔ P := by
  classical
  unfold propInd
  split_ifs with h <;> simp [h]

namespace OracleComp.Possible

variable {ι : Type u} {spec : OracleSpec ι} {α : Type}

/-- Core weakest preconditions for some structurally reachable output. Opening the scope selects
it over the structural reading. -/
noncomputable scoped instance (priority := 1100) instWP :
    Std.WP.WPMonad (OracleComp spec) Prop EStack⟨⟩ :=
  MonadAttach.toWPMonadAngelic

/-- The angelic reading as a direct `WP` instance on programs, at the scope's priority, so that
no direct instance of another scope outranks it while this one is open. -/
noncomputable scoped instance (priority := 1100) wpInst :
    Std.WP.WP (OracleComp spec α) α Prop EStack⟨⟩ :=
  (instWP (spec := spec)).toWP α

/-- The angelic weakest precondition holds exactly when some possible output satisfies the
postcondition. -/
theorem wp_iff_exists_support (oa : OracleComp spec α) (post : α → Prop) :
    Std.WP.wp oa post Lean.Order.bot ↔ ∃ a ∈ support oa, post a :=
  Iff.rfl

/-- A triple of the angelic reading: from its precondition, some possible output satisfies the
postcondition. -/
theorem triple_iff (oa : OracleComp spec α) (pre : Prop) (post : α → Prop) :
    ⦃ pre ⦄ oa ⦃ post ⦄ ↔ (pre → ∃ a ∈ support oa, post a) :=
  Triple.iff

/-- A possible outcome is an angelic triple from `True`. -/
theorem exists_mem_support_iff_triple (oa : OracleComp spec α) (p : α → Prop) :
    (∃ x ∈ support oa, p x) ↔ ⦃ True ⦄ oa ⦃ p ⦄ :=
  ⟨fun h => ⟨fun _ => h⟩, fun h => h.le_wp trivial⟩

/-- An angelic weakest precondition left by `vcgen` after a witness is named is again a triple,
which `vcgen` continues through. -/
theorem wp_iff_triple (oa : OracleComp spec α) (post : α → Prop) :
    Std.WP.wp oa post Lean.Order.bot ↔ ⦃ True ⦄ oa ⦃ post ⦄ :=
  exists_mem_support_iff_triple oa post

/-- An angelic weakest precondition of an optional computation, with failure forbidden, is a
triple of core's `OptionT` lift of the reading from `True`. -/
theorem OptionT.wp_iff_triple (mx : OptionT (OracleComp spec) α) (post : α → Prop) :
    Std.WP.wp mx post (fun _ => False, Lean.Order.bot) ↔
      ⦃ True ⦄ mx ⦃ post; (fun _ => False, Lean.Order.bot) ⦄ := by
  rw [Triple.iff]
  exact ⟨fun h _ => h, fun h => h trivial⟩

/-- An angelic weakest precondition of an exceptional computation, with exceptions forbidden, is
a triple of core's `ExceptT` lift of the reading from `True`. -/
theorem ExceptT.wp_iff_triple {E : Type} (mx : ExceptT E (OracleComp spec) α)
    (post : α → Prop) :
    Std.WP.wp mx post (fun _ => False, Lean.Order.bot) ↔
      ⦃ True ⦄ mx ⦃ post; (fun _ => False, Lean.Order.bot) ⦄ := by
  rw [Triple.iff]
  exact ⟨fun h _ => h, fun h => h trivial⟩

/-! ## Rules -/

/-- A lifted primitive query may return any answer. This is the form `vcgen` reaches from
`liftM (OracleSpec.query t)`. -/
@[spec]
theorem Spec.monadLift_query (t : spec.Domain) (post : spec.Range t → Prop)
    {epost : EStack⟨⟩} :
    Triple (MonadLift.monadLift (liftM (OracleSpec.query t) : OracleQuery spec (spec.Range t)) :
      OracleComp spec (spec.Range t)) (∃ u, post u) post epost :=
  ⟨fun ⟨u, hu⟩ => ⟨u, OracleComp.mem_support_query t u, hu⟩⟩

/-- The rule for the `query t` spelling itself, stated on `OracleComp spec`. It applies where the
program's answer type was elaborated to its reduced form (a concrete specification's `Bool` rather
than `spec.Range t`), on which the generic `HasQuery.instOfMonadLift_query` unfold cannot be
unified: here the specification is fixed by the monad before the answer type is compared. -/
@[spec]
theorem Spec.query (t : spec.Domain) (post : spec.Range t → Prop) {epost : EStack⟨⟩} :
    Triple (query t : OracleComp spec (spec.Range t)) (∃ u, post u) post epost := by
  rw [HasQuery.instOfMonadLift_query]
  exact Spec.monadLift_query t post

/-- An opaque sub-program meets a postcondition that holds at one of its possible outputs. Not
registered, since it applies to every program. -/
theorem Spec.ofSupport (oa : OracleComp spec α) (post : α → Prop) {epost : EStack⟨⟩} :
    Triple oa (∃ a ∈ support oa, post a) post epost :=
  ⟨id⟩

/-- `oa.replicate n` may return any list of `n` possible outputs of `oa`. -/
@[spec]
theorem Spec.replicate (n : ℕ) (oa : OracleComp spec α) (post : List α → Prop)
    {epost : EStack⟨⟩} :
    ⦃ ∃ xs : List α, xs.length = n ∧ (∀ x ∈ xs, x ∈ support oa) ∧ post xs ⦄ oa.replicate n
      ⦃ post; epost ⦄ :=
  ⟨fun ⟨xs, hlen, hmem, h⟩ =>
    ⟨xs, show xs ∈ support (oa.replicate n) by rw [support_replicate]; exact ⟨hlen, hmem⟩, h⟩⟩

/-- Lifting to a larger oracle world keeps the possible outputs. The precondition is the angelic
weakest precondition of the lifted program, so `vcgen` continues into it. -/
@[spec]
theorem Spec.liftComp {τ : Type u'} {superSpec : OracleSpec τ}
    [spec ⊂ₒ superSpec] [spec ˡ⊂ₒ superSpec] (oa : OracleComp spec α) (post : α → Prop)
    {epost : EStack⟨⟩} :
    ⦃ wp oa post epost ⦄ liftComp oa superSpec ⦃ post; epost ⦄ :=
  ⟨fun ⟨a, ha, h⟩ => ⟨a, (mem_support_liftComp_iff oa a).mpr ha, h⟩⟩

/-- `Spec.liftComp` for the lift written as `liftM oa`. -/
@[spec]
theorem Spec.monadLift_liftComp {τ : Type u'} {superSpec : OracleSpec τ}
    [spec ⊂ₒ superSpec] [spec ˡ⊂ₒ superSpec] (oa : OracleComp spec α) (post : α → Prop)
    {epost : EStack⟨⟩} :
    ⦃ wp oa post epost ⦄ (MonadLift.monadLift oa : OracleComp superSpec α) ⦃ post; epost ⦄ :=
  Spec.liftComp oa post

end OracleComp.Possible

namespace OracleComp.Possible

/-- A uniform draw may return any value. -/
@[spec]
theorem Spec.uniformSample (β : Type) [SampleableType β] (post : β → Prop) {epost : EStack⟨⟩} :
    Triple ($ᵗ β) (∃ x, post x) post epost :=
  ⟨fun ⟨x, hx⟩ => ⟨x, mem_support_uniformSample β, hx⟩⟩

/-- A uniform index `$[0..n]` may be any element of `Fin (n + 1)`. -/
@[spec]
theorem Spec.uniformFin (n : ℕ) (post : Fin (n + 1) → Prop) {epost : EStack⟨⟩} :
    Triple ($[0..n]) (∃ i, post i) post epost := by
  refine ⟨fun ⟨i, hi⟩ => ⟨i, ?_, hi⟩⟩
  change i ∈ support $[0..n]
  rw [ProbComp.support_uniformFin]
  trivial

/-! ## Positive probability -/

variable {ι : Type u} {spec : OracleSpec.{u, 0} ι} [OracleSpec.AnswerMeasure spec] {α : Type}

/-- When every answer of every query has positive mass, an expectation is positive exactly when
its observation is positive at some possible output. -/
theorem pos_wp_iff_of_fullSupport
    (hfull : ∀ t (u : spec.Range t), 0 < OracleSpec.AnswerMeasure.toMeasure t {u})
    (oa : OracleComp spec α) (g : α → ℝ≥0∞) :
    0 < wp⟦oa⟧ g ↔ ∃ a ∈ support oa, 0 < g a := by
  constructor
  · intro h
    by_contra hne
    push Not at hne
    exact (lt_irrefl 0) (h.trans_le
      (OracleComp.ProgramLogic.wp_le_const_of_support oa fun a ha => hne a ha))
  · rintro ⟨a, ha, hpos⟩
    let : MeasurableSpace α := ⊤
    have hmass : 0 < Pr{let x ← oa}[x = a] := by
      rw [prEvent_eq_evalDist_singleton]
      exact (mem_support_iff_evalDist_singleton_pos_of_fullSupport hfull oa a).mp ha
    calc (0 : ℝ≥0∞) < g a * Pr{let x ← oa}[x = a] := ENNReal.mul_pos hpos.ne' hmass.ne'
      _ = wp⟦oa⟧ (fun x => g a * propInd (x = a)) := (ExpectationWP.wp_const_mul _ _ _).symm
      _ ≤ wp⟦oa⟧ g := ExpectationWP.wp_mono oa fun x => by
          by_cases hx : x = a
          · subst hx
            simp
          · simp [hx]

/-- When every answer of every query has positive mass, an event has positive probability
exactly when it is possible. -/
theorem prEvent_pos_iff_of_fullSupport
    (hfull : ∀ t (u : spec.Range t), 0 < OracleSpec.AnswerMeasure.toMeasure t {u})
    (oa : OracleComp spec α) (p : α → Prop) :
    0 < Pr{let x ← oa}[p x] ↔ ∃ x ∈ support oa, p x := by
  rw [pos_wp_iff_of_fullSupport hfull]
  simp only [predInd_apply, propInd_pos_iff]

/-- When every answer of every query has positive mass, a positive probability is an angelic
triple from `True`. -/
theorem prEvent_pos_iff_triple_of_fullSupport
    (hfull : ∀ t (u : spec.Range t), 0 < OracleSpec.AnswerMeasure.toMeasure t {u})
    (oa : OracleComp spec α) (p : α → Prop) :
    0 < Pr{let x ← oa}[p x] ↔ ⦃ True ⦄ oa ⦃ p ⦄ := by
  rw [prEvent_pos_iff_of_fullSupport hfull, exists_mem_support_iff_triple]

variable {ι : Type u} {spec : OracleSpec.{u, 0} ι} [OracleSpec.UniformAnswerMeasure spec]
  {α : Type}

/-- Under uniform answers, a positive probability is an angelic triple from `True`. -/
theorem prEvent_pos_iff_triple (oa : OracleComp spec α) (p : α → Prop) :
    0 < Pr{let x ← oa}[p x] ↔ ⦃ True ⦄ oa ⦃ p ⦄ :=
  prEvent_pos_iff_triple_of_fullSupport
    (fun t u => OracleSpec.UniformAnswerMeasure.toMeasure_singleton_pos t u) oa p

/-- Under uniform answers, positivity of an expectation is the angelic weakest precondition of
positivity. As an equation of propositions it rewrites the nested expectations of an event's
normal form. -/
theorem pos_wp_eq_wp (oa : OracleComp spec α) (g : α → ℝ≥0∞) :
    (0 < wp⟦oa⟧ g) = Std.WP.wp oa (fun a => 0 < g a) Lean.Order.bot :=
  propext (pos_wp_iff_of_fullSupport
    (fun t u => OracleSpec.UniformAnswerMeasure.toMeasure_singleton_pos t u) oa g)

/-- Under uniform answers, an event of an optional computation is positive exactly when some run
succeeds with an output satisfying it: a triple of core's `OptionT` lift of the angelic reading
from `True`, with failure forbidden. -/
theorem OptionT.prEvent_pos_iff_triple (mx : OptionT (OracleComp spec) α) (p : α → Prop) :
    0 < Pr{let x ← mx}[p x] ↔ ⦃ True ⦄ mx ⦃ p; (fun _ => False, Lean.Order.bot) ⦄ := by
  rw [_root_.OptionT.prEvent_eq_run, OracleComp.Possible.prEvent_pos_iff_triple, Triple.iff,
    Triple.iff]
  simp only [Std.WP.OptionT.wp_apply_eq]
  exact imp_congr_right fun _ => Iff.of_eq (congrArg (fun q => Std.WP.wp mx.run q Lean.Order.bot)
    (funext fun o => by cases o <;> rfl))

/-- Under uniform answers, an event of an exceptional computation is positive exactly when some
run returns an output satisfying it: a triple of core's `ExceptT` lift of the angelic reading
from `True`, with exceptions forbidden. -/
theorem ExceptT.prEvent_pos_iff_triple {E : Type} (mx : ExceptT E (OracleComp spec) α)
    (p : α → Prop) :
    0 < Pr{let x ← mx}[p x] ↔ ⦃ True ⦄ mx ⦃ p; (fun _ => False, Lean.Order.bot) ⦄ := by
  rw [_root_.ExceptT.prEvent_eq_run, OracleComp.Possible.prEvent_pos_iff_triple, Triple.iff,
    Triple.iff]
  simp only [Std.WP.ExceptT.wp_apply_eq]
  exact imp_congr_right fun _ => Iff.of_eq (congrArg (fun q => Std.WP.wp mx.run q Lean.Order.bot)
    (funext fun r => by cases r <;> rfl))

/-- Under uniform answers, positivity of an expectation over an optional computation is the
angelic weakest precondition, with failure forbidden, of positivity. -/
theorem OptionT.pos_wp_eq_wp (mx : OptionT (OracleComp spec) α) (g : α → ℝ≥0∞) :
    (0 < wp⟦mx⟧ g) = Std.WP.wp mx (fun a => 0 < g a) (fun _ => False, Lean.Order.bot) := by
  rw [_root_.OptionT.wp_eq_run, OracleComp.Possible.pos_wp_eq_wp]
  simp only [Std.WP.OptionT.wp_apply_eq]
  exact congrArg (fun q => Std.WP.wp mx.run q Lean.Order.bot)
    (funext fun o => by cases o <;> simp [Lean.Order.pushOption])

/-- Under uniform answers, positivity of an expectation over an exceptional computation is the
angelic weakest precondition, with exceptions forbidden, of positivity. -/
theorem ExceptT.pos_wp_eq_wp {E : Type} (mx : ExceptT E (OracleComp spec) α) (g : α → ℝ≥0∞) :
    (0 < wp⟦mx⟧ g) = Std.WP.wp mx (fun a => 0 < g a) (fun _ => False, Lean.Order.bot) := by
  rw [_root_.ExceptT.wp_eq_run, OracleComp.Possible.pos_wp_eq_wp]
  simp only [Std.WP.ExceptT.wp_apply_eq]
  exact congrArg (fun q => Std.WP.wp mx.run q Lean.Order.bot)
    (funext fun r => by cases r <;> simp [Lean.Order.pushExcept, Except.toOption])

end OracleComp.Possible

namespace OracleComp.Possible.Dispatch

variable {ι : Type u} {spec : OracleSpec ι}

/-- The angelic reading at the priority of a per-call scope, above every reading a file opens:
`open scoped OracleComp.Possible.Dispatch in vcgen`. -/
noncomputable scoped instance (priority := 1200) instWP :
    Std.WP.WPMonad (OracleComp spec) Prop EStack⟨⟩ :=
  OracleComp.Possible.instWP

/-- The per-call angelic reading as a direct `WP` instance, which outranks direct instances of
other readings. -/
noncomputable scoped instance (priority := 1200) wpInst {α : Type} :
    Std.WP.WP (OracleComp spec α) α Prop EStack⟨⟩ :=
  (OracleComp.Possible.instWP (spec := spec)).toWP α

end OracleComp.Possible.Dispatch
