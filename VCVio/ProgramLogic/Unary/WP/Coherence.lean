/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import VCVio.ProgramLogic.Unary.WP.Probabilistic
public import VCVio.ProgramLogic.Unary.WP.Necessary
public import VCVio.ProgramLogic.Unary.WP.Possible
public import VCVio.ProgramLogic.Unary.WP.Upper

/-!
# Coherence of unary assertion carriers

These lemmas relate structural predicates, probability-valued assertions, and quantitative
expectations. The probability-one equivalence uses `UniformAnswerMeasure`; it is not a generic
identification of measure-theoretic almost-sure behavior with structural reachability.

The statements expose the underlying algebras, so several carrier instances need not be
active in the same scope. Forgetting the probability bound uses `wp_restrictIic_val`.

The bridges in `OracleComp.Necessary` state events of probability one or zero as structural
triples, the form core's `vcgen` proves: `prEvent_eq_one_iff_triple`,
`evalDist_true_eq_one_iff_triple` (the shape of the `PerfectlyCorrect` and `PerfectlyComplete`
notions), and `prEvent_eq_zero_iff_triple`. Establishing probability one from a triple,
`prEvent_eq_one_of_triple`, needs no uniformity. `forall_mem_support_iff_triple` states a support
condition as a structural triple, with no probability interpretation.

An event's normal form nests one expectation per draw. `wp_eq_one_iff_of_fullSupport` states an
expectation of an observation bounded by `1` equal to `1` as the observation equal to `1` at every
possible output, when every answer has positive mass; `wp_eq_one_eq_wp` is its uniform-answer form
as an equation of propositions, which rewrites each nested expectation into the structural
reading.
-/

@[expose] public section

universe u

open ENNReal OracleComp.ProgramLogic OracleComp.ProgramLogic.PropLogic

namespace OracleComp.WP.Coherence

variable {ι : Type u} {spec : OracleSpec ι}
variable [OracleSpec.UniformAnswerMeasure spec]
variable {α : Type}

/-! ## Probabilistic ↔ Quantitative

The probabilistic `Std.WP.wp` agrees with the quantitative one
under `Subtype.val`; that statement lives in `…/WP/Probabilistic.lean`
as `OracleComp.Probabilistic.wp_val_eq_wp`. We do not restate
it here because pulling `OracleComp.Probabilistic.instWP_prob` into scope
to talk about `Std.WP.wp` requires `open OracleComp.Probabilistic`,
which then occludes the qualitative tier discussed below. -/

/-! ## Qualitative ↔ Probabilistic (support-vs-expectation bridge)

For an `OracleComp` with uniform configured answer measures, the support-based `Prop`-valued
`wp` agrees
with "the probabilistic `wp` on the indicator post equals `1`". -/

/-- Qualitative ↔ Probabilistic coherence: a `Prop`-valued post is
satisfied almost-surely iff its indicator post has probabilistic `wp`
equal to `1`.

The `[DecidablePred post]` requirement is intrinsic to the indicator
construction; consumers without classical-decidable predicates can
`Classical.dec`-coerce on call sites or reformulate via
`prEvent_eq_wp_indicator` directly. -/
theorem wp_qual_iff_wp_prob_indicator_eq_one
    (oa : OracleComp spec α) (post : α → Prop) [DecidablePred post] :
    (letI := MonadAttach.toWPMonadDemonic (m := OracleComp spec);
      Std.WP.wp oa post estack⟨⟩) ↔
      wp⟦oa⟧ (fun a => if post a then 1 else 0) = 1 := by
  rw [wp_iff_forall_support, ← prEvent_eq_wp_indicator, OracleComp.prEvent_eq_one_iff]

/-- Convenience: the `Prob`-valued indicator-as-`wp` form of the
coherence lemma, for users who have already lifted their post to `Prob`
via `Prob.indicator`. -/
theorem wp_qual_iff_wp_prob_indicator_val_eq_one
    (oa : OracleComp spec α) (post : α → Prop) [DecidablePred post] :
    (letI := MonadAttach.toWPMonadDemonic (m := OracleComp spec);
      Std.WP.wp oa post estack⟨⟩) ↔
      wp⟦oa⟧ (fun a => (Prob.indicator (post a)).val) = 1 :=
  wp_qual_iff_wp_prob_indicator_eq_one oa post

end OracleComp.WP.Coherence

/-! ## Events as structural triples -/

namespace OracleComp.Necessary

open Std.WP

variable {ι : Type u} {spec : OracleSpec ι} {α : Type}

/-- A support condition is a structural triple from `True`. -/
theorem forall_mem_support_iff_triple (mx : OracleComp spec α) (p : α → Prop) :
    (∀ x ∈ support mx, p x) ↔ ⦃ True ⦄ mx ⦃ p ⦄ := by
  rw [Triple.iff]
  exact ⟨fun h _ => h, fun h => h trivial⟩

/-- A structural weakest precondition is a triple from `True`. -/
theorem wp_iff_triple (mx : OracleComp spec α) (post : α → Prop) :
    Std.WP.wp mx post Lean.Order.bot ↔ ⦃ True ⦄ mx ⦃ post ⦄ :=
  forall_mem_support_iff_triple mx post

/-- A structural triple from `True` gives probability one under any answer measures. -/
theorem prEvent_eq_one_of_triple [OracleSpec.AnswerMeasure spec] {mx : OracleComp spec α}
    {p : α → Prop} (h : ⦃ True ⦄ mx ⦃ p ⦄) : Pr{let x ← mx}[p x] = 1 :=
  prEvent_eq_one_of_forall_mem_support mx p (h.le_wp trivial)

variable [OracleSpec.UniformAnswerMeasure spec]

/-- Under uniform answers, an event has probability one exactly when every possible output
satisfies it: a structural triple from `True`. -/
theorem prEvent_eq_one_iff_triple (mx : OracleComp spec α) (p : α → Prop) :
    Pr{let x ← mx}[p x] = 1 ↔ ⦃ True ⦄ mx ⦃ p ⦄ := by
  rw [prEvent_eq_one_iff, Triple.iff]
  exact ⟨fun h _ => h, fun h => h trivial⟩

/-- Under uniform answers, a Boolean computation puts mass one on `true` exactly when it always
returns `true`: the form of the `PerfectlyCorrect` and `PerfectlyComplete` notions. -/
theorem evalDist_true_eq_one_iff_triple (mx : OracleComp spec Bool) :
    𝒟[mx] {true} = 1 ↔ ⦃ True ⦄ mx ⦃ fun b => b = true ⦄ := by
  rw [← prEvent_eq_evalDist_singleton, prEvent_eq_one_iff_triple]

/-- Under uniform answers, an event has probability zero exactly when no possible output
satisfies it. -/
theorem prEvent_eq_zero_iff_triple (mx : OracleComp spec α) (p : α → Prop) :
    Pr{let x ← mx}[p x] = 0 ↔ ⦃ True ⦄ mx ⦃ fun x => ¬ p x ⦄ := by
  rw [prEvent_eq_zero_iff, Triple.iff]
  exact ⟨fun h _ => h, fun h => h trivial⟩

end OracleComp.Necessary

/-! ## Nested expectations equal to one -/

namespace OracleComp.Necessary

open Std.WP

section fullSupport

variable {ι : Type u} {spec : OracleSpec.{u, 0} ι} [OracleSpec.AnswerMeasure spec] {α : Type}

/-- When every answer of every query has positive mass, an expectation of an observation bounded
by `1` equals `1` exactly when the observation equals `1` at every possible output. -/
theorem wp_eq_one_iff_of_fullSupport
    (hfull : ∀ t (u : spec.Range t), 0 < OracleSpec.AnswerMeasure.toMeasure t {u})
    (mx : OracleComp spec α) (g : α → ℝ≥0∞) (hg : ∀ a, g a ≤ 1) :
    wp⟦mx⟧ g = 1 ↔ ∀ a ∈ support mx, g a = 1 := by
  constructor
  · intro h a ha
    by_contra hne
    have hsum : wp⟦mx⟧ g + wp⟦mx⟧ (fun x => 1 - g x) = 1 + 0 := by
      rw [← ExpectationWP.wp_add, add_zero]
      simp only [add_tsub_cancel_of_le (hg _)]
      exact ExpectationWP.wp_const_of_oracle mx 1
    rw [h, ENNReal.add_right_inj ENNReal.one_ne_top] at hsum
    refine (ne_of_gt ?_) hsum
    exact (OracleComp.Possible.pos_wp_iff_of_fullSupport hfull mx _).2
      ⟨a, ha, tsub_pos_of_lt (lt_of_le_of_ne (hg a) hne)⟩
  · intro h
    rw [← ExpectationWP.wp_const_of_oracle mx 1]
    exact wp_congr_of_support mx h

/-- When every answer of every query has positive mass, an expectation of an observation bounded
by `1` equals `1` exactly when a structural triple from `True` holds. -/
theorem wp_eq_one_iff_triple_of_fullSupport
    (hfull : ∀ t (u : spec.Range t), 0 < OracleSpec.AnswerMeasure.toMeasure t {u})
    (mx : OracleComp spec α) (g : α → ℝ≥0∞) (hg : ∀ a, g a ≤ 1) :
    wp⟦mx⟧ g = 1 ↔ ⦃ True ⦄ mx ⦃ fun a => g a = 1 ⦄ := by
  rw [wp_eq_one_iff_of_fullSupport hfull mx g hg, forall_mem_support_iff_triple]

end fullSupport

variable {ι : Type u} {spec : OracleSpec.{u, 0} ι} [OracleSpec.UniformAnswerMeasure spec]
  {α : Type}

/-- Under uniform answers, an expectation of an observation bounded by `1` equal to `1` is the
structural weakest precondition of the observation equal to `1`. As an equation of propositions
it rewrites the nested expectations of an event's normal form. -/
theorem wp_eq_one_eq_wp (mx : OracleComp spec α) (g : α → ℝ≥0∞) (hg : ∀ a, g a ≤ 1) :
    (wp⟦mx⟧ g = 1) = Std.WP.wp mx (fun a => g a = 1) Lean.Order.bot :=
  propext (wp_eq_one_iff_of_fullSupport
    (fun t u => OracleSpec.UniformAnswerMeasure.toMeasure_singleton_pos t u) mx g hg)

end OracleComp.Necessary

/-! ## Events of transformer stacks

An event of an `OptionT` or `ExceptT` program over an oracle computation is read through core's
lift of the reading, with failure and exceptions forbidden: the exception assertion is
`fun _ => False`. The bridges mirror the flat ones, through the run of the stack. -/

namespace OracleComp.Necessary

open Std.WP

variable {ι : Type u} {spec : OracleSpec.{u, 0} ι} {α : Type}

/-- A structural weakest precondition of an optional computation, with failure forbidden, is a
triple of core's `OptionT` lift of the necessary reading from `True`. -/
theorem OptionT.wp_iff_triple (mx : OptionT (OracleComp spec) α) (post : α → Prop) :
    Std.WP.wp mx post (fun _ => False, Lean.Order.bot) ↔
      ⦃ True ⦄ mx ⦃ post; (fun _ => False, Lean.Order.bot) ⦄ := by
  rw [Triple.iff]
  exact ⟨fun h _ => h, fun h => h trivial⟩

/-- A structural weakest precondition of an exceptional computation, with exceptions forbidden,
is a triple of core's `ExceptT` lift of the necessary reading from `True`. -/
theorem ExceptT.wp_iff_triple {E : Type} (mx : ExceptT E (OracleComp spec) α)
    (post : α → Prop) :
    Std.WP.wp mx post (fun _ => False, Lean.Order.bot) ↔
      ⦃ True ⦄ mx ⦃ post; (fun _ => False, Lean.Order.bot) ⦄ := by
  rw [Triple.iff]
  exact ⟨fun h _ => h, fun h => h trivial⟩

variable [OracleSpec.UniformAnswerMeasure spec]

/-- Under uniform answers, an event of an optional computation has probability one exactly when
every run succeeds with an output satisfying it: a triple of core's `OptionT` lift of the
necessary reading from `True`, with failure forbidden. -/
theorem OptionT.prEvent_eq_one_iff_triple (mx : OptionT (OracleComp spec) α) (p : α → Prop) :
    Pr{let x ← mx}[p x] = 1 ↔ ⦃ True ⦄ mx ⦃ p; (fun _ => False, Lean.Order.bot) ⦄ := by
  rw [_root_.OptionT.prEvent_eq_run, OracleComp.Necessary.prEvent_eq_one_iff_triple, Triple.iff,
    Triple.iff]
  simp only [Std.WP.OptionT.wp_apply_eq]
  exact imp_congr_right fun _ => Iff.of_eq (congrArg (fun q => Std.WP.wp mx.run q Lean.Order.bot)
    (funext fun o => by cases o <;> rfl))

/-- Under uniform answers, an event of an exceptional computation has probability one exactly
when every run returns an output satisfying it: a triple of core's `ExceptT` lift of the
necessary reading from `True`, with exceptions forbidden. -/
theorem ExceptT.prEvent_eq_one_iff_triple {E : Type} (mx : ExceptT E (OracleComp spec) α)
    (p : α → Prop) :
    Pr{let x ← mx}[p x] = 1 ↔ ⦃ True ⦄ mx ⦃ p; (fun _ => False, Lean.Order.bot) ⦄ := by
  rw [_root_.ExceptT.prEvent_eq_run, OracleComp.Necessary.prEvent_eq_one_iff_triple, Triple.iff,
    Triple.iff]
  simp only [Std.WP.ExceptT.wp_apply_eq]
  exact imp_congr_right fun _ => Iff.of_eq (congrArg (fun q => Std.WP.wp mx.run q Lean.Order.bot)
    (funext fun r => by cases r <;> rfl))

/-- Under uniform answers, an expectation over an optional computation of an observation bounded
by `1` equal to `1` is the structural weakest precondition, with failure forbidden, of the
observation equal to `1`. -/
theorem OptionT.wp_eq_one_eq_wp (mx : OptionT (OracleComp spec) α) (g : α → ℝ≥0∞)
    (hg : ∀ a, g a ≤ 1) :
    (wp⟦mx⟧ g = 1) = Std.WP.wp mx (fun a => g a = 1) (fun _ => False, Lean.Order.bot) := by
  rw [_root_.OptionT.wp_eq_run,
    OracleComp.Necessary.wp_eq_one_eq_wp _ _ fun o => by cases o <;> simp [hg]]
  simp only [Std.WP.OptionT.wp_apply_eq]
  exact congrArg (fun q => Std.WP.wp mx.run q Lean.Order.bot)
    (funext fun o => by cases o <;> simp [Lean.Order.pushOption])

/-- Under uniform answers, an expectation over an exceptional computation of an observation
bounded by `1` equal to `1` is the structural weakest precondition, with exceptions forbidden,
of the observation equal to `1`. -/
theorem ExceptT.wp_eq_one_eq_wp {E : Type} (mx : ExceptT E (OracleComp spec) α) (g : α → ℝ≥0∞)
    (hg : ∀ a, g a ≤ 1) :
    (wp⟦mx⟧ g = 1) = Std.WP.wp mx (fun a => g a = 1) (fun _ => False, Lean.Order.bot) := by
  rw [_root_.ExceptT.wp_eq_run,
    OracleComp.Necessary.wp_eq_one_eq_wp _ _ fun r => by cases r <;> simp [hg, Except.toOption]]
  simp only [Std.WP.ExceptT.wp_apply_eq]
  exact congrArg (fun q => Std.WP.wp mx.run q Lean.Order.bot)
    (funext fun r => by cases r <;> simp [Lean.Order.pushExcept, Except.toOption])

end OracleComp.Necessary

/-! ## What each reading means, against the others

The readings of one statement agree: the lower-bound triple from `1` of an event's indicator,
the upper-bound triple from `0` of the indicator of its negation, and the necessary triple of the
event are one statement, and a necessary triple gives a possible one wherever some outcome is
possible. A scope selects one carrier per program type, so each side names its reading's
instance. -/

namespace OracleComp.Necessary

open Std.WP OrderDual

variable {ι : Type u} {spec : OracleSpec.{u, 0} ι} [OracleSpec.UniformAnswerMeasure spec]
  {α : Type}

/-- Under uniform answers, the lower-bound triple from `1` of an event's indicator is the
necessary triple of the event. -/
theorem triple_one_iff_triple (oa : OracleComp spec α) (p : α → Prop) :
    @Std.WP.Triple ℝ≥0∞ EStack⟨⟩ (OracleComp spec α) α _ _ oa OracleComp.Lower.wpInst 1
      (predInd p) Lean.Order.bot ↔ ⦃ True ⦄ oa ⦃ p ⦄ := by
  rw [← OracleComp.ProgramLogic.le_prEvent_iff_triple, ← prEvent_eq_one_iff_triple]
  exact ⟨fun h => le_antisymm (prEvent_le_one _) h, fun h => h.ge⟩

/-- Under uniform answers, the upper-bound triple from `0` of the indicator of an event's
negation is the necessary triple of the event. -/
theorem triple_zero_not_iff_triple (oa : OracleComp spec α) (p : α → Prop) :
    @Std.WP.Triple ℝ≥0∞ᵒᵈ EStack⟨⟩ᵒᵈ (OracleComp spec α) α _ _ oa OracleComp.Upper.wpInst
      (toDual 0) (fun x => toDual (propInd (¬ p x))) Lean.Order.bot ↔ ⦃ True ⦄ oa ⦃ p ⦄ := by
  rw [← OracleComp.Upper.wp_le_iff_triple, nonpos_iff_eq_zero,
    show wp⟦oa⟧ (fun x => propInd (¬ p x)) = Pr{let x ← oa}[¬ p x] from rfl,
    prEvent_eq_zero_iff_triple, Triple.iff, Triple.iff]
  simp only [not_not]

end OracleComp.Necessary

namespace OracleComp.Possible

open Std.WP

variable {ι : Type u} {spec : OracleSpec ι} {α : Type}

/-- A necessary triple from `True` gives a possible one wherever some outcome is possible. -/
theorem triple_of_necessary (oa : OracleComp spec α) (p : α → Prop)
    (hne : (support oa).Nonempty)
    (h : @Std.WP.Triple Prop EStack⟨⟩ (OracleComp spec α) α _ _ oa
      (@Std.WP.instWPOfWPMonad _ _ _ _ _ _ _ OracleComp.Necessary.instWP) True p
      Lean.Order.bot) :
    ⦃ True ⦄ oa ⦃ p ⦄ := by
  obtain ⟨hle⟩ := h
  obtain ⟨x, hx⟩ := hne
  exact ⟨fun _ => ⟨x, hx, hle trivial x hx⟩⟩

end OracleComp.Possible
