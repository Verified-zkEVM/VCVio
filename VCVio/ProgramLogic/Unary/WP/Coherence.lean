/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import VCVio.ProgramLogic.Unary.WP.Probabilistic
public import VCVio.ProgramLogic.Unary.WP.Qualitative
public import VCVio.ProgramLogic.Unary.WP.Angelic

/-!
# Coherence of unary assertion carriers

These lemmas relate structural predicates, probability-valued assertions, and quantitative
expectations. The probability-one equivalence uses `IsUniformMeasureSpec`; it is not a generic
identification of measure-theoretic almost-sure behavior with structural reachability.

The statements expose the underlying algebras, so several carrier instances need not be
active in the same scope. Forgetting the probability bound uses `wp_restrictIic_val`.

The bridges in `OracleComp.Qualitative` state events of probability one or zero as structural
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
variable [OracleSpec.IsUniformMeasureSpec spec]
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

namespace OracleComp.Qualitative

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
theorem prEvent_eq_one_of_triple [OracleSpec.IsMeasureSpec spec] {mx : OracleComp spec α}
    {p : α → Prop} (h : ⦃ True ⦄ mx ⦃ p ⦄) : Pr{let x ← mx}[p x] = 1 :=
  prEvent_eq_one_of_forall_mem_support mx p (h.le_wp trivial)

variable [OracleSpec.IsUniformMeasureSpec spec]

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

end OracleComp.Qualitative

/-! ## Nested expectations equal to one -/

namespace OracleComp.Qualitative

open Std.WP

section fullSupport

variable {ι : Type u} {spec : OracleSpec.{u, 0} ι} [OracleSpec.IsMeasureSpec spec] {α : Type}

/-- When every answer of every query has positive mass, an expectation of an observation bounded
by `1` equals `1` exactly when the observation equals `1` at every possible output. -/
theorem wp_eq_one_iff_of_fullSupport
    (hfull : ∀ t (u : spec.Range t), 0 < OracleSpec.IsMeasureSpec.toMeasure t {u})
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
    exact (OracleComp.Angelic.pos_wp_iff_of_fullSupport hfull mx _).2
      ⟨a, ha, tsub_pos_of_lt (lt_of_le_of_ne (hg a) hne)⟩
  · intro h
    rw [← ExpectationWP.wp_const_of_oracle mx 1]
    exact wp_congr_of_support mx h

/-- When every answer of every query has positive mass, an expectation of an observation bounded
by `1` equals `1` exactly when a structural triple from `True` holds. -/
theorem wp_eq_one_iff_triple_of_fullSupport
    (hfull : ∀ t (u : spec.Range t), 0 < OracleSpec.IsMeasureSpec.toMeasure t {u})
    (mx : OracleComp spec α) (g : α → ℝ≥0∞) (hg : ∀ a, g a ≤ 1) :
    wp⟦mx⟧ g = 1 ↔ ⦃ True ⦄ mx ⦃ fun a => g a = 1 ⦄ := by
  rw [wp_eq_one_iff_of_fullSupport hfull mx g hg, forall_mem_support_iff_triple]

end fullSupport

variable {ι : Type u} {spec : OracleSpec.{u, 0} ι} [OracleSpec.IsUniformMeasureSpec spec]
  {α : Type}

/-- Under uniform answers, an expectation of an observation bounded by `1` equal to `1` is the
structural weakest precondition of the observation equal to `1`. As an equation of propositions
it rewrites the nested expectations of an event's normal form. -/
theorem wp_eq_one_eq_wp (mx : OracleComp spec α) (g : α → ℝ≥0∞) (hg : ∀ a, g a ≤ 1) :
    (wp⟦mx⟧ g = 1) = Std.WP.wp mx (fun a => g a = 1) Lean.Order.bot :=
  propext (wp_eq_one_iff_of_fullSupport
    (fun t u => OracleSpec.IsUniformMeasureSpec.toMeasure_singleton_pos t u) mx g hg)

end OracleComp.Qualitative
