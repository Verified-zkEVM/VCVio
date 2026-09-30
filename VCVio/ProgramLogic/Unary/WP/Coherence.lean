/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import VCVio.ProgramLogic.Unary.WP.Probabilistic
public import VCVio.ProgramLogic.Unary.WP.Qualitative

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
`prEvent_eq_one_of_triple`, needs no uniformity.
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
open scoped OracleComp.Qualitative

variable {ι : Type u} {spec : OracleSpec ι} {α : Type}

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
