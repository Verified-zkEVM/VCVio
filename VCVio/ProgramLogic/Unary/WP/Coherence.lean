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
expectations. The probability-one equivalence uses `IsUniformSpec`; it is not a generic
identification of measure-theoretic almost-sure behavior with structural reachability.

The statements expose the underlying algebras, so several carrier instances need not be
active in the same scope. Forgetting the probability bound uses `wp_restrictIic_val`.
-/

@[expose] public section

universe u

open ENNReal OracleComp.ProgramLogic OracleComp.ProgramLogic.PropLogic

namespace OracleComp.WP.Coherence

variable {ι : Type u} {spec : OracleSpec ι}
variable [IsUniformSpec spec]
variable {α : Type}

/-! ## Probabilistic ↔ Quantitative

The probabilistic `Std.Internal.Do.wp` agrees with the quantitative `MAlgOrdered.wp`
under `Subtype.val`; that statement lives in `…/WP/Probabilistic.lean`
as `OracleComp.Probabilistic.wp_val_eq_mAlgOrdered_wp`. We do not restate
it here because pulling `OracleComp.Probabilistic.instWP_prob` into scope
to talk about `Std.Internal.Do.wp` requires `open OracleComp.Probabilistic`,
which then occludes the qualitative tier discussed below. -/

/-! ## Qualitative ↔ Probabilistic (support-vs-expectation bridge)

For an `OracleComp` (which has a canonical `MonadLiftT … PMF`, so total
probability is exactly `1`), the support-based `Prop`-valued `wp` agrees
with "the probabilistic `wp` on the indicator post equals `1`". -/

/-- Qualitative ↔ Probabilistic coherence: a `Prop`-valued post is
satisfied almost-surely iff its indicator post has probabilistic `wp`
equal to `1`.

The `[DecidablePred post]` requirement is intrinsic to the indicator
construction; consumers without classical-decidable predicates can
`Classical.dec`-coerce on call sites or reformulate via
`probEvent_eq_wp_indicator` directly. -/
theorem wp_qual_iff_wp_prob_indicator_eq_one
    (oa : OracleComp spec α) (post : α → Prop) [DecidablePred post] :
    MAlgOrdered.wp (m := OracleComp spec) (l := Prop) oa post ↔
      MAlgOrdered.wp (m := OracleComp spec) (l := ℝ≥0∞) oa
          (fun a => if post a then 1 else 0) = 1 := by
  rw [wp_iff_forall_support]
  change (∀ x ∈ support oa, post x) ↔
        wp oa (fun a => if post a then 1 else 0) = 1
  rw [← probEvent_eq_wp_indicator, probEvent_eq_one_iff]
  exact (and_iff_right probFailure_eq_zero).symm

/-- Convenience: the `Prob`-valued indicator-as-`wp` form of the
coherence lemma, for users who have already lifted their post to `Prob`
via `Prob.indicator`. -/
theorem wp_qual_iff_wp_prob_indicator_val_eq_one
    (oa : OracleComp spec α) (post : α → Prop) [DecidablePred post] :
    MAlgOrdered.wp (m := OracleComp spec) (l := Prop) oa post ↔
      MAlgOrdered.wp (m := OracleComp spec) (l := ℝ≥0∞) oa
          (fun a => (Prob.indicator (post a)).val) = 1 :=
  wp_qual_iff_wp_prob_indicator_eq_one oa post

end OracleComp.WP.Coherence
