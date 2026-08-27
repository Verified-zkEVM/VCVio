/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import Mathlib.Probability.ProbabilityMassFunction.Basic
public import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
public import Mathlib.MeasureTheory.Integral.Lebesgue.Countable

/-!
# Radon-Nikodym derivatives of `PMF.toMeasure`

Mathlib's divergences are stated through `Measure.rnDeriv`, while VCVio's are stated as sums of
pointwise masses. `PMF.rnDeriv_toMeasure` is the equation between the two: the derivative of one
`PMF`'s measure against another's is the pointwise ratio.

It is what lets a measure-level divergence result be read back as the `tsum` formula an existing
`PMF` proof is stated in, and conversely.

## Two useful forms

The unrestricted bridge is stated on a countable carrier with measurable singletons. This is the
legacy API and applies, for example, to ordinary Borel spaces when the carrier is countable.

For callers such as `SPMF` that work over an arbitrary carrier, the `_of_ac` form removes the
carrier-countability assumption by restricting the integral to the countable support of `q`. It
uses `q.toMeasure` itself as the dominating measure and therefore carries an explicit absolute-
continuity hypothesis.

## The absolute-continuity hypothesis

The unrestricted theorem is an almost-everywhere equality and does not need absolute continuity:
points where `q` vanishes are already invisible to `=ᵐ[q.toMeasure]`. The arbitrary-carrier
`rnDeriv_toMeasure_of_ac` uses absolute continuity only because its supporting `withDensity`
factorization does.
-/

@[expose] public section

open MeasureTheory

namespace PMF

variable {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]

/-- A `PMF`'s measure is counting measure with the mass function as density. -/
theorem toMeasure_eq_withDensity_count (p : PMF α) :
    p.toMeasure = Measure.count.withDensity p := by
  ext s hs
  rw [PMF.toMeasure_apply_eq_tsum, withDensity_apply _ hs, ← lintegral_indicator hs,
    lintegral_count]

omit [MeasurableSingletonClass α] in
/-- Every `PMF` measure is dominated by counting measure. -/
theorem absolutelyContinuous_count (p : PMF α) : p.toMeasure ≪ Measure.count :=
  Measure.AbsolutelyContinuous.mk fun s _ h => by
    simp [Measure.count_eq_zero_iff.mp h]

section Countable

variable [Countable α]

/-- The density of a `PMF` measure against counting measure is its mass function. -/
theorem rnDeriv_toMeasure_count (p : PMF α) :
    p.toMeasure.rnDeriv Measure.count =ᵐ[Measure.count] p := by
  rw [toMeasure_eq_withDensity_count]
  exact Measure.rnDeriv_withDensity _ (measurable_of_countable _)

/-- **The pointwise Radon--Nikodym derivative of one `PMF` against another.** -/
theorem rnDeriv_toMeasure (p q : PMF α) :
    p.toMeasure.rnDeriv q.toMeasure =ᵐ[q.toMeasure] fun x => p x / q x := by
  filter_upwards [Measure.rnDeriv_eq_div (absolutelyContinuous_count p)
      (absolutelyContinuous_count q),
    absolutelyContinuous_count q (rnDeriv_toMeasure_count p),
    absolutelyContinuous_count q (rnDeriv_toMeasure_count q)] with x h1 h2 h3
  rw [h1, h2, h3]

end Countable

/-- Absolute continuity of `PMF` measures is inclusion of supports. -/
theorem absolutelyContinuous_toMeasure_iff (p q : PMF α) :
    p.toMeasure ≪ q.toMeasure ↔ ∀ x, q x = 0 → p x = 0 := by
  constructor
  · intro h x hx
    have hq : q.toMeasure {x} = 0 := by
      rw [PMF.toMeasure_apply_singleton _ _ (MeasurableSet.singleton x)]; exact hx
    have := h hq
    rwa [PMF.toMeasure_apply_singleton _ _ (MeasurableSet.singleton x)] at this
  · intro h
    refine Measure.AbsolutelyContinuous.mk fun s hs hzero => ?_
    rw [PMF.toMeasure_apply_eq_zero_iff _ hs] at hzero ⊢
    exact Set.disjoint_left.mpr fun x hxp hxs =>
      Set.disjoint_left.mp hzero (fun hq => hxp (h x hq)) hxs

section Discrete

variable [DiscreteMeasurableSpace α]

/-- Under absolute continuity, `p` is `q` carrying the pointwise ratio as a density.

Only the countable set `q.support` carries any mass, which is what lets this avoid a countability
hypothesis on `α`. -/
theorem toMeasure_eq_withDensity_of_ac (p q : PMF α) (hpq : p.toMeasure ≪ q.toMeasure) :
    q.toMeasure.withDensity (fun x => p x / q x) = p.toMeasure := by
  have hsupp : ∀ x, q x = 0 → p x = 0 := (absolutelyContinuous_toMeasure_iff p q).mp hpq
  ext s _
  rw [withDensity_apply _ MeasurableSet.of_discrete, PMF.toMeasure_apply_eq_tsum,
    ← PMF.restrict_toMeasure_support q, Measure.restrict_restrict MeasurableSet.of_discrete,
    lintegral_countable _ (q.support_countable.mono Set.inter_subset_right)]
  have hind : s.indicator (⇑p) = (s ∩ q.support).indicator (⇑p) := by
    funext x
    by_cases hx : x ∈ s
    · by_cases hq : x ∈ q.support
      · simp [hx, hq]
      · simp [hx, hq, hsupp x (by simpa [PMF.mem_support_iff] using hq)]
    · simp [hx]
  rw [hind, ← tsum_subtype]
  refine tsum_congr fun x => ?_
  rw [PMF.toMeasure_apply_singleton _ _ MeasurableSet.of_discrete]
  exact ENNReal.div_mul_cancel (by simpa [PMF.mem_support_iff] using x.2.2) (PMF.apply_ne_top q x)

/-- **The pointwise Radon-Nikodym derivative of one `PMF` against another.**

This is the bridge between a measure-level divergence and its `tsum` formula. -/
theorem rnDeriv_toMeasure_of_ac (p q : PMF α) (hpq : p.toMeasure ≪ q.toMeasure) :
    p.toMeasure.rnDeriv q.toMeasure =ᵐ[q.toMeasure] fun x => p x / q x := by
  conv_lhs => rw [← toMeasure_eq_withDensity_of_ac p q hpq]
  exact Measure.rnDeriv_withDensity _ Measurable.of_discrete

end Discrete

end PMF
