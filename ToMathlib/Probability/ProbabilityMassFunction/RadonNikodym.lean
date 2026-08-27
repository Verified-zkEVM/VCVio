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
pointwise masses. `PMF.rnDeriv_toMeasure` is the equation between the two: on a countable
discrete space the derivative of one `PMF`'s measure against another's is the pointwise ratio.

It is what lets a measure-level divergence result be read back as the `tsum` formula an existing
`PMF` proof is stated in, and conversely.

## Route

`p.toMeasure` is the counting measure carrying `p` as a density, so its derivative against
`Measure.count` is `p` itself (`Measure.rnDeriv_withDensity`). Both measures are absolutely
continuous with respect to counting measure, so `Measure.rnDeriv_eq_div` turns the derivative of
one against the other into the ratio of those densities.

The `=ᵐ` is not incidental. Where `q x = 0` the ratio is not determined by the derivative, and
the almost-everywhere qualifier is exactly what excludes those points — which is also why a
divergence defined by an integral against `q` must carry an absolute-continuity guard to see
them at all.
-/

@[expose] public section

open MeasureTheory

namespace PMF

variable {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]

/-- A `PMF`'s measure is the counting measure with the mass function as its density. -/
theorem toMeasure_eq_withDensity_count (p : PMF α) :
    p.toMeasure = Measure.count.withDensity p := by
  ext s hs
  rw [PMF.toMeasure_apply_eq_tsum, withDensity_apply _ hs, ← lintegral_indicator hs,
    lintegral_count]

omit [MeasurableSingletonClass α] in
/-- Only the empty set is null for counting measure, so every `PMF` measure is dominated by it. -/
theorem absolutelyContinuous_count (p : PMF α) : p.toMeasure ≪ Measure.count :=
  Measure.AbsolutelyContinuous.mk fun s _ h => by
    simp [Measure.count_eq_zero_iff.mp h]

variable [Countable α]

/-- The density of a `PMF` measure against counting measure is the mass function. -/
theorem rnDeriv_toMeasure_count (p : PMF α) :
    p.toMeasure.rnDeriv Measure.count =ᵐ[Measure.count] p := by
  rw [toMeasure_eq_withDensity_count]
  exact Measure.rnDeriv_withDensity _ (measurable_of_countable _)

/-- **The pointwise Radon-Nikodym derivative of one `PMF` against another.**

This is the bridge between a measure-level divergence and its `tsum` formula. -/
theorem rnDeriv_toMeasure (p q : PMF α) :
    p.toMeasure.rnDeriv q.toMeasure =ᵐ[q.toMeasure] fun x => p x / q x := by
  filter_upwards [Measure.rnDeriv_eq_div (absolutelyContinuous_count p)
      (absolutelyContinuous_count q),
    absolutelyContinuous_count q (rnDeriv_toMeasure_count p),
    absolutelyContinuous_count q (rnDeriv_toMeasure_count q)] with x h1 h2 h3
  rw [h1, h2, h3]

omit [Countable α] in
/-- Absolute continuity of `PMF` measures is inclusion of supports. -/
theorem absolutelyContinuous_toMeasure_iff (p q : PMF α) :
    p.toMeasure ≪ q.toMeasure ↔ ∀ x, q x = 0 → p x = 0 := by
  constructor
  · intro h x hx
    have : q.toMeasure {x} = 0 := by
      rw [PMF.toMeasure_apply_singleton _ _ (MeasurableSet.singleton x)]; exact hx
    have := h this
    rwa [PMF.toMeasure_apply_singleton _ _ (MeasurableSet.singleton x)] at this
  · intro h
    refine Measure.AbsolutelyContinuous.mk fun s hs hzero => ?_
    rw [PMF.toMeasure_apply_eq_zero_iff _ hs] at hzero ⊢
    exact Set.disjoint_left.mpr fun x hxp hxs =>
      Set.disjoint_left.mp hzero (fun hq => hxp (h x hq)) hxs

end PMF
