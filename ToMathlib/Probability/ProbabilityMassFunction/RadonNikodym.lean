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

## Countability is not required

A `PMF` has countable support whatever its carrier, so nothing here needs `[Countable α]` — only a
measurable structure in which the relevant sets are measurable. That matters: the `SPMF` layer
instantiates these results at `Option α'` for a completely arbitrary `α'`, where no countability
instance is available, so a countable-carrier version would not reach the callers that need it.

The route is `withDensity` rather than counting measure for the same reason. Counting measure is
`SigmaFinite` only on a countable carrier, whereas `q.toMeasure` is a probability measure and so is
σ-finite always.

## The absolute-continuity hypothesis

`rnDeriv_toMeasure` asks for `p.toMeasure ≪ q.toMeasure`. Where `q` vanishes the ratio is not
determined by the derivative, and absolute continuity is what rules those points out — the same
reason a divergence defined by an integral against `q` must carry the guard to see them at all.
-/

@[expose] public section

open MeasureTheory

namespace PMF

variable {α : Type*} [MeasurableSpace α] [DiscreteMeasurableSpace α]

/-- Absolute continuity of `PMF` measures is inclusion of supports. -/
theorem absolutelyContinuous_toMeasure_iff (p q : PMF α) :
    p.toMeasure ≪ q.toMeasure ↔ ∀ x, q x = 0 → p x = 0 := by
  constructor
  · intro h x hx
    have hq : q.toMeasure {x} = 0 := by
      rw [PMF.toMeasure_apply_singleton _ _ MeasurableSet.of_discrete]; exact hx
    have := h hq
    rwa [PMF.toMeasure_apply_singleton _ _ MeasurableSet.of_discrete] at this
  · intro h
    refine Measure.AbsolutelyContinuous.mk fun s hs hzero => ?_
    rw [PMF.toMeasure_apply_eq_zero_iff _ hs] at hzero ⊢
    exact Set.disjoint_left.mpr fun x hxp hxs =>
      Set.disjoint_left.mp hzero (fun hq => hxp (h x hq)) hxs

/-- Under absolute continuity, `p` is `q` carrying the pointwise ratio as a density.

Only the countable set `q.support` carries any mass, which is what lets this avoid a countability
hypothesis on `α`. -/
theorem toMeasure_eq_withDensity (p q : PMF α) (hpq : p.toMeasure ≪ q.toMeasure) :
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
theorem rnDeriv_toMeasure (p q : PMF α) (hpq : p.toMeasure ≪ q.toMeasure) :
    p.toMeasure.rnDeriv q.toMeasure =ᵐ[q.toMeasure] fun x => p x / q x := by
  conv_lhs => rw [← toMeasure_eq_withDensity p q hpq]
  exact Measure.rnDeriv_withDensity _ Measurable.of_discrete

end PMF
