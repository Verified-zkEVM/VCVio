/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import Mathlib.Probability.ProbabilityMassFunction.Monad
public import Mathlib.MeasureTheory.Measure.GiryMonad
public import Mathlib.MeasureTheory.Integral.Lebesgue.Countable

/-!
# `PMF.toMeasure` is a monad morphism

Mathlib records two thirds of this: `PMF.toMeasure_pure` sends `PMF.pure` to `Measure.dirac`,
and `PMF.toMeasure_map` commutes `toMeasure` with `map`. For `bind` it provides only the
applied form, `PMF.toMeasure_bind_apply`, which evaluates `(p.bind f).toMeasure` at a
measurable set as a `tsum`.

`PMF.toMeasure_bind` below is the measure-level equality. It is what a monad-morphism
argument needs — in particular, transporting a proof about a `PMF`-valued denotation to the
corresponding `Measure`-valued one — and it is the natural companion to the two lemmas already
upstream. It stays in `ToMathlib` during the migration and can be removed if the upstream API
acquires the same equality.

## Hypotheses

Only `[DiscreteMeasurableSpace α]` is required. The proof restricts the source measure to the
countable support of `p`, then applies `lintegral_countable`; no countability assumption on the
ambient carrier is needed.
-/

@[expose] public section

open MeasureTheory ENNReal

namespace PMF

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

/-- `PMF.toMeasure` commutes with `bind`: the measure of a bound computation is the Giry bind
of the measures.

This is the measure-level form of `PMF.toMeasure_bind_apply`, and together with
`PMF.toMeasure_pure` it says that `PMF.toMeasure` is a monad morphism from `PMF` into the Giry
monad. -/
lemma toMeasure_bind [DiscreteMeasurableSpace α]
    (p : PMF α) (f : α → PMF β) :
    (p.bind f).toMeasure = Measure.bind p.toMeasure fun a => (f a).toMeasure := by
  ext s hs
  rw [toMeasure_bind_apply _ _ _ hs,
    Measure.bind_apply hs (Measurable.of_discrete).aemeasurable]
  conv_rhs => rw [← PMF.restrict_toMeasure_support p]
  rw [lintegral_countable _ p.support_countable]
  have hind : (fun a => p a * (f a).toMeasure s)
      = p.support.indicator (fun a => p a * (f a).toMeasure s) := by
    funext a
    by_cases ha : a ∈ p.support
    · simp [ha]
    · simp [ha, (PMF.apply_eq_zero_iff p a).mpr ha]
  rw [hind, ← tsum_subtype]
  exact tsum_congr fun a => by
    rw [p.toMeasure_apply_singleton a MeasurableSet.of_discrete, mul_comm]

end PMF
