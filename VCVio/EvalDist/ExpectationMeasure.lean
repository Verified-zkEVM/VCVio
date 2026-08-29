/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import VCVio.EvalDist.Expectation
public import ToMathlib.MeasureTheory.Measure.Option
public import ToMathlib.Probability.ProbabilityMassFunction.Measure

/-!
# `expectedValue` as a Lebesgue integral

`VCVio.EvalDist.Expectation` defines `expectedValue mx g` as `∑' x, Pr[= x | mx] * g x`. This
module identifies that discrete spelling with the `lintegral` against the primary evaluation
measure `𝒟[mx]`.

`expectedValue_eq_lintegral` is an equation, so every existing `∑'`-shaped proof remains usable.
The conversion to `SPMF` is confined to proving the discrete singleton bridge; the statement and
the notation expose only `Measure`.

## What it buys

Monotone convergence, Fatou and Tonelli become available for VCVio expectations by rewriting
once. `lintegral_iSup` is recorded below as `expectedValue_iSup`, since a supremum of an
increasing sequence of functionals is the shape a fuel-indexed or loop-indexed cost argument
takes, and there is no `∑'` lemma for it in the library.

## Generality

The hypotheses are exactly those needed to identify a countable sum with an integral:
`Countable α` and a discrete measurable structure. They are what `lintegral_countable'` asks
for, and they hold for every cryptographic sample type.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

universe u v

namespace OracleComp.EvalDist

variable {α : Type u} {m : Type u → Type v} [Monad m] [MonadLiftT m SPMF]
  [MeasurableSpace α] [DiscreteMeasurableSpace α] [Countable α]

/-- The measure denoted by `mx`, as a Mathlib `Measure` on the result type.

Failure is missing mass rather than an ordinary output. -/
noncomputable def toMeasure (mx : m α) : Measure α :=
  (evalSPMF mx).toMeasure

omit [Monad m] [Countable α] in
@[simp]
theorem toMeasure_apply_singleton (mx : m α) (x : α) :
    toMeasure mx {x} = Pr[= x | mx] := by
  exact (probOutput_eq_evalSPMF_toMeasure mx x).symm

omit [Monad m] in
/-- The expected value is a Lebesgue integral against the denoted measure. -/
theorem expectedValue_eq_lintegral (mx : m α) (g : α → ℝ≥0∞) :
    expectedValue mx g = ∫⁻ x, g x ∂(toMeasure mx) := by
  rw [expectedValue_def, lintegral_countable']
  exact tsum_congr fun x => by rw [toMeasure_apply_singleton, mul_comm]

omit [Monad m] in
/-- **Monotone convergence** for VCVio expectations.

There is no `∑'`-shaped counterpart to this in the library: it is `lintegral_iSup`, reachable
only once the expectation is an integral. -/
theorem expectedValue_iSup (mx : m α) (g : ℕ → α → ℝ≥0∞) (hg : Monotone g) :
    expectedValue mx (fun x => ⨆ n, g n x) = ⨆ n, expectedValue mx (g n) := by
  simp only [expectedValue_eq_lintegral]
  exact lintegral_iSup (fun _ => Measurable.of_discrete) hg

end OracleComp.EvalDist
