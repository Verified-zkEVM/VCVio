/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-!
# The Renyi moment generating function of a pair of measures

Mathlib states Kullback-Leibler for measures (`InformationTheory.klDiv`) but has no Renyi
divergence at all, so this is local development rather than a wrapper. It follows `klDiv`'s shape
deliberately: `ℝ≥0∞`-valued, defined by an integral of a function of `Measure.rnDeriv`, and
guarded by absolute continuity.

## Why the guard

`∫⁻ x, (∂μ/∂ν x) ^ a ∂ν` integrates against `ν`, so it cannot see a set where `ν` vanishes and
`μ` does not — it would report a finite value for a pair at infinite divergence. The `μ ≪ ν`
guard restores that, and it is what makes `renyiMGF_toMeasure` below an equality rather than an
inequality. Mathlib's `klDiv` carries the same guard for the same reason.

## The discrete theory

`ToMathlib.Probability.Divergence.RenyiDiscrete` identifies this with the countably supported
formula, so that development becomes a corollary of this one rather than a parallel copy. This
module is deliberately free of any dependence on that layer.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace InformationTheory

variable {α : Type*} [MeasurableSpace α]

open scoped Classical in
/-- The Renyi moment generating function of order `a`, also called the Hellinger integral.

For `a > 1` this is `∑' x, p x ^ a * q x ^ (1 - a)` in the countably supported case; see
`ToMathlib.Probability.Divergence.RenyiDiscrete`. -/
noncomputable def renyiMGF (a : ℝ) (μ ν : Measure α) : ℝ≥0∞ :=
  if μ ≪ ν then ∫⁻ x, (μ.rnDeriv ν x) ^ a ∂ν else ⊤

open scoped Classical in
theorem renyiMGF_of_ac {a : ℝ} {μ ν : Measure α} (h : μ ≪ ν) :
    renyiMGF a μ ν = ∫⁻ x, (μ.rnDeriv ν x) ^ a ∂ν := if_pos h

open scoped Classical in
@[simp]
theorem renyiMGF_of_not_ac {a : ℝ} {μ ν : Measure α} (h : ¬ μ ≪ ν) :
    renyiMGF a μ ν = ⊤ := if_neg h

/-- A measure has Renyi MGF one against itself. -/
@[simp]
theorem renyiMGF_self (a : ℝ) (μ : Measure α) [IsProbabilityMeasure μ] :
    renyiMGF a μ μ = 1 := by
  rw [renyiMGF_of_ac (Measure.AbsolutelyContinuous.refl μ)]
  have h : ∫⁻ x, (μ.rnDeriv μ x) ^ a ∂μ = ∫⁻ _, 1 ∂μ := by
    refine lintegral_congr_ae ?_
    filter_upwards [μ.rnDeriv_self] with x hx
    simp [hx]
  rw [h]
  simp

end InformationTheory
