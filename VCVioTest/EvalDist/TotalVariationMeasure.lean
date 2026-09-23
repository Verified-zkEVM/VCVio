/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import VCVio.EvalDist.MeasureTVDist.Bind
public import VCVio.EvalDist.Defs.Measure.Deterministic
public import ToMathlib.MeasureTheory.MeasurableSpace.Option
public import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# Native total variation composition regressions

Real spaces retain their usual measurable structure. Conditional variation bounds use supplied
majorants, null-set changes have no cost, and lossy prefixes retain their mass. An explicit
optional abort remains distinguishable from computational failure.
-/

public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory

run_cmd do
  let env ← Lean.getEnv
  for name in [`PMF, `SPMF, `NeverFail, `EvalDistCompatible, `DiscreteEvalDistCompatible] do
    if env.contains name then
      throwError "native total variation unexpectedly imports {name}"

namespace VCVioTest.TotalVariationMeasure

example (μ ν : Measure ℝ) (f : ℝ → ENNReal) (hf : Measurable f)
    (hbound : ∀ x, f x ≤ 1) :
    ENNReal.absDiff (∫⁻ x, f x ∂μ) (∫⁻ x, f x ∂ν) ≤ μ.etvDist ν :=
  Measure.absDiff_lintegral_le_etvDist μ ν f hf hbound

/-- Measurable postprocessing of continuous measures contracts variation. -/
example (μ ν : Measure ℝ) :
    (μ.bind (Kernel.deterministic (fun x : ℝ ↦ x + 1) (measurable_id.add_const 1))).etvDist
      (ν.bind (Kernel.deterministic (fun x : ℝ ↦ x + 1) (measurable_id.add_const 1))) ≤
      μ.etvDist ν :=
  Measure.etvDist_bind_le μ ν _ (Kernel.deterministic _ _).measurable

example (κ ξ : Kernel ℝ ℝ) (η τ : Kernel ℝ ℝ) [IsSubprobabilityKernel η]
    (r : ℝ) (bound : ℝ → ENNReal)
    (hbound : ∀ᵐ x ∂ξ r, (η x).etvDist (τ x) ≤ bound x) :
    ((η ∘ₖ κ) r).etvDist ((τ ∘ₖ ξ) r) ≤
      (κ r).etvDist (ξ r) + ∫⁻ x, bound x ∂ξ r :=
  Kernel.etvDist_comp_comp_le_add_lintegral κ ξ η τ r bound hbound

/-- The expected majorant is measurable without a measurable conditional TV function. -/
example (κ : Kernel ℝ ℝ) [IsSFiniteKernel κ]
    (bound : ℝ × ℝ → ENNReal) (hbound : Measurable bound) :
    Measurable (fun r ↦ ∫⁻ x, bound (r, x) ∂κ r) := hbound.lintegral_kernel_prod_right'

example (μ : Measure ℝ) [NullSingletonClass μ] (κ η : Kernel ℝ ℝ)
    [IsSubprobabilityKernel κ] [IsSubprobabilityKernel η]
    (h : ∀ x, x ≠ 0 → κ x = η x) : (μ.bind κ).etvDist (μ.bind η) = 0 := by
  apply nonpos_iff_eq_zero.mp
  have htv := Measure.etvDist_bind_bind_le_of_bad μ κ η κ.aemeasurable η.aemeasurable
    (measurableSet_singleton (0 : ℝ)) 0
    (Filter.Eventually.of_forall fun x hx ↦ by
      rw [h x (by simpa using hx)]
      simp)
  simpa using htv

/-- A lossy continuous prefix contributes only its actual half mass. -/
example (κ η : Kernel ℝ ℝ) (ε : ENNReal)
    (h : ∀ᵐ x ∂((1 / 2 : ENNReal) • gaussianReal 0 1), (κ x).etvDist (η x) ≤ ε) :
    (((1 / 2 : ENNReal) • gaussianReal 0 1).bind κ).etvDist
      (((1 / 2 : ENNReal) • gaussianReal 0 1).bind η) ≤ ε * (1 / 2) := by
  simpa only [lintegral_const, Measure.smul_apply, measure_univ, smul_eq_mul, mul_one] using
    Measure.etvDist_bind_bind_le_lintegral ((1 / 2 : ENNReal) • gaussianReal 0 1)
      κ η κ.aemeasurable η.aemeasurable (fun _ ↦ ε) h

/-- Returning an abort is distinct from losing the entire computation. -/
example : (Measure.dirac (none : Option ℝ)).etvDist 0 = 1 := by
  apply le_antisymm
  · exact Measure.etvDist_le_one _ _ (by simp) (by simp)
  · simpa [ENNReal.absDiff] using
      Measure.absDiff_apply_le_etvDist (Measure.dirac (none : Option ℝ)) 0
        (measurableSet_singleton none)

example (mx my : Option ℝ) :
    measureETVDist (mx >>= fun x ↦ some (x + 1)) (my >>= fun x ↦ some (x + 1)) ≤
      measureETVDist mx my := by
  apply measureETVDist_bind_le
  simp only [Option.evalDist_some]
  exact Measure.measurable_dirac.comp (measurable_id.add_const 1)

end VCVioTest.TotalVariationMeasure
