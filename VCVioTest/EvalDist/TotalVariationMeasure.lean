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
# Total variation composition regressions

Real spaces retain their usual measurable structure, under which distinct points still give
Dirac measures at total variation one. Conditional variation bounds use supplied
majorants, null-set changes have no cost, and lossy prefixes retain their mass. An explicit
optional abort remains distinguishable from computational failure.
-/

public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory

run_cmd do
  let env ← Lean.getEnv
  if env.contains `PMF then
    throwError "total variation unexpectedly imports PMF"

namespace VCVioTest.TotalVariationMeasure

example (μ ν : Measure ℝ) (f : ℝ → ENNReal) (hf : Measurable f)
    (hbound : ∀ x, f x ≤ 1) :
    ENNReal.absDiff (∫⁻ x, f x ∂μ) (∫⁻ x, f x ∂ν) ≤ μ.statEDist ν :=
  Measure.absDiff_lintegral_le_statEDist μ ν f hf hbound

/-- Measurable postprocessing of continuous measures contracts variation. -/
example (μ ν : Measure ℝ) :
    (μ.bind (Kernel.deterministic (fun x : ℝ ↦ x + 1) (measurable_id.add_const 1))).statEDist
      (ν.bind (Kernel.deterministic (fun x : ℝ ↦ x + 1) (measurable_id.add_const 1))) ≤
      μ.statEDist ν :=
  Measure.statEDist_bind_le μ ν _ (Kernel.deterministic _ _).measurable

example (κ ξ : Kernel ℝ ℝ) (η τ : Kernel ℝ ℝ) [IsSubprobabilityKernel η]
    (r : ℝ) (bound : ℝ → ENNReal)
    (hbound : ∀ᵐ x ∂ξ r, (η x).statEDist (τ x) ≤ bound x) :
    ((η ∘ₖ κ) r).statEDist ((τ ∘ₖ ξ) r) ≤
      (κ r).statEDist (ξ r) + ∫⁻ x, bound x ∂ξ r :=
  Kernel.statEDist_comp_comp_le_add_lintegral κ ξ η τ r bound hbound

/-- The expected majorant is measurable without a measurable conditional TV function. -/
example (κ : Kernel ℝ ℝ) [IsSFiniteKernel κ]
    (bound : ℝ × ℝ → ENNReal) (hbound : Measurable bound) :
    Measurable (fun r ↦ ∫⁻ x, bound (r, x) ∂κ r) := hbound.lintegral_kernel_prod_right'

example (μ : Measure ℝ) [NullSingletonClass μ] (κ η : Kernel ℝ ℝ)
    [IsSubprobabilityKernel κ] [IsSubprobabilityKernel η]
    (h : ∀ x, x ≠ 0 → κ x = η x) : (μ.bind κ).statEDist (μ.bind η) = 0 := by
  apply nonpos_iff_eq_zero.mp
  have htv := Measure.statEDist_bind_bind_le_of_bad μ κ η κ.aemeasurable η.aemeasurable
    (measurableSet_singleton (0 : ℝ)) 0
    (Filter.Eventually.of_forall fun x hx ↦ by
      rw [h x (by simpa using hx)]
      simp)
  simpa using htv

/-- A lossy continuous prefix contributes only its actual half mass. -/
example (κ η : Kernel ℝ ℝ) (ε : ENNReal)
    (h : ∀ᵐ x ∂((1 / 2 : ENNReal) • gaussianReal 0 1), (κ x).statEDist (η x) ≤ ε) :
    (((1 / 2 : ENNReal) • gaussianReal 0 1).bind κ).statEDist
      (((1 / 2 : ENNReal) • gaussianReal 0 1).bind η) ≤ ε * (1 / 2) := by
  simpa only [lintegral_const, Measure.smul_apply, measure_univ, smul_eq_mul, mul_one] using
    Measure.statEDist_bind_bind_le_lintegral ((1 / 2 : ENNReal) • gaussianReal 0 1)
      κ η κ.aemeasurable η.aemeasurable (fun _ ↦ ε) h

/-- Dirac measures at distinct reals are at total variation one under the Borel σ-algebra. -/
example : (Measure.dirac (0 : ℝ)).statEDist (Measure.dirac 1) = 1 :=
  Measure.statEDist_dirac_dirac_of_ne (by norm_num)

example : (Measure.dirac (0 : ℝ)).statDist (Measure.dirac 1) = 1 :=
  Measure.statDist_dirac_dirac_of_ne (by norm_num)

/-- Returning an abort is distinct from losing the entire computation. -/
example : (Measure.dirac (none : Option ℝ)).statEDist 0 = 1 := by
  apply le_antisymm
  · exact Measure.statEDist_le_one _ _ (by simp) (by simp)
  · simpa [ENNReal.absDiff] using
      Measure.absDiff_apply_le_statEDist (Measure.dirac (none : Option ℝ)) 0
        (measurableSet_singleton none)

example (mx my : Option ℝ) :
    measureETVDist (mx >>= fun x ↦ some (x + 1)) (my >>= fun x ↦ some (x + 1)) ≤
      measureETVDist mx my := by
  apply measureETVDist_bind_le
  simp only [Option.evalDist_some]
  exact Measure.measurable_dirac.comp (measurable_id.add_const 1)

end VCVioTest.TotalVariationMeasure
