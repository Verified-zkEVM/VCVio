/-
Copyright (c) 2026 VCVio Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import VCVio.OracleComp.ProbComp
public import VCVio.OracleComp.EvalDist.MeasureSpec
public import VCVio.EvalDist.ProbabilityNotation
public import ToMathlib.MeasureTheory.Measure.Bounds
public import ToMathlib.Probability.UniformOn

/-!
# Measure semantics for finite-range sampling

The finite-range oracle is interpreted by a native uniform measure. Its event law is
stated directly in the measure-backed probability notation and exposes exact finite
cardinality only when the event predicate is decidable.
-/

public section

open MeasureTheory ProbabilityTheory

namespace ProbComp

/-- A finite-range draw denotes the uniform measure chosen for its oracle response. -/
@[simp]
theorem evalDist_uniformFin (n : ℕ) :
    𝒟[uniformFin n] = uniformOn Set.univ := by
  change 𝒟[(unifSpec.query n : OracleComp unifSpec (Fin (n + 1)))] = _
  exact OracleComp.evalDist_query_uniform n

/-- Integrating a finite-range draw is a finite average, including for infinite integrands. -/
theorem lintegral_evalDist_uniformFin (n : ℕ) (f : Fin (n + 1) → ENNReal) :
    ∫⁻ i, f i ∂𝒟[uniformFin n] = (∑ i, f i) / (n + 1) := by
  rw [evalDist_uniformFin, lintegral_uniformOn_univ]
  simp

/-- A decidable event on a finite-range draw has its normalized cardinality. -/
theorem prEvent_uniformFin (n : ℕ) (p : Fin (n + 1) → Prop) [DecidablePred p] :
    Pr{let x ← uniformFin n}[p x] =
      ((Finset.univ.filter p).card : ENNReal) / (n + 1) := by
  rw [prEvent_eq_evalDist_of_discrete, evalDist_uniformFin,
    uniformOn_univ_apply_setOf]
  simp

end ProbComp
