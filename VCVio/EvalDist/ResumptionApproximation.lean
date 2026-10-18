/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module
public import VCVio.EvalDist.ResumptionCost
public import ToMathlib.MeasureTheory.Measure.TotalVariation.Submeasure
public import ToMathlib.Probability.Kernel.TotalVariation

/-!
# Exact returned laws from bounded approximations

A bounded successful-output measure is below the unbounded returned law. Its total variation
error is bounded by the explicit cutoff mass, including after any subprobability kernel.
This allows exact sampler laws to be obtained from arbitrarily accurate capped executions
without conditioning away timeout or silently renormalizing a partial result.
-/

public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace PFunctor.Resumption

variable {P : PFunctor} [∀ a, MeasurableSpace (P.B a)] [P.AnswerMeasure]
  [∀ a, DiscreteMeasurableSpace (P.B a)] {β : Type*} [MeasurableSpace β]

/-- The event variation error of a bounded returned law is at most its cutoff probability. -/
theorem etvDist_outputMeasure_returnedMeasure_le (computation : Resumption P β) (fuel : ℕ) :
    (outputMeasure fuel computation).etvDist (returnedMeasure computation) ≤
      truncateMeasure fuel computation {none} := by
  have : IsSubprobabilityMeasure (outputMeasure fuel computation) :=
    ⟨outputMeasure_apply_univ_le_one fuel computation⟩
  rw [Measure.etvDist_eq_sub_univ_of_le (outputMeasure_le_returnedMeasure fuel computation)]
  apply tsub_le_iff_right.mpr
  rw [add_comm, outputMeasure_add_cutoff]
  exact returnedMeasure_apply_univ_le_one computation

/-- A measurable continuation cannot amplify the cutoff error, including a private-state
reconstruction kernel. -/
theorem etvDist_bind_outputMeasure_returnedMeasure_le {γ : Type*} [MeasurableSpace γ]
    (computation : Resumption P β) (fuel : ℕ) (continuation : Kernel β γ)
    [IsSubprobabilityKernel continuation] :
    ((outputMeasure fuel computation).bind continuation).etvDist
      ((returnedMeasure computation).bind continuation) ≤
        truncateMeasure fuel computation {none} :=
  (Measure.etvDist_bind_le _ _ continuation continuation.measurable).trans
    (etvDist_outputMeasure_returnedMeasure_le computation fuel)

end PFunctor.Resumption
