/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module
public import VCVio.EvalDist.ResumptionMeasure
public import Mathlib.Topology.Instances.ENNReal.Lemmas

/-!
# Query tails and almost-sure return

Cutoff probabilities are the strict upper tails of the number of visible queries before
return. Their sum is the extended expected query count, with infinite executions charged
infinitely and terminal readout charged zero. Vanishing cutoff probabilities imply that the
returned-output measure has full mass.
-/

public section

open MeasureTheory Filter
open scoped ENNReal Topology

namespace PFunctor.Resumption

variable {P : PFunctor} [∀ a, MeasurableSpace (P.B a)] [P.AnswerMeasure]
  {β : Type*} [MeasurableSpace β]

/-- Expected visible queries, expressed as the sum of strict cutoff tails. -/
noncomputable def expectedQueries (computation : Resumption P β) : ℝ≥0∞ :=
  ∑' k, truncateMeasure k computation {none}

/-- The tail-sum formula for the extended query count. -/
theorem expectedQueries_eq_tsum (computation : Resumption P β) :
    expectedQueries computation = ∑' k, truncateMeasure k computation {none} := by rfl

/-- Returned mass and cutoff mass partition the finite observation. -/
theorem outputMeasure_add_cutoff [∀ a, DiscreteMeasurableSpace (P.B a)]
    (computation : Resumption P β) (fuel : ℕ) :
    outputMeasure fuel computation Set.univ + truncateMeasure fuel computation {none} = 1 := by
  have := isProbabilityMeasure_truncateMeasure fuel computation
  rw [outputMeasure, Measure.dropNone_apply_univ]
  have hc : {value : Option β | value.isSome} = ({none} : Set (Option β))ᶜ := by
    ext value
    cases value <;> simp
  rw [hc, add_comm, measure_add_measure_compl Option.measurableSet_none, measure_univ]

/-- Vanishing cutoff tails certify almost-sure return without renormalizing the output law. -/
theorem returnedMeasure_univ_eq_one_of_cutoff_tendsto [∀ a, DiscreteMeasurableSpace (P.B a)]
    (computation : Resumption P β)
    (h : Tendsto (fun k => truncateMeasure k computation {none}) atTop (𝓝 0)) :
    returnedMeasure computation Set.univ = 1 := by
  apply le_antisymm (returnedMeasure_apply_univ_le_one computation)
  have ht := (tendsto_const_nhds (x := returnedMeasure computation Set.univ)).add h
  rw [add_zero] at ht
  apply ge_of_tendsto ht
  apply Eventually.of_forall
  intro k
  rw [← outputMeasure_add_cutoff computation k]
  exact add_le_add ((outputMeasure_le_returnedMeasure k computation) Set.univ) le_rfl

/-- A deterministic immediate return consumes no visible query. -/
@[simp] theorem expectedQueries_pure (value : β) :
    expectedQueries (pure (p := P) value) = 0 := by
  simp [expectedQueries]

end PFunctor.Resumption
