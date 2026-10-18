/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import VCVio.OracleComp.Coinductive.UniformThreshold.Categorical.Semantics

/-!
# An exact ternary sampler from the generic rational categorical construction

Three equal rational tickets partition one persistent uniform real. The generic
categorical client shares a finite dyadic prefix across two threshold queries,
and its compiled fair-bit machine returns exactly the uniform `Fin 3` measure.
The ideal Borel partition remains available as a compact mathematical view.
-/

public section

open MeasureTheory ProbabilityTheory PFunctor UniformThreshold
open scoped ENNReal

namespace UniformTernary

attribute [local instance] UniformThreshold.answerMeasurableSpace

/-- Three equally weighted tickets in the existing executable rational representation. -/
@[expose] def distribution : FinRatPMF.Raw (Fin 3) :=
  ⟨#[(0, 1 / 3), (1, 1 / 3), (2, 1 / 3)], by norm_num⟩

/-- The generic cumulative-threshold client specializes to the two ternary boundaries. -/
@[expose] def client : FreeM spec.toPFunctor (Fin 3) := Categorical.client distribution

/-- The corresponding exact partition of the ideal uniform real. -/
noncomputable def bin (u : ℝ) : Fin 3 :=
  if u < 1 / 3 then 0 else if u < 2 / 3 then 1 else 2

/-- The three-cell partition is Borel measurable. -/
theorem measurable_bin : Measurable bin := by
  exact measurable_const.ite (measurableSet_lt measurable_id measurable_const)
    (measurable_const.ite (measurableSet_lt measurable_id measurable_const) measurable_const)

/-- The generic cumulative partition has exactly the two ternary boundaries. -/
theorem partition_eq_bin (u : ℝ) :
    Categorical.partition (Categorical.fallback distribution) 0 distribution.toList u = bin u := by
  norm_num [Categorical.partition, Categorical.fallback, distribution, FinRatPMF.Raw.toList, bin]

/-- Running the ideal threshold client just applies the three-cell partition. -/
theorem ideal_run (u : ℝ) :
    FreeM.runKernel idealAnswer client u = Measure.dirac (bin u, u) := by
  change FreeM.runKernel idealAnswer
    (Categorical.scan (Categorical.fallback distribution) 0 distribution.toList) u = _
  rw [Categorical.ideal_scan, partition_eq_bin]

/-- The normalized ticket array denotes the uniform ternary measure. -/
theorem distribution_measure : distribution.toMeasure = uniformOn (Set.univ : Set (Fin 3)) := by
  apply Measure.ext_of_singleton
  intro i
  rw [FinRatPMF.Raw.toMeasure_apply_singleton, uniformOn_univ_apply_singleton]
  fin_cases i <;> norm_num [distribution, FinRatPMF.Raw.prob, FinRatPMF.Raw.probOfList,
    FinRatPMF.Raw.toList]

/-- The actual fair-bit service implements the exact uniform ternary sampler. -/
theorem concrete_uniform :
    (FreeM.runKernel answerKernel client Prefix.empty).map Prod.fst =
      uniformOn (Set.univ : Set (Fin 3)) :=
  (Categorical.concrete_law distribution).trans distribution_measure

/-- Each of the three ideal bins has probability exactly one third. -/
theorem bin_uniform : (cellLaw Prefix.empty).map bin = uniformOn (Set.univ : Set (Fin 3)) := by
  have h := concrete_uniform
  have hm : Measurable (fun u : ℝ => (bin u, u)) := measurable_bin.prodMk measurable_id
  rw [← adaptive_output_law client Prefix.empty,
    show ⇑(FreeM.runKernel idealAnswer client) = (fun u => Measure.dirac (bin u, u)) from
      funext ideal_run, Measure.bind_dirac_eq_map _ hm, Measure.map_map measurable_fst hm] at h
  exact h

/-- The whole ternary sampler as one machine, including persistent service state. -/
@[expose] def compiled := Categorical.compiled distribution

/-- The actual composed machine has the exact uniform ternary returned law. -/
theorem compiled_uniform :
    (𝒟[ITree.ofResumptionWithTau (compiled.denote ((), Prefix.empty))]).map Prod.fst =
      uniformOn (Set.univ : Set (Fin 3)) :=
  (Categorical.compiled_law distribution).trans distribution_measure

/-- Execute the ternary sampler through an injected source of independent fair bits. -/
def sampleIO (drawBit : IO Bool) : IO (Fin 3) := Categorical.sampleIO distribution drawBit

/-- The client uses at most two threshold queries on every branch. -/
theorem client_query_bound : client.IsTotalRollBound 2 :=
  Categorical.client_query_bound distribution

/-- The executable optional sampler inherits the precision bound, including timeout mass. -/
theorem capped_program_error_le (fuel : ℕ) :
    (uniformOn (Set.univ : Set (Fin 3))).etvDist
      (𝒟[cappedClient (fun _ _ => fuel) client Prefix.empty].map Prod.fst) ≤
        2 * (2 : ℝ≥0∞)⁻¹ ^ fuel := by
  have h := Categorical.capped_error_le distribution fuel
  rw [distribution_measure] at h
  exact h

/-- Capping each query at `fuel` new bits gives a concrete uniform-output approximation. -/
theorem capped_error_le (fuel : ℕ) :
    (uniformOn (Set.univ : Set (Fin 3))).etvDist
      ((FreeM.runKernel (cappedAnswer (fun _ _ => fuel)) client Prefix.empty).map Prod.fst) ≤
        2 * (2 : ℝ≥0∞)⁻¹ ^ fuel := by
  rw [← evalDist_cappedClient]
  exact capped_program_error_le fuel

end UniformTernary
