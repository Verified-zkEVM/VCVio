/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module
public import VCVio.OracleComp.Coinductive.UniformThreshold.Approximation

/-!
# An exact finite sampler implemented through a persistent uniform real

Two rational threshold queries divide `[0,1)` into three equal cells. The mathematical
specification uses Lebesgue measure, but its implementation stores only a finite bit prefix
and compares rational numbers. The second query reuses the prefix produced by the first.
This is an exact non-dyadic discrete distribution, not floating-point Gaussian sampling.
-/

public section

open MeasureTheory ProbabilityTheory PFunctor UniformThreshold
open scoped ENNReal

namespace UniformTernary

attribute [local instance] UniformThreshold.answerMeasurableSpace

/-- A threshold client which chooses one of three equal subintervals. -/
@[expose] def client : FreeM spec.toPFunctor (Fin 3) :=
  .liftBind (1 / 3) fun left => if left then .pure 0 else
    .liftBind (2 / 3) fun middle => .pure (if middle then 1 else 2)

/-- The corresponding exact partition of the ideal uniform real. -/
noncomputable def bin (u : ℝ) : Fin 3 :=
  if u < 1 / 3 then 0 else if u < 2 / 3 then 1 else 2

/-- The three-cell partition is Borel measurable. -/
theorem measurable_bin : Measurable bin := by
  exact measurable_const.ite (measurableSet_lt measurable_id measurable_const)
    (measurable_const.ite (measurableSet_lt measurable_id measurable_const) measurable_const)

/-- Running the ideal threshold client just applies the three-cell partition. -/
theorem ideal_run (u : ℝ) :
    FreeM.runKernel idealAnswer client u = Measure.dirac (bin u, u) := by
  rw [client, runKernel_ideal_liftBind]
  simp only [readReal_eq, Rat.cast_div, Rat.cast_ofNat, Rat.cast_one]
  by_cases h : u < 1 / 3
  · simp only [h, ↓reduceIte, bin]
    exact FreeM.runKernel_pure (P := spec.toPFunctor) idealAnswer (0 : Fin 3) u
  · simp only [h, ↓reduceIte, Bool.false_eq_true]
    rw [runKernel_ideal_liftBind]
    change FreeM.runKernel (P := spec.toPFunctor) idealAnswer
      (pure (if readReal (2 / 3) u then 1 else 2 : Fin 3)) u = _
    rw [FreeM.runKernel_pure (P := spec.toPFunctor)]
    simp only [readReal_eq, Rat.cast_div, Rat.cast_ofNat, bin, h, ↓reduceIte]
    split_ifs <;> simp_all

/-- Each of the three ideal bins has probability exactly one third. -/
theorem bin_uniform : (cellLaw Prefix.empty).map bin = uniformOn (Set.univ : Set (Fin 3)) := by
  apply Measure.ext_of_singleton
  intro i
  rw [Measure.map_apply measurable_bin (measurableSet_singleton _), cellLaw_empty,
    Measure.restrict_apply (measurable_bin (measurableSet_singleton _)),
    uniformOn_univ_apply_singleton]
  have h0 : bin ⁻¹' {0} ∩ Set.Ico (0 : ℝ) 1 = Set.Ico (0 : ℝ) (1 / 3) := by
    ext u
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff, Set.mem_Ico, bin]
    split_ifs <;> norm_num <;> grind
  have h1 : bin ⁻¹' {1} ∩ Set.Ico (0 : ℝ) 1 = Set.Ico (1 / 3 : ℝ) (2 / 3) := by
    ext u
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff, Set.mem_Ico, bin]
    split_ifs <;> norm_num <;> grind
  have h2 : bin ⁻¹' {2} ∩ Set.Ico (0 : ℝ) 1 = Set.Ico (2 / 3 : ℝ) 1 := by
    ext u
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff, Set.mem_Ico, bin]
    split_ifs <;> norm_num <;> grind
  fin_cases i
  · change volume (bin ⁻¹' {(0 : Fin 3)} ∩ Set.Ico (0 : ℝ) 1) = _
    rw [h0, Real.volume_Ico]; norm_num [ENNReal.ofReal_div_of_pos]
  · change volume (bin ⁻¹' {(1 : Fin 3)} ∩ Set.Ico (0 : ℝ) 1) = _
    rw [h1, Real.volume_Ico]; norm_num [ENNReal.ofReal_div_of_pos]
  · change volume (bin ⁻¹' {(2 : Fin 3)} ∩ Set.Ico (0 : ℝ) 1) = _
    rw [h2, Real.volume_Ico]; norm_num [ENNReal.ofReal_div_of_pos]

/-- The actual fair-bit service implements the exact uniform ternary sampler. -/
theorem concrete_uniform :
    (FreeM.runKernel answerKernel client Prefix.empty).map Prod.fst =
      uniformOn (Set.univ : Set (Fin 3)) := by
  have hm : Measurable (fun u : ℝ => (bin u, u)) := measurable_bin.prodMk measurable_id
  rw [← adaptive_output_law client Prefix.empty]
  rw [show ⇑(FreeM.runKernel idealAnswer client) =
    (fun u => Measure.dirac (bin u, u)) from funext ideal_run,
    Measure.bind_dirac_eq_map _ hm,
    Measure.map_map measurable_fst hm]
  exact bin_uniform

/-- The whole ternary sampler as one machine, including persistent service state. -/
@[expose] def compiled := machineHandler.compile (fun _ : Unit => client)

/-- The actual composed machine has the exact uniform ternary returned law. -/
theorem compiled_uniform :
    (𝒟[ITree.ofResumptionWithTau (compiled.denote ((), Prefix.empty))]).map Prod.fst =
      uniformOn (Set.univ : Set (Fin 3)) := by
  rw [compiled, machineHandler.evalDist_compile answerKernel machineHandler_realizes]
  exact concrete_uniform

/-- Execute the ternary sampler through an injected source of independent fair bits. -/
def sampleIO (drawBit : IO Bool) : IO (Fin 3) := do
  let result ← compiled.runIO (ITree.withSilentSteps (fun _ => drawBit))
    (compiled.init ((), Prefix.empty))
  return result.1

/-- The client uses at most two threshold queries on every branch. -/
theorem client_query_bound : client.IsTotalRollBound 2 := by
  rw [client, FreeM.isTotalRollBound_liftBind_iff]
  refine ⟨by omega, fun b => ?_⟩
  cases b
  · rw [ite_eq_right Bool.false_ne_true, FreeM.isTotalRollBound_liftBind_iff]
    exact ⟨by omega, fun _ => trivial⟩
  · exact ⟨⟩

/-- Capping each query at `fuel` new bits gives a concrete uniform-output approximation. -/
theorem capped_error_le (fuel : ℕ) :
    (uniformOn (Set.univ : Set (Fin 3))).etvDist
      ((FreeM.runKernel (cappedAnswer (fun _ _ => fuel)) client Prefix.empty).map Prod.fst) ≤
        2 * (2 : ℝ≥0∞)⁻¹ ^ fuel := by
  have h := capped_output_law_le (fun _ _ => fuel) client Prefix.empty
  rw [adaptive_output_law, concrete_uniform] at h
  exact h.trans (KernelHandler.expectedCharge_le_of_totalRollBound
    (cappedAnswer (fun _ _ => fuel)) (fun _ _ => (2 : ℝ≥0∞)⁻¹ ^ fuel)
    ((2 : ℝ≥0∞)⁻¹ ^ fuel) (fun _ _ => le_rfl) client 2 client_query_bound Prefix.empty)

/-- The executable optional sampler inherits the precision bound, including timeout mass. -/
theorem capped_program_error_le (fuel : ℕ) :
    (uniformOn (Set.univ : Set (Fin 3))).etvDist
      (𝒟[cappedClient (fun _ _ => fuel) client Prefix.empty].map Prod.fst) ≤
        2 * (2 : ℝ≥0∞)⁻¹ ^ fuel := by
  rw [evalDist_cappedClient]
  exact capped_error_le fuel

end UniformTernary
