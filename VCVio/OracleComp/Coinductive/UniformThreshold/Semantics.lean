/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module
public import VCVio.OracleComp.Coinductive.UniformThreshold.Interval
public import VCVio.EvalDist.ResumptionApproximation
public import ToMathlib.Probability.FairBit
public import VCVio.ProgramLogic.Relational.Reconstruction
public import VCVio.OracleComp.Coinductive.BitRealization

/-!
# Persistent-threshold implementation correctness

The concrete machine retains finite bits; the ideal service retains one real sampled once.
Reconstructing the real from the machine's returned prefix gives exactly the ideal joint
answer/real law. Thus the local correctness statement retains enough information for
arbitrary subsequent adaptive queries. Almost-sure termination is established independently
by the uniform bit-cost tail bound.
-/

public section

open MeasureTheory ProbabilityTheory PFunctor
open scoped ENNReal

namespace UniformThreshold

attribute [local instance] coinAnswerMeasurableSpace

/-- The ideal answer to a rational threshold query on a persistent real state. -/
noncomputable def readReal (q : ℚ) (u : ℝ) : Bool := if u < (q : ℝ) then true else false

theorem measurable_readReal (q : ℚ) : Measurable (readReal q) :=
  measurable_const.ite (measurableSet_lt measurable_id measurable_const) measurable_const

/-- The ideal answer is the Boolean test of the real threshold comparison. -/
theorem readReal_eq (q : ℚ) (u : ℝ) : readReal q u = if u < (q : ℝ) then true else false := by
  rfl

/-- The ideal joint answer/state law from a represented dyadic cell. -/
noncomputable def idealLaw (q : ℚ) (p : Prefix) : Measure (Bool × ℝ) :=
  (cellLaw p).map (fun u => (readReal q u, u))

instance (q : ℚ) (p : Prefix) : IsProbabilityMeasure (idealLaw q p) :=
  (Measure.isProbabilityMeasure_map_iff
    ((measurable_readReal q).prodMk measurable_id).aemeasurable).mpr inferInstance

/-- A resolved prefix gives a constant ideal answer throughout its cell. -/
theorem idealLaw_of_resolved (q : ℚ) (p : Prefix) {b : Bool} (h : classify q p = some b) :
    idealLaw q p = Kernel.retainLeft Bool reconstruct (b, p) := by
  rw [idealLaw, Kernel.retainLeft_apply, reconstruct_apply]
  apply Measure.map_congr
  filter_upwards [cellLaw_ae_interval p] with u hu
  rw [Prefix.mem_interval] at hu
  apply congrArg (fun b => (b, u))
  cases b with
  | false => simp [readReal, not_lt.mpr (classify_false_sound q p h hu.1)]
  | true => simp [readReal, classify_true_sound q p h hu.2]

/-- Refining a represented real by a fair bit preserves its ideal answer/state law. -/
theorem idealLaw_split (q : ℚ) (p : Prefix) :
    (uniformOn (Set.univ : Set Bool)).bind (fun b => idealLaw q (p.push b)) = idealLaw q p := by
  rw [Measure.bind_uniformOn_bool]
  have hm : Measurable (fun u : ℝ => (readReal q u, u)) :=
    (measurable_readReal q).prodMk measurable_id
  simp only [idealLaw]
  rw [← Measure.map_add _ _ hm, ← Measure.map_smul _ hm.aemeasurable, cellLaw_split]

/-- The successful outputs of a bounded query, without its cutoff outcome. -/
noncomputable def outputLaw (q : ℚ) (p : Prefix) (fuel : ℕ) : Measure (Bool × Prefix) :=
  (boundedLaw q p fuel).dropNone

/-- Finite successful laws agree with the coinductive returned-output approximations. -/
theorem outputLaw_eq_outputMeasure (q : ℚ) (p : Prefix) (fuel : ℕ) :
    outputLaw q p fuel = Resumption.outputMeasure fuel ((machine q).denote p) := by
  rw [outputLaw, boundedLaw_eq_truncateMeasure]
  rfl

/-- One unresolved bit composes the two successful continuation laws. -/
theorem outputLaw_succ (q : ℚ) (p : Prefix) (fuel : ℕ) (h : classify q p = none) :
    outputLaw q p (fuel + 1) = (uniformOn (Set.univ : Set Bool)).bind
      (fun b => outputLaw q (p.push b) fuel) := by
  rw [outputLaw, boundedLaw_succ q p fuel h, Measure.dropNone,
    Measure.bind_bind Measurable.of_discrete.aemeasurable
      Measure.measurable_dropNoneKernel.aemeasurable]
  rfl

/-- Reconstructed successful outputs form a submeasure of the ideal joint law at every budget. -/
theorem bind_outputLaw_le_idealLaw (q : ℚ) (p : Prefix) (fuel : ℕ) :
    (outputLaw q p fuel).bind (Kernel.retainLeft Bool reconstruct) ≤ idealLaw q p := by
  induction fuel generalizing p with
  | zero =>
      cases hc : classify q p with
      | none =>
          simp only [outputLaw, boundedLaw_zero_of_unresolved q p hc,
            Measure.dropNone_dirac_none, Measure.bind_zero_left]
          exact Measure.zero_le _
      | some b =>
          rw [outputLaw, boundedLaw_of_resolved q p 0 hc, Measure.dropNone_dirac_some,
            Measure.dirac_bind (Kernel.retainLeft Bool reconstruct).measurable,
            idealLaw_of_resolved q p hc]
  | succ fuel ih =>
      cases hc : classify q p with
      | none =>
          rw [outputLaw_succ q p fuel hc,
            Measure.bind_bind Measurable.of_discrete.aemeasurable
              (Kernel.retainLeft Bool reconstruct).aemeasurable, ← idealLaw_split q p]
          exact Measure.bind_mono_right_of_forall Measurable.of_discrete.aemeasurable
            Measurable.of_discrete.aemeasurable (fun b => ih (p.push b))
      | some b =>
          rw [outputLaw, boundedLaw_of_resolved q p (fuel + 1) hc, Measure.dropNone_dirac_some,
            Measure.dirac_bind (Kernel.retainLeft Bool reconstruct).measurable,
            idealLaw_of_resolved q p hc]

/-- The actual joint answer/prefix kernel, obtained from the executable machine's return law. -/
noncomputable def answerKernel (q : ℚ) : Kernel Prefix (Bool × Prefix) :=
  ⟨fun p => Resumption.returnedMeasure ((machine q).denote p), Measurable.of_discrete⟩

instance (q : ℚ) : IsMarkovKernel (answerKernel q) := ⟨fun p => ⟨returnedMeasure_univ q p⟩⟩

/-- The kernel's measure is exactly the returned law of the supplied machine. -/
theorem answerKernel_apply (q : ℚ) (p : Prefix) :
    answerKernel q p = Resumption.returnedMeasure ((machine q).denote p) := by rfl

/-- Reconstructing after return gives exactly the persistent ideal answer and real state. -/
theorem bind_answerKernel_eq_idealLaw (q : ℚ) (p : Prefix) :
    (answerKernel q p).bind (Kernel.retainLeft Bool reconstruct) = idealLaw q p := by
  have hprob : IsProbabilityMeasure
      ((answerKernel q p).bind (Kernel.retainLeft Bool reconstruct)) :=
    isProbabilityMeasure_bind (Kernel.retainLeft Bool reconstruct).aemeasurable
      (Filter.Eventually.of_forall fun _ => inferInstance)
  apply Measure.eq_of_le_of_measure_univ_eq _ (by simp)
  apply Measure.le_iff.mpr
  intro event hevent
  have ht := (tendsto_const_nhds (x := idealLaw q p event)).add
    (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (2 : ℝ≥0∞)⁻¹ < 1))
  rw [add_zero] at ht
  apply ge_of_tendsto ht
  apply Filter.Eventually.of_forall
  intro fuel
  have hd := Resumption.etvDist_bind_outputMeasure_returnedMeasure_le
    ((machine q).denote p) fuel (Kernel.retainLeft Bool reconstruct)
  rw [← outputLaw_eq_outputMeasure, ← answerKernel_apply, ← boundedLaw_eq_truncateMeasure] at hd
  have he := Measure.absDiff_apply_le_etvDist
    ((answerKernel q p).bind (Kernel.retainLeft Bool reconstruct))
    ((outputLaw q p fuel).bind (Kernel.retainLeft Bool reconstruct)) hevent
  rw [Measure.etvDist_comm] at he
  have hsub := (le_add_right le_rfl).trans (he.trans hd)
  have hle := tsub_le_iff_right.mp hsub
  exact hle.trans (by
    rw [add_comm]
    exact add_le_add (bind_outputLaw_le_idealLaw q p fuel event) (cutoff_le q p fuel))

/-- Threshold answers carry the usual Boolean measurable space. -/
local instance answerMeasurableSpace :
    (q : spec.toPFunctor.A) → MeasurableSpace (spec.toPFunctor.B q) :=
  fun _ => inferInstanceAs (MeasurableSpace Bool)

/-- The ideal service reads its fixed real state and preserves it. -/
noncomputable def idealAnswer (q : ℚ) : Kernel ℝ (Bool × ℝ) :=
  Kernel.deterministic (fun u => (readReal q u, u))
    ((measurable_readReal q).prodMk measurable_id)

instance (q : ℚ) : IsMarkovKernel (idealAnswer q) := by
  unfold idealAnswer
  infer_instance

/-- The ideal kernel is a point mass at the answer and unchanged real state. -/
theorem idealAnswer_apply (q : ℚ) (u : ℝ) :
    idealAnswer q u = Measure.dirac (readReal q u, u) := by rfl

/-- An ideal query selects its continuation without changing the persistent real. -/
theorem runKernel_ideal_liftBind {α : Type*} [MeasurableSpace α] (q : ℚ)
    (next : Bool → FreeM spec.toPFunctor α) (u : ℝ) :
    FreeM.runKernel idealAnswer (FreeM.liftBind (P := spec.toPFunctor) q next) u =
      FreeM.runKernel idealAnswer (next (readReal q u)) u := by
  rw [FreeM.runKernel_liftBind (P := spec.toPFunctor), idealAnswer_apply,
    Measure.dirac_bind
      (FreeM.measurable_runKernel_continuation (P := spec.toPFunctor) idealAnswer next)]

/-- The lazy finite-prefix service refines the persistent ideal real service. -/
theorem reconstructionContract :
    KernelHandler.ReconstructionContract (P := spec.toPFunctor)
      answerKernel idealAnswer reconstruct := by
  refine ⟨inferInstance, fun q => ?_⟩
  ext p : 1
  rw [Kernel.comp_apply, Kernel.comp_apply, bind_answerKernel_eq_idealLaw]
  rw [reconstruct_apply]
  change (cellLaw p).bind (fun u => Measure.dirac (readReal q u, u)) = idealLaw q p
  exact Measure.bind_dirac_eq_map _ ((measurable_readReal q).prodMk measurable_id)

/-- Every adaptive client has the same result law under the executable and ideal services. -/
theorem adaptive_output_law {α : Type*} [MeasurableSpace α]
    (program : FreeM spec.toPFunctor α) (p : Prefix) :
    ((cellLaw p).bind (FreeM.runKernel idealAnswer program)).map Prod.fst =
      (FreeM.runKernel answerKernel program p).map Prod.fst := by
  have h := reconstructionContract.output_law (Measure.dirac p) program
  simpa only [Measure.dirac_bind reconstruct.measurable, reconstruct_apply,
    Measure.dirac_bind (FreeM.runKernel answerKernel program).measurable] using h

/-- Each executable machine has its advertised joint answer-and-prefix law. -/
theorem machineHandler_realizes :
    KernelHandler.Realizes answerKernel machineHandler.toHandler := by
  intro q p
  exact (answerKernel_apply q p).symm

/-- A service whose concrete state is the finite prefix of a single persistent random real. -/
@[expose] noncomputable def responder : ProbResponder spec where
  State := Prefix
  instMeasurableSpaceState := inferInstance
  instMeasurableSpaceRange := fun _ => inferInstance
  answerKernel := answerKernel
  answerKernel_isSubprobability := fun _ => inferInstance

/-- The actual rational-arithmetic bit machine realizes the service's joint kernels. -/
def bitRealization : ProbResponder.BitRealization responder where
  machine := machine
  returned_eq := fun q p => (answerKernel_apply q p).symm

end UniformThreshold
