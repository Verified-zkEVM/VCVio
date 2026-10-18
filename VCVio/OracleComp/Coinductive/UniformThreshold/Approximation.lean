/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module
public import VCVio.OracleComp.Coinductive.UniformThreshold.Semantics
public import VCVio.ProgramLogic.Relational.ApproxReconstruction

/-!
# Capped implementations of the persistent threshold service

A cap may depend on the query and retained prefix. A timed-out operation contributes no
successful output mass; it is not retried or conditioned on success. Approximate reconstruction
then gives the expected accumulated precision charge for an arbitrary adaptive client.
-/

public section

open MeasureTheory ProbabilityTheory PFunctor
open scoped ENNReal

namespace UniformThreshold

attribute [local instance] coinAnswerMeasurableSpace answerMeasurableSpace

/-- Successful answer/state kernel of a query stopped at its supplied bit budget. -/
noncomputable def cappedAnswer (cap : ℚ → Prefix → ℕ) (q : ℚ) : Kernel Prefix (Bool × Prefix) :=
  ⟨fun p => outputLaw q p (cap q p), Measurable.of_discrete⟩

instance (cap : ℚ → Prefix → ℕ) (q : ℚ) : IsSubprobabilityKernel (cappedAnswer cap q) := by
  constructor
  intro p
  change outputLaw q p (cap q p) Set.univ ≤ 1
  rw [outputLaw_eq_outputMeasure]
  exact (Resumption.outputMeasure_le_returnedMeasure (P := coinSpec.toPFunctor)
    (cap q p) ((machine q).denote p) Set.univ).trans_eq (returnedMeasure_univ q p)

/-- Executable finite syntax for an adaptive client with permanently capped operations. -/
@[expose] def cappedClient {α : Type} (cap : ℚ → Prefix → ℕ)
    (program : FreeM spec.toPFunctor α) (p : Prefix) :
    OptionT (FreeM coinSpec.toPFunctor) (α × Prefix) :=
  (machineHandler.capped cap).run program p

/-- The capped machine implementation realizes the cutoff kernel without renormalization. -/
theorem capped_realizes (cap : ℚ → Prefix → ℕ) :
    KernelHandler.Realizes (cappedAnswer cap) (machineHandler.capped cap) := by
  intro q p
  rw [MachineHandler.evalDist_capped (P := spec.toPFunctor) machineHandler cap q p]
  exact (outputLaw_eq_outputMeasure q p (cap q p)).symm

/-- The finite optional client has exactly the capped stateful kernel law. -/
theorem evalDist_cappedClient {α : Type} [MeasurableSpace α] (cap : ℚ → Prefix → ℕ)
    (program : FreeM spec.toPFunctor α) (p : Prefix) :
    𝒟[cappedClient cap program p] = FreeM.runKernel (cappedAnswer cap) program p :=
  (capped_realizes cap).run program p

/-- Precision caps incur at most their geometric tail as local reconstruction error. -/
theorem capped_reconstructionContract (cap : ℚ → Prefix → ℕ) :
    KernelHandler.ApproxReconstructionContract (P := spec.toPFunctor)
      (cappedAnswer cap) idealAnswer reconstruct (fun q p => (2 : ℝ≥0∞)⁻¹ ^ cap q p) := by
  refine ⟨inferInstance, fun _ => Measurable.of_discrete, fun q p => ?_⟩
  rw [reconstructionContract.step, Kernel.comp_apply, Kernel.comp_apply, Measure.etvDist_comm]
  change ((outputLaw q p (cap q p)).bind (Kernel.retainLeft Bool reconstruct)).etvDist
    ((answerKernel q p).bind (Kernel.retainLeft Bool reconstruct)) ≤ _
  rw [outputLaw_eq_outputMeasure, answerKernel_apply]
  exact (Resumption.etvDist_bind_outputMeasure_returnedMeasure_le
    ((machine q).denote p) (cap q p) (Kernel.retainLeft Bool reconstruct)).trans
      (by rw [← boundedLaw_eq_truncateMeasure]; exact cutoff_le q p _)

/-- An adaptive capped client approximates the ideal persistent service by its actual expected
sum of local precision charges, with no renormalization after a timeout. -/
theorem capped_output_law_le {α : Type} [MeasurableSpace α] (cap : ℚ → Prefix → ℕ)
    (program : FreeM spec.toPFunctor α) (p : Prefix) :
    (((cellLaw p).bind (FreeM.runKernel idealAnswer program)).map Prod.fst).etvDist
      ((FreeM.runKernel (cappedAnswer cap) program p).map Prod.fst) ≤
        KernelHandler.expectedCharge (cappedAnswer cap)
          (fun q p => (2 : ℝ≥0∞)⁻¹ ^ cap q p) program p := by
  have h := (capped_reconstructionContract cap).output_law_le
    (Measure.dirac p) (cellLaw p) program
  simpa only [Measure.dirac_bind reconstruct.measurable, reconstruct_apply,
    Measure.dirac_bind (FreeM.runKernel (cappedAnswer cap) program).measurable,
    Measure.etvDist_self, zero_add, lintegral_dirac] using h

end UniformThreshold
