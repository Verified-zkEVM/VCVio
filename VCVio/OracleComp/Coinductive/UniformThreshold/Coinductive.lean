/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import VCVio.OracleComp.Coinductive.UniformThreshold.Semantics
public import VCVio.ProgramLogic.Relational.Reconstruction.Coinductive
public import VCVio.EvalDist.KernelHandler.Machine

/-!
# Persistent ideal randomness for continuing threshold clients

The actual fair-bit dispatcher and the persistent ideal-real service have equal
returned laws for arbitrary adaptive caller machines. Reconstruction couples the
retained finite prefix with a uniform real in its dyadic cell. The coinductive
contract lifts this local law without imposing a bound on the number of calls.
-/

public section

open MeasureTheory ProbabilityTheory

namespace UniformThreshold

variable {A B : Type} [MeasurableSpace B]

/-- Reconstructing the retained prefix after actual execution gives the joint ideal
result/real law, including clients with positive divergence probability. -/
theorem adaptive_dispatch_reconstruction
    (caller : PFunctor.DynSystem.DynComputation spec.toPFunctor A B)
    (input : A) (p : Prefix) :
    (𝒟[ITree.ofResumptionWithTau
      ((machineHandler.dispatch caller).denote (input, p))]).bind
        (Kernel.retainLeft B reconstruct) =
      (cellLaw p).bind (PFunctor.Resumption.runKernel idealAnswer (caller.denote input)) := by
  rw [machineHandler.evalDist_dispatch answerKernel machineHandler_realizes]
  have h := reconstructionContract.bind_state_laws_resumption
    (Measure.dirac p) (caller.denote input)
  simpa only [Measure.dirac_bind reconstruct.measurable, reconstruct_apply,
    Measure.dirac_bind
      (PFunctor.Resumption.runKernel answerKernel (caller.denote input)).measurable] using h.symm

/-- Every adaptive caller machine has the same returned law as comparisons against one
persistent ideal uniform real in the initial dyadic cell. Divergence remains missing mass. -/
theorem adaptive_dispatch_output_law
    (caller : PFunctor.DynSystem.DynComputation spec.toPFunctor A B)
    (input : A) (p : Prefix) :
    (𝒟[ITree.ofResumptionWithTau
      ((machineHandler.dispatch caller).denote (input, p))]).map Prod.fst =
      ((cellLaw p).bind (PFunctor.Resumption.runKernel idealAnswer (caller.denote input))).map
        Prod.fst := by
  rw [← adaptive_dispatch_reconstruction, Kernel.map_fst_bind_retainLeft]

end UniformThreshold
