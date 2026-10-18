/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import VCVio.EvalDist.KernelHandler.Machine
public import VCVio.EvalDist.ResumptionKernel.Stateless
public import VCVio.OracleComp.Coinductive.UniformThreshold.Coinductive

/-!
# Coinductive handler laws through ordinary imports

The persistent threshold service can implement a continuing caller with a Borel
real result. A second consumer uses continuous private state and supplies its
measurability obligation explicitly. The kernel bridge also accepts independent
result universes and handles silent divergence. Reconstruction also covers continuous private
state, independent result universes and the actual persistent threshold dispatcher.
-/

public section

open MeasureTheory ProbabilityTheory PFunctor UniformThreshold

namespace VCVioTest.KernelCoinductive

example (caller : DynSystem.DynComputation spec.toPFunctor Unit ℝ) (p : Prefix) :
    𝒟[ITree.ofResumptionWithTau ((machineHandler.dispatch caller).denote ((), p))] =
      Resumption.runKernel answerKernel (caller.denote ()) p :=
  machineHandler.evalDist_dispatch answerKernel machineHandler_realizes caller () p

example {K : KernelHandler coinSpec.toPFunctor ℝ}
    {handler : Handler.Stateful (ITree coinSpec.toPFunctor) ℝ coinSpec.toPFunctor}
    (hh : K.Realizes handler)
    (hmeas : ∀ tree : ITree coinSpec.toPFunctor ℝ,
      Measurable fun s => 𝒟[(ITree.interp handler tree).run s])
    (tree : ITree coinSpec.toPFunctor ℝ) (state : ℝ) :
    𝒟[(ITree.interp handler tree).run state] = ITree.runKernel K tree state :=
  hh.interp_of_measurable hmeas tree state

example (K : KernelHandler coinSpec.toPFunctor ℝ)
    (tree : Resumption coinSpec.toPFunctor (ULift.{1} ℝ)) :
    ITree.runKernel K tree.toITree = Resumption.runKernel K tree :=
  ITree.runKernel_toITree K tree

example (K : KernelHandler coinSpec.toPFunctor ℝ) :
    ITree.runKernel K (ITree.diverge : ITree coinSpec.toPFunctor ℝ) = 0 :=
  ITree.runKernel_diverge K

example {concrete ideal : KernelHandler coinSpec.toPFunctor ℝ} {R : Kernel ℝ ℝ}
    (contract : KernelHandler.ReconstructionContract concrete ideal R)
    (tree : ITree coinSpec.toPFunctor (ULift.{1} ℝ)) :
    ITree.runKernel ideal tree ∘ₖ R =
      Kernel.retainLeft (ULift.{1} ℝ) R ∘ₖ ITree.runKernel concrete tree :=
  contract.runKernel_itree tree

example (caller : DynSystem.DynComputation spec.toPFunctor Unit ℝ) (p : Prefix) :
    (𝒟[ITree.ofResumptionWithTau
      ((machineHandler.dispatch caller).denote ((), p))]).map Prod.fst =
      ((cellLaw p).bind (Resumption.runKernel idealAnswer (caller.denote ()))).map Prod.fst :=
  adaptive_dispatch_output_law caller () p

example {concrete ideal : KernelHandler coinSpec.toPFunctor ℝ} {R : Kernel ℝ ℝ}
    (contract : KernelHandler.ReconstructionContract concrete ideal R)
    (μ : Measure ℝ) :
    ((μ.bind R).bind (ITree.runKernel ideal (ITree.diverge : ITree coinSpec.toPFunctor ℝ))).map
        Prod.fst =
      (μ.bind (ITree.runKernel concrete (ITree.diverge : ITree coinSpec.toPFunctor ℝ))).map
        Prod.fst :=
  contract.output_law_itree μ ITree.diverge

example {P : PFunctor.{0, 1}} {α : Type 1}
    [∀ a, MeasurableSpace (P.B a)] [∀ a, Countable (P.B a)]
    [∀ a, MeasurableSingletonClass (P.B a)] [P.AnswerMeasure] [MeasurableSpace α]
    (tree : Resumption P α) :
    (Resumption.runKernel (AnswerMeasure.statelessKernel P) tree ()).map Prod.fst =
      Resumption.returnedMeasure tree :=
  Resumption.map_runKernel_stateless tree

end VCVioTest.KernelCoinductive
