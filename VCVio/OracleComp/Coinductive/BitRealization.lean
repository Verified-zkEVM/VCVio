/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module
public import VCVio.OracleComp.Coinductive.Responder
public import VCVio.OracleComp.Coinductive.Machine
public import VCVio.EvalDist.MachineMeasure
public import VCVio.EvalDist.KernelHandler.Machine
public import PolyFun.ITree.Machine
public import PolyFun.PFunctor.Dynamical.DynComputation.IO

/-!
# Fair-bit realizations of probabilistic services

A realization supplies executable machines and proves their returned-output measures equal
the service's joint answer/state kernels. Unlike a finite `ProbComp` presentation, a machine
may require an unbounded number of random bits. A probability answer kernel certifies almost
sure return through the equality of total mass; a subprobability kernel can describe genuine
divergence. The IO adapter takes its bit source as an argument. Its semantic assumption is
that calls supply independent fair bits, which is not a property of arbitrary IO code.
-/

public section

open MeasureTheory PFunctor OracleComp

namespace ProbResponder

variable {ι : Type} {spec : OracleSpec.{0, 0} ι}

/-- An executable fair-bit machine for each query, with its joint answer/state correctness law. -/
structure BitRealization (R : ProbResponder spec) where
  /-- A machine initialized with the service state and returning its answer and successor state. -/
  machine : (q : spec.Domain) → OracleMachine coinSpec R.State (spec.Range q × R.State)
  /-- The unbounded returned-output law equals the advertised joint kernel. -/
  returned_eq : ∀ q s,
    letI := R.instMeasurableSpaceRange q
    @Resumption.returnedMeasure coinSpec.toPFunctor (fun _ => ⊤) _ _ _ _
      ((machine q).denote s) = R.answerKernel q s

namespace BitRealization

variable {R : ProbResponder spec} (realization : BitRealization R)

/-- The machines are a polynomial service handler with shared responder state. -/
@[expose] def toMachineHandler :
    MachineHandler spec.toPFunctor coinSpec.toPFunctor R.State :=
  realization.machine

/-- A fair-bit realization satisfies the monad-independent local kernel contract. -/
theorem realizes :
    letI := R.instMeasurableSpaceRange
    KernelHandler.Realizes (P := spec.toPFunctor) R.answerKernel
      realization.toMachineHandler.toHandler := by
  let := R.instMeasurableSpaceRange
  intro q s
  exact realization.returned_eq q s

/-- Compile a finite client into one resumable fair-bit machine. -/
@[expose, implicit_reducible] def compile {A B : Type} (client : A → OracleComp spec B) :
    PFunctor.DynSystem.DynComputation
      (coinSpec.toPFunctor + PFunctor.y) (A × R.State) (B × R.State) :=
  realization.toMachineHandler.compile client

/-- Execute an entire client with one injected bit source and retained service state. -/
def runClientIO {A B : Type} (drawBit : IO Bool) (client : A → OracleComp spec B)
    (input : A) (state : R.State) : IO (B × R.State) :=
  let machine := realization.compile client
  machine.runIO (ITree.withSilentSteps (fun _ => drawBit)) (machine.init (input, state))

/-- The compiled client's joint returned law is its stateful kernel interpretation. -/
theorem evalDist_compile [∀ q, Countable (spec.Range q)]
    [∀ q, @MeasurableSingletonClass (spec.Range q) (R.instMeasurableSpaceRange q)]
    {A B : Type} [MeasurableSpace B] (client : A → OracleComp spec B)
    (input : A) (state : R.State) :
    letI := R.instMeasurableSpaceRange
    𝒟[ITree.ofResumptionWithTau ((realization.compile client).denote (input, state))] =
      FreeM.runKernel R.answerKernel (client input) state := by
  let := R.instMeasurableSpaceRange
  exact realization.toMachineHandler.evalDist_compile R.answerKernel realization.realizes
    client input state

/-- Execute through an injected bit source using the generic resumable IO driver. -/
def runIO (drawBit : IO Bool) (q : spec.Domain) (s : R.State) : IO (spec.Range q × R.State) :=
  (realization.machine q).runIO (fun _ => drawBit) ((realization.machine q).init s)

/-- Finite returned-output approximations are below the advertised service law. -/
theorem outputMeasure_le (q : spec.Domain) (s : R.State) (fuel : ℕ) :
    letI := R.instMeasurableSpaceRange q
    @Resumption.outputMeasure coinSpec.toPFunctor (fun _ => ⊤) _ _ _ fuel
      ((realization.machine q).denote s) ≤ R.answerKernel q s := by
  let := R.instMeasurableSpaceRange q
  rw [← realization.returned_eq]
  exact @Resumption.outputMeasure_le_returnedMeasure coinSpec.toPFunctor
    (fun _ => ⊤) _ _ _ _ fuel _

end BitRealization
end ProbResponder
