/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import VCVio.EvalDist.KernelHandler.ITree
public import VCVio.EvalDist.ITreeMeasure
public import VCVio.EvalDist.MachineMeasure
public import VCVio.EvalDist.Defs.Measure.OptionT
public import PolyFun.PFunctor.Handler.Machine.Behavior

/-!
# Correctness of compiled stateful services

Local machine correctness extends to a single composed executable client.
Its explicit entry and return transitions become ITree silent steps, whose
measure interpretation is invariant under the dispatcher's weak bisimulation.
The output includes the final shared state, allowing subsequent initialization,
reconstruction, and observation maps to use the same theorem.
-/

public section

open MeasureTheory ProbabilityTheory

namespace PFunctor.MachineHandler

universe u

variable {P Q : PFunctor.{u, u}} {S A B : Type u}
  [∀ a, MeasurableSpace (P.B a)] [MeasurableSpace S] [MeasurableSpace B]
  [∀ a, MeasurableSpace (Q.B a)] [Q.AnswerMeasure]

/-- Local joint-law correctness implies correctness of the composed executable machine. -/
theorem evalDist_compile [∀ a, Countable (P.B a)]
    [∀ a, MeasurableSingletonClass (P.B a)] [∀ a, DiscreteMeasurableSpace (Q.B a)]
    (h : MachineHandler P Q S) (K : KernelHandler P S)
    (hh : K.Realizes h.toHandler) (client : A → FreeM P B) (input : A) (state : S) :
    𝒟[ITree.ofResumptionWithTau ((h.compile client).denote (input, state))] =
      FreeM.runKernel K (client input) state := by
  rw [ITree.evalDist_eq_returnedMeasure,
    (h.compile_weakBisim_execute client input state).returnedMeasure_eq,
    ITree.returnedMeasure_toITree]
  exact hh.run (client input) state

/-- A capped syntactic operation denotes its finite returned-output approximation. -/
theorem evalDist_capped (h : MachineHandler P Q S) (cap : (a : P.A) → S → Nat)
    (a : P.A) (state : S) :
    𝒟[(h.capped cap a).run state] =
      Resumption.outputMeasure (cap a state) ((h a).denote state) := by
  rw [OptionT.evalDist_eq_dropNone, capped_run, FreeM.evalDist_eq_denote,
    DynSystem.DynComputation.dropNone_denote_unroll]
  rfl

/-- A continuing caller's actual composed machine has the service-kernel law
when its stateful interpretation varies measurably with private service state. -/
theorem evalDist_dispatch_of_measurable
    [∀ a, Countable (P.B a)] [∀ a, MeasurableSingletonClass (P.B a)]
    [∀ a, DiscreteMeasurableSpace (Q.B a)] (h : MachineHandler P Q S) (K : KernelHandler P S)
    (hh : K.Realizes h.toHandler)
    (hmeas : ∀ tree : ITree P B,
      Measurable fun s => 𝒟[(ITree.interp h.toITreeHandler tree).run s])
    (caller : DynSystem.DynComputation.{u} P A B) (input : A) (state : S) :
    𝒟[ITree.ofResumptionWithTau ((h.dispatch caller).denote (input, state))] =
      Resumption.runKernel K (caller.denote input) state := by
  have hi : K.Realizes h.toITreeHandler := by
    intro a s
    change ITree.returnedMeasure ((h a).denote s).toITree = K a s
    rw [ITree.returnedMeasure_toITree]
    exact hh a s
  rw [ITree.evalDist_eq_returnedMeasure,
    (h.dispatch_weakBisim_interp caller input state).returnedMeasure_eq,
    ← ITree.evalDist_eq_returnedMeasure, hi.interp_of_measurable hmeas, ITree.runKernel_toITree]

/-- Countable separated service state makes the coinductive dispatcher law
automatic. Caller state and returned values need not be countable. -/
theorem evalDist_dispatch [Countable S] [MeasurableSingletonClass S]
    [∀ a, Countable (P.B a)] [∀ a, MeasurableSingletonClass (P.B a)]
    [∀ a, DiscreteMeasurableSpace (Q.B a)] (h : MachineHandler P Q S) (K : KernelHandler P S)
    (hh : K.Realizes h.toHandler) (caller : DynSystem.DynComputation.{u} P A B)
    (input : A) (state : S) :
    𝒟[ITree.ofResumptionWithTau ((h.dispatch caller).denote (input, state))] =
      Resumption.runKernel K (caller.denote input) state :=
  h.evalDist_dispatch_of_measurable K hh (fun _ => Measurable.of_discrete) caller input state

end PFunctor.MachineHandler
