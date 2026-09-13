/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module
public import VCVio.EvalDist.PFunctorKernel
public import PolyFun.PFunctor.Wiring

/-!
# Kernel semantics of recursive polynomial wiring

The actual `PFunctor.Wiring` syntax is interpreted through its universal free handler. The box
law identifies this with interpreting its children first and supplying their kernels to the
box implementation. Every wire uses the same private state space and the same state value;
referring to one external service twice therefore preserves its shared state.
-/

public section

open MeasureTheory ProbabilityTheory

universe uB uS

namespace PFunctor.Wiring

variable {Boxes Inputs : Type} {Arity : Boxes → Type}
  {Dom : (b : Boxes) → Arity b → PFunctor.{uB, uB}}
  {Cod : Boxes → PFunctor.{uB, uB}} {inputInterface : Inputs → PFunctor.{uB, uB}}
  {S : Type uS} [MeasurableSpace S]
  [∀ a, MeasurableSpace ((PFunctor.sigma inputInterface).B a)]
  [∀ a, Countable ((PFunctor.sigma inputInterface).B a)]
  [∀ a, MeasurableSingletonClass ((PFunctor.sigma inputInterface).B a)]

/-- Run a recursive wiring against shared external kernel services. -/
noncomputable def runKernel
    (implementation : (b : Boxes) →
      (a : (Cod b).A) → FreeM (PFunctor.sigma (Dom b)) ((Cod b).B a))
    (services : KernelHandler (PFunctor.sigma inputInterface) S)
    {output : PFunctor.{uB, uB}}
    (wiring : Wiring Boxes Arity Dom Cod Inputs inputInterface output)
    (a : output.A) [MeasurableSpace (output.B a)] : Kernel S (output.B a × S) :=
  FreeM.runKernel services (wiring.eval implementation a)

/-- Kernel evaluation is the stateful interpretation of the wiring's free handler. -/
theorem runKernel_eq
    (implementation : (b : Boxes) →
      (a : (Cod b).A) → FreeM (PFunctor.sigma (Dom b)) ((Cod b).B a))
    (services : KernelHandler (PFunctor.sigma inputInterface) S)
    {output : PFunctor.{uB, uB}}
    (wiring : Wiring Boxes Arity Dom Cod Inputs inputInterface output)
    (a : output.A) [MeasurableSpace (output.B a)] :
    runKernel implementation services wiring a =
      FreeM.runKernel services (wiring.eval implementation a) := by rfl

/-- A box may be interpreted after its children, with no change to its result or state law. -/
theorem runKernel_box
    (implementation : (b : Boxes) →
      (a : (Cod b).A) → FreeM (PFunctor.sigma (Dom b)) ((Cod b).B a))
    (services : KernelHandler (PFunctor.sigma inputInterface) S) (b : Boxes)
    [∀ a, MeasurableSpace ((PFunctor.sigma (Dom b)).B a)]
    [∀ a, Countable ((PFunctor.sigma (Dom b)).B a)]
    [∀ a, MeasurableSingletonClass ((PFunctor.sigma (Dom b)).B a)]
    (children : (port : Arity b) →
      Wiring Boxes Arity Dom Cod Inputs inputInterface (Dom b port))
    (a : (Cod b).A) [MeasurableSpace ((Cod b).B a)] (state : S) :
    runKernel implementation services (.box b children) a state =
      FreeM.runKernel
        (fun q : (PFunctor.sigma (Dom b)).A =>
          FreeM.runKernel services (eval implementation (children q.1) q.2))
        (implementation b a) state := by
  unfold runKernel
  rw [eval_box, FreeM.runKernel_liftM]
  rfl

end PFunctor.Wiring
