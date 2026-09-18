/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module
public import VCVio.EvalDist.WiringKernel
public import VCVio.ProgramLogic.Relational.KernelHandler

/-!
# Coupling contracts through recursive polynomial wiring

The same recursive wiring may be supplied with two families of external services. Local
coupling contracts for those services induce a contract for the complete wired handler and a
relational judgment over arbitrary initial private-state laws. A service referenced by several
ports retains its common state throughout evaluation.
-/

public section

open MeasureTheory ProbabilityTheory

universe uB uS uT

namespace PFunctor.Wiring

variable {Boxes Inputs : Type} {Arity : Boxes → Type}
  {Dom : (b : Boxes) → Arity b → PFunctor.{uB, uB}}
  {Cod : Boxes → PFunctor.{uB, uB}} {inputInterface : Inputs → PFunctor.{uB, uB}}
  {S : Type uS} {T : Type uT} [MeasurableSpace S] [MeasurableSpace T]
  [∀ a, MeasurableSpace ((PFunctor.sigma inputInterface).B a)]
  [∀ a, Countable ((PFunctor.sigma inputInterface).B a)]
  [∀ a, MeasurableSingletonClass ((PFunctor.sigma inputInterface).B a)]
  {left : KernelHandler (PFunctor.sigma inputInterface) S}
  {right : KernelHandler (PFunctor.sigma inputInterface) T} {R : S → T → Prop}

/-- Local service contracts compose through the actual recursive wiring syntax. -/
noncomputable def couplingContract
    (implementation : (b : Boxes) →
      (a : (Cod b).A) → FreeM (PFunctor.sigma (Dom b)) ((Cod b).B a))
    (contract : KernelHandler.CouplingContract left right R)
    {output : PFunctor.{uB, uB}} [∀ a, MeasurableSpace (output.B a)]
    (wiring : Wiring Boxes Arity Dom Cod Inputs inputInterface output) :
    KernelHandler.CouplingContract (fun a => runKernel implementation left wiring a)
      (fun a => runKernel implementation right wiring a) R := by
  simpa only [runKernel_eq] using contract.freeHandler (eval implementation wiring)

/-- A whole wired invocation relates random initial states using only local service contracts. -/
theorem bind_state_laws
    (implementation : (b : Boxes) →
      (a : (Cod b).A) → FreeM (PFunctor.sigma (Dom b)) ((Cod b).B a))
    (contract : KernelHandler.CouplingContract left right R)
    {output : PFunctor.{uB, uB}}
    (wiring : Wiring Boxes Arity Dom Cod Inputs inputInterface output)
    (a : output.A) [MeasurableSpace (output.B a)]
    {μ : Measure S} {ν : Measure T} (hinit : MeasureProgramLogic.CouplingPost μ ν R)
    {post : (output.B a × S) → (output.B a × T) → Prop}
    (hpost : MeasurableSet {out : (output.B a × S) × (output.B a × T) | post out.1 out.2})
    (hresult : ∀ x s t, R s t → post (x, s) (x, t)) :
    MeasureProgramLogic.CouplingPost (μ.bind (runKernel implementation left wiring a))
      (ν.bind (runKernel implementation right wiring a)) post := by
  simpa only [runKernel_eq] using
    contract.bind_state_laws hinit (eval implementation wiring a) hpost hresult

end PFunctor.Wiring
