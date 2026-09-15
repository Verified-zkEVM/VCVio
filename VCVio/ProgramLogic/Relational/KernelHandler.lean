/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module
public import VCVio.EvalDist.PFunctorKernelTransport
public import VCVio.ProgramLogic.Relational.Measure.Bind

/-!
# Local coupling contracts for polynomial kernel handlers

A contract supplies a measurable joint handler with a common answer and two private states.
Its projections implement the two marginal handlers on a measurable state relation. The free
extension yields a coupling for every adaptive program, including when its initial private
states have arbitrary coupled laws. Shared services keep their state across repeated calls.
-/

public section

open MeasureTheory ProbabilityTheory

universe uA uB uS uT uR

namespace PFunctor

variable {P : PFunctor.{uA, uB}} {S : Type uS} {T : Type uT}
  [∀ a, MeasurableSpace (P.B a)] [MeasurableSpace S] [MeasurableSpace T]

/-- A measurable, common-answer coupling of two local handlers on related private states. -/
structure KernelHandler.CouplingContract (left : KernelHandler P S)
    (right : KernelHandler P T) (R : S → T → Prop) where
  /-- Joint operation kernels, retaining both private states. -/
  joint : KernelHandler P (S × T)
  /-- The related-state region is measurable. -/
  measurable_relation : MeasurableSet {state : S × T | R state.1 state.2}
  /-- Projecting the first private state gives the left operation. -/
  map_left : ∀ a state, R state.1 state.2 →
    (joint a state).map (fun out => (out.1, out.2.1)) = left a state.1
  /-- Projecting the second private state gives the right operation. -/
  map_right : ∀ a state, R state.1 state.2 →
    (joint a state).map (fun out => (out.1, out.2.2)) = right a state.2
  /-- A local operation preserves the state relation almost everywhere. -/
  invariant : ∀ a state, R state.1 state.2 → ∀ᵐ out ∂joint a state, R out.2.1 out.2.2

namespace KernelHandler.CouplingContract

variable [∀ a, Countable (P.B a)] [∀ a, MeasurableSingletonClass (P.B a)]
  {left : KernelHandler P S} {right : KernelHandler P T} {R : S → T → Prop}
  (contract : CouplingContract left right R)
  {α : Type uR} [MeasurableSpace α]

/-- The joint result-and-state kernel induced by the local contract. -/
noncomputable def runJoint (program : FreeM P α) : Kernel (S × T) ((α × S) × (α × T)) :=
  (FreeM.runKernel contract.joint program).map fun out =>
    ((out.1, out.2.1), (out.1, out.2.2))

private theorem measurable_split :
    Measurable (fun out : α × (S × T) => ((out.1, out.2.1), (out.1, out.2.2))) :=
  (measurable_fst.prodMk measurable_snd.fst).prodMk
    (measurable_fst.prodMk measurable_snd.snd)

/-- The induced joint kernel has the required whole-program marginals. -/
theorem runJoint_isCoupling (program : FreeM P α) {state : S × T}
    (hstate : R state.1 state.2) :
    Measure.IsCoupling (contract.runJoint program state)
      (FreeM.runKernel left program state.1) (FreeM.runKernel right program state.2) := by
  rw [runJoint, Kernel.map_apply _ measurable_split]
  constructor
  · rw [Measure.fst, Measure.map_map measurable_fst measurable_split]
    exact FreeM.map_runKernel_state contract.joint left Prod.fst measurable_fst
      contract.map_left contract.invariant program hstate
  · rw [Measure.snd, Measure.map_map measurable_snd measurable_split]
    exact FreeM.map_runKernel_state contract.joint right Prod.snd measurable_snd
      contract.map_right contract.invariant program hstate

/-- Lifting local contracts preserves every measurable postcondition that holds for a common
result and related final states. -/
theorem runJoint_ae (program : FreeM P α) {state : S × T} (hstate : R state.1 state.2)
    {post : (α × S) → (α × T) → Prop}
    (hpost : MeasurableSet {out : (α × S) × (α × T) | post out.1 out.2})
    (hresult : ∀ x s t, R s t → post (x, s) (x, t)) :
    ∀ᵐ out ∂contract.runJoint program state, post out.1 out.2 := by
  rw [runJoint, Kernel.map_apply _ measurable_split]
  apply (ae_map_iff measurable_split.aemeasurable hpost).2
  exact (FreeM.runKernel_ae_invariant contract.joint contract.measurable_relation
    contract.invariant program hstate).mono fun out hout => hresult out.1 out.2.1 out.2.2 hout

include contract in
/-- Initial coupled state laws compose with every adaptive program using only local contracts. -/
theorem bind_state_laws {μ : Measure S} {ν : Measure T}
    (hinit : MeasureProgramLogic.CouplingPost μ ν R) (program : FreeM P α)
    {post : (α × S) → (α × T) → Prop}
    (hpost : MeasurableSet {out : (α × S) × (α × T) | post out.1 out.2})
    (hresult : ∀ x s t, R s t → post (x, s) (x, t)) :
    MeasureProgramLogic.CouplingPost (μ.bind (FreeM.runKernel left program))
      (ν.bind (FreeM.runKernel right program)) post := by
  exact hinit.bind (FreeM.runKernel left program).measurable
    (FreeM.runKernel right program).measurable (contract.runJoint program).measurable hpost
      fun state hstate => ⟨contract.runJoint_isCoupling program hstate,
        contract.runJoint_ae program hstate hpost hresult⟩

end KernelHandler.CouplingContract

namespace KernelHandler.CouplingContract

variable [∀ a, Countable (P.B a)] [∀ a, MeasurableSingletonClass (P.B a)]
  {left : KernelHandler P S} {right : KernelHandler P T} {R : S → T → Prop}
  (contract : CouplingContract left right R)
  {Q : PFunctor.{uA, uB}} [∀ a, MeasurableSpace (Q.B a)]

/-- A local coupling contract extends to any free handler. The resulting contract can itself
be supplied at the next layer of a polynomial wiring. -/
noncomputable def freeHandler (implementation : (a : Q.A) → FreeM P (Q.B a)) :
    CouplingContract (fun a => FreeM.runKernel left (implementation a))
      (fun a => FreeM.runKernel right (implementation a)) R where
  joint a := FreeM.runKernel contract.joint (implementation a)
  measurable_relation := contract.measurable_relation
  map_left a _ hstate := FreeM.map_runKernel_state contract.joint left Prod.fst measurable_fst
    contract.map_left contract.invariant (implementation a) hstate
  map_right a _ hstate := FreeM.map_runKernel_state contract.joint right Prod.snd measurable_snd
    contract.map_right contract.invariant (implementation a) hstate
  invariant a _ hstate := FreeM.runKernel_ae_invariant contract.joint
    contract.measurable_relation contract.invariant (implementation a) hstate

end KernelHandler.CouplingContract
end PFunctor
