/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module
public import VCVio.ProgramLogic.Relational.WiringKernel
public import Examples.ProgramLogic.MeasureCoupling

/-!
# Shared continuous state behind polynomial wiring

A two-port box calls one Gaussian state service twice. Both ports reference the same external
service. Its local offset coupling composes through any recursive wiring of these boxes, for
arbitrary initial state laws. Query replies are discrete acknowledgements while private state
and transitions are continuous.
-/

public section

open MeasureTheory ProbabilityTheory MeasureProgramLogic PFunctor
open scoped NNReal

namespace Examples.GaussianWiring

attribute [local implicit_reducible] PFunctor.sigma

/-- An operation acknowledging that its private state has advanced. -/
abbrev tick : PFunctor := ⟨Unit, fun _ => Unit⟩

instance : (a : (PFunctor.sigma fun _ : Unit => tick).A) →
    MeasurableSpace ((PFunctor.sigma fun _ : Unit => tick).B a) :=
  fun _ => inferInstanceAs (MeasurableSpace Unit)

instance : (a : (PFunctor.sigma fun _ : Unit => tick).A) →
    Countable ((PFunctor.sigma fun _ : Unit => tick).B a) :=
  fun _ => inferInstanceAs (Countable Unit)

instance : (a : (PFunctor.sigma fun _ : Unit => tick).A) →
    MeasurableSingletonClass ((PFunctor.sigma fun _ : Unit => tick).B a) :=
  fun _ => inferInstanceAs (MeasurableSingletonClass Unit)

/-- Both box inputs and its output have the acknowledgement interface. -/
abbrev Network := Wiring Unit (fun _ => Bool) (fun _ _ => tick) (fun _ => tick)
  Unit (fun _ => tick) tick

/-- The box calls both of its ports in sequence. -/
@[expose] def implementation (_ : Unit) (_ : tick.A) :
    FreeM (PFunctor.sigma fun _ : Bool => tick) Unit := do
  let _ ← FreeM.lift (P := PFunctor.sigma fun _ : Bool => tick) ⟨true, ()⟩
  FreeM.lift (P := PFunctor.sigma fun _ : Bool => tick) ⟨false, ()⟩

/-- Each of the two ports refers to the same external state service. -/
@[expose] def twice : Network := .box () (fun _ => .input ())

/-- Gaussian motion followed by an acknowledgement. -/
noncomputable def service (variance : ℝ≥0) :
    KernelHandler (PFunctor.sigma fun _ : Unit => tick) ℝ := fun _ =>
  { toFun := fun state => (gaussianReal state variance).map fun next => ((), next)
    measurable' := (Measure.measurable_map _ (by fun_prop)).comp
      (measurable_gaussianReal.comp (measurable_id.prodMk measurable_const)) }

/-- The joint service uses the same Gaussian increment for both private states. -/
noncomputable def jointService (variance : ℝ≥0) :
    KernelHandler (PFunctor.sigma fun _ : Unit => tick) (ℝ × ℝ) := fun _ =>
  { toFun := fun state => (MeasureCoupling.sharedGaussian variance state).map
      fun next => ((), next)
    measurable' := (Measure.measurable_map _ (by fun_prop)).comp
      (MeasureCoupling.measurable_sharedGaussian variance) }

/-- One local Gaussian transition preserves an arbitrary offset between private states. -/
noncomputable def offsetContract (variance : ℝ≥0) (offset : ℝ) :
    KernelHandler.CouplingContract (service variance) (service variance)
      (fun left right => right = left + offset) where
  joint := jointService variance
  measurable_relation := by measurability
  map_left := by
    intro a state _
    change ((MeasureCoupling.sharedGaussian variance state).map (fun next => ((), next))).map
      (fun out => (out.1, out.2.1)) =
        (gaussianReal state.1 variance).map (fun next => ((), next))
    rw [Measure.map_map (by fun_prop) (by fun_prop)]
    have h := (MeasureCoupling.sharedGaussian_isCoupling variance state).fst_eq
    rw [← h, Measure.fst, Measure.map_map (by fun_prop) measurable_fst]
    rfl
  map_right := by
    intro a state _
    change ((MeasureCoupling.sharedGaussian variance state).map (fun next => ((), next))).map
      (fun out => (out.1, out.2.2)) =
        (gaussianReal state.2 variance).map (fun next => ((), next))
    rw [Measure.map_map (by fun_prop) (by fun_prop)]
    have h := (MeasureCoupling.sharedGaussian_isCoupling variance state).snd_eq
    rw [← h, Measure.snd, Measure.map_map (by fun_prop) measurable_snd]
    rfl
  invariant := by
    intro a state hstate
    change ∀ᵐ out ∂(MeasureCoupling.sharedGaussian variance state).map
      (fun next => ((), next)), out.2.2 = out.2.1 + offset
    rw [ae_map_iff (by fun_prop) (by measurability)]
    change ∀ᵐ out ∂MeasureCoupling.sharedGaussian variance state, out.2 = out.1 + offset
    exact MeasureCoupling.sharedGaussian_ae_offset variance offset state hstate

/-- Every recursive network of these boxes preserves the offset for arbitrary random initial
states. This includes several wires sharing a single service and continuous positive variance. -/
theorem network_preserves_offset (network : Network) (variance : ℝ≥0) (offset : ℝ)
    (μ ν : Measure ℝ) (hinit : CouplingPost μ ν (fun s t => t = s + offset)) :
    CouplingPost (μ.bind (Wiring.runKernel implementation (service variance) network ()))
      (ν.bind (Wiring.runKernel implementation (service variance) network ()))
      (fun left right => right.2 = left.2 + offset) := by
  exact Wiring.bind_state_laws implementation (offsetContract variance offset) network ()
    hinit (measurableSet_eq_fun measurable_snd.snd
      (measurable_fst.snd.add measurable_const)) (fun _ _ _ h => h)

/-- The two-port wiring threads the successor state of its first call into its second call. -/
theorem twice_runKernel (variance : ℝ≥0) (state : ℝ) :
    Wiring.runKernel implementation (service variance) twice () state =
      (service variance ⟨(), ()⟩ state).bind fun out =>
        service variance ⟨(), ()⟩ out.2 := by
  let : MeasurableSpace ((PFunctor.sigma fun _ : Unit => tick).B ⟨(), ()⟩) :=
    inferInstanceAs (MeasurableSpace Unit)
  let : Countable ((PFunctor.sigma fun _ : Unit => tick).B ⟨(), ()⟩) :=
    inferInstanceAs (Countable Unit)
  let : MeasurableSingletonClass ((PFunctor.sigma fun _ : Unit => tick).B ⟨(), ()⟩) :=
    inferInstanceAs (MeasurableSingletonClass Unit)
  rw [Wiring.runKernel_eq]
  change FreeM.runKernel (service variance)
    ((FreeM.lift (P := PFunctor.sigma fun _ : Unit => tick) ⟨(), ()⟩).bind fun _ =>
      FreeM.lift (P := PFunctor.sigma fun _ : Unit => tick) ⟨(), ()⟩) state = _
  rw [FreeM.runKernel_bind, FreeM.runKernel_lift]
  simp only [FreeM.runKernel_lift]

end Examples.GaussianWiring
