/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Examples.MeasurableServices.UniformTernary
public import VCVio.EvalDist.Trajectory
public import PolyFun.ITree.Unfold

/-!
# A reactive dyadic threshold client

The client repeatedly asks for the midpoint of its current interval and keeps
its selected half. Its `DynSystem`, terminal-coalgebra behavior, cofree
trajectory, and nonreturning ITree are existing PolyFun models of one client.
Finite observations compile to fair-bit service machines. The completed-call
transition is exactly one fair bit, and its full product-space path law equals
the posterior-reconstructed ideal path law. This clock counts completed calls,
not dispatcher transitions or wall time.
-/

public section

open MeasureTheory ProbabilityTheory PFunctor UniformThreshold

namespace ReactiveThreshold

attribute [local instance] UniformThreshold.answerMeasurableSpace

/-- The continuing client has no final outputs. -/
@[instance_reducible] def emptyResultSpace : MeasurableSpace PEmpty := ⊤

/-- Finite public histories carry their discrete sigma algebra. -/
@[instance_reducible] def historySpace : MeasurableSpace (List Prefix) := ⊤

attribute [local instance] emptyResultSpace historySpace

local instance historyDiscreteMeasurableSpace : DiscreteMeasurableSpace (List Prefix) :=
  ⟨fun _ => MeasurableSpace.measurableSet_top⟩

/-- The exact rational boundary between the two child cells. -/
@[expose] def midpoint (p : Prefix) : ℚ := (p.push false).upper

/-- A true threshold answer selects the lower half. -/
@[expose] def advance (p : Prefix) (answer : Bool) : Prefix := p.push (!answer)

/-- An indefinitely interacting adaptive client. -/
@[expose] def system : DynSystem Prefix spec.toPFunctor :=
  DynSystem.mk' midpoint advance

/-- The cofree trajectory and terminal-coalgebra behavior encode the same client. -/
theorem trajectory_eq (p : Prefix) :
    system.trajectory p = M.selfLabel (system.behavior p) :=
  system.trajectory_eq_selfLabel_behavior p

/-- The interaction-tree view uses the canonical embedding of the same behavior. -/
theorem toITree_eq (p : Prefix) :
    system.toITree p = M.toITree (system.behavior p) :=
  system.toITree_eq_toITree_behavior p

/-- The midpoint query always needs a bit from the current cell. -/
theorem classify_midpoint (p : Prefix) : classify (midpoint p) p = none := by
  apply (classify_eq_none_iff _ _).mpr
  constructor
  · simpa only [midpoint, Prefix.lower_push_false] using (p.push false).lower_lt_upper
  · simpa only [midpoint, Prefix.upper_push_false_eq_lower_push_true,
      Prefix.upper_push_true] using (p.push true).lower_lt_upper

/-- After one bit the midpoint query resolves, retaining exactly the refined cell. -/
theorem classify_midpoint_push (p : Prefix) (b : Bool) :
    classify (midpoint p) (p.push b) = some (!b) := by
  cases b
  · simp [classify, midpoint]
  · have h : ¬ (p.push true).upper ≤ midpoint p := by
      rw [midpoint, Prefix.upper_push_false_eq_lower_push_true]
      exact not_le.mpr (p.push true).lower_lt_upper
    rw [classify, ite_eq_right h]
    simp only [midpoint, Prefix.upper_push_false_eq_lower_push_true, le_refl, ↓reduceIte]
    rfl

/-- The completed-call kernel is one fair bit, with its actual retained service state. -/
theorem answer_midpoint (p : Prefix) :
    answerKernel (midpoint p) p =
      (PFunctor.AnswerMeasure.toMeasure (P := coinSpec.toPFunctor) ()).map
        (fun b : Bool => (!b, p.push b)) := by
  rw [answerKernel_apply]
  have root := (machine (midpoint p)).dest_denote p
  change Resumption.dest ((machine (midpoint p)).denote p) =
    Sum.map (fun value => value)
      (coinSpec.toPFunctor.map (machine (midpoint p)).toDynSystem.behavior)
      ((machine (midpoint p)).view p) at root
  rw [machine_view, classify_midpoint] at root
  have tree : (machine (midpoint p)).denote p =
      Resumption.query () (fun b => Resumption.pure (!b, p.push b)) := by
    apply Resumption.eq_of_dest_eq
    rw [root, Resumption.dest_query]
    apply congrArg Sum.inr
    change (PFunctor.Obj.mk (P := coinSpec.toPFunctor) ()
      (fun b => (machine (midpoint p)).toDynSystem.behavior (p.push b))) = _
    apply congrArg (PFunctor.Obj.mk (P := coinSpec.toPFunctor) ())
    funext b
    apply Resumption.eq_of_dest_eq
    rw [DynSystem.DynComputation.dest_behavior_view, machine_view,
      classify_midpoint_push, Resumption.dest_pure]
    rfl
  rw [tree, Resumption.returnedMeasure_query (P := coinSpec.toPFunctor)]
  simp_rw [Resumption.returnedMeasure_pure]
  exact Measure.bind_dirac_eq_map _ Measurable.of_discrete

/-- A finite observation of the continuing client, retaining the ordered public history. -/
@[expose] def observe : ℕ → Prefix → FreeM spec.toPFunctor (List Prefix)
  | 0, _ => pure []
  | n + 1, p => .liftBind (system.expose p) fun answer =>
      let next := system.update p answer
      (observe n next).map (next :: ·)

/-- Every finite observation has one executable composed fair-bit machine. -/
@[expose] def compiled (n : ℕ) := machineHandler.compile (observe n)

/-- The compiled history law equals observation of one persistent ideal real. -/
theorem compiled_history_law (n : ℕ) (p : Prefix) :
    (𝒟[ITree.ofResumptionWithTau ((compiled n).denote (p, p))]).map Prod.fst =
      ((cellLaw p).bind (FreeM.runKernel idealAnswer (observe n p))).map Prod.fst := by
  rw [compiled, machineHandler.evalDist_compile answerKernel machineHandler_realizes]
  exact (adaptive_output_law (observe n p) p).symm

/-- A completed call advances both public and private intervals by the sampled bit. -/
noncomputable def completedStep : Kernel Prefix Prefix where
  toFun p := (answerKernel (midpoint p) p).map Prod.snd
  measurable' := Measurable.of_discrete

instance : IsMarkovKernel completedStep :=
  ⟨fun p => by change IsProbabilityMeasure ((answerKernel (midpoint p) p).map Prod.snd)
               infer_instance⟩

/-- Completed calls form the usual fair dyadic refinement chain. -/
theorem completedStep_apply (p : Prefix) :
    completedStep p =
      (PFunctor.AnswerMeasure.toMeasure (P := coinSpec.toPFunctor) ()).map p.push := by
  change ((answerKernel (midpoint p) p).map Prod.snd) = _
  rw [answer_midpoint, Measure.map_map measurable_snd Measurable.of_discrete]
  rfl

/-- The ideal completed-call transition reconstructs the real from its current cell. -/
noncomputable def idealStep : Kernel Prefix Prefix where
  toFun p := ((cellLaw p).bind (idealAnswer (midpoint p))).map
    (fun result => advance p result.1)
  measurable' := Measurable.of_discrete

/-- Posterior reconstruction yields exactly the actual completed-call transition. -/
theorem idealStep_eq : idealStep = completedStep := by
  ext p : 1
  have h := adaptive_output_law (FreeM.lift (P := spec.toPFunctor) (midpoint p)) p
  have hkernel : FreeM.runKernel idealAnswer (FreeM.lift (P := spec.toPFunctor) (midpoint p)) =
      idealAnswer (midpoint p) := by
    ext u : 1
    exact FreeM.runKernel_lift (P := spec.toPFunctor) idealAnswer (midpoint p) u
  rw [hkernel, FreeM.runKernel_lift (P := spec.toPFunctor)] at h
  have hm : Measurable (advance p) := Measurable.of_discrete
  have hm' : Measurable (fun result : Bool × Prefix => advance p result.1) :=
    hm.comp measurable_fst
  have h' := congrArg (Measure.map (advance p)) h
  rw [Measure.map_map hm measurable_fst, Measure.map_map hm measurable_fst,
    answer_midpoint] at h'
  simp only [Function.comp_def] at h'
  rw [Measure.map_map hm' Measurable.of_discrete] at h'
  change idealStep p = completedStep p
  rw [completedStep_apply]
  change ((cellLaw p).bind (idealAnswer (midpoint p))).map
    (fun result => advance p result.1) = _
  simpa only [advance, Function.comp_def, Bool.not_not] using h'

instance : IsMarkovKernel idealStep := by rw [idealStep_eq]; infer_instance

/-- Full path laws agree on the product sigma algebra, not only on point events. -/
theorem pathLaw_eq (p : Prefix) :
    Kernel.pathLaw idealStep (Measure.dirac p) =
      Kernel.pathLaw completedStep (Measure.dirac p) := by simp only [idealStep_eq]

/-- A continuing client's empty return type has zero returned law even while its path evolves. -/
theorem returnedMeasure_eq_zero (p : Prefix) :
    ITree.returnedMeasure
      ((ITree.interp machineHandler.toITreeHandler (system.toITree p)).run p) = 0 := by
  apply Measure.ext
  intro event _
  have : event = ∅ := Set.eq_empty_iff_forall_notMem.mpr fun x => PEmpty.elim x.1
  simp [this]

end ReactiveThreshold
