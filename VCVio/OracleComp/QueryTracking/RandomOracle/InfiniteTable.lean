/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module
public import VCVio.ProgramLogic.Relational.Reconstruction
public import VCVio.OracleComp.QueryTracking.ListCache
public import ToMathlib.Probability.InfiniteTable.Resampling
public import VCVio.OracleComp.Constructions.SampleableType.Measure

/-!
# A lazy list cache represents an infinite random function

The reconstruction kernel fills all uncached keys independently. Its commuting law retains
both the answer and the complete ideal table, and therefore composes for adaptive clients.
The ideal state uses the product σ-algebra; the concrete state is a finite association list.
First bindings win, including when an initial list has shadowed duplicate keys.
-/

public section

open MeasureTheory ProbabilityTheory PFunctor OracleSpec

namespace QueryImpl.ListCache

variable {D A : Type} [DecidableEq D]

/-- Fill the missing keys of a list cache from a total table. -/
def complete (cache : List (D × A)) (g : D → A) (d : D) : A :=
  (cache.lookup d).getD (g d)

/-- Completion is measurable for the product σ-algebra. -/
theorem measurable_complete [MeasurableSpace A] (cache : List (D × A)) :
    Measurable (complete cache) := by
  apply Measurable.of_eval
  intro d
  unfold complete
  cases cache.lookup d <;> simp only [Option.getD] <;> fun_prop

/-- A newly stored entry overwrites precisely its coordinate of the completed table. -/
theorem complete_cons (cache : List (D × A)) (q : D) (r : A) (g : D → A) :
    complete ((q, r) :: cache) g = Function.update (complete cache g) q r := by
  funext d
  by_cases h : d = q
  · subst d; simp [complete]
  · simp [complete, List.lookup_cons, beq_eq_false_iff_ne.mpr h, h]

/-- Updating an uncached coordinate commutes with completion. -/
theorem complete_update (cache : List (D × A)) {q : D} (hq : cache.lookup q = none)
    (r : A) (g : D → A) :
    complete cache (Function.update g q r) = Function.update (complete cache g) q r := by
  funext d
  by_cases h : d = q
  · subst d; simp [complete, hq]
  · simp [complete, Function.update_of_ne h]

variable [MeasurableSpace A]

/-- The finite cache is discrete even when no measurable space is chosen for the key type. -/
local instance cacheMeasurableSpace : MeasurableSpace (List (D × A)) := ⊤
local instance : DiscreteMeasurableSpace (List (D × A)) :=
  ⟨fun _ => MeasurableSpace.measurableSet_top⟩
/-- Each lookup returns an element of the chosen measurable answer space. -/
local instance lookupAnswerMeasurableSpace :
    (q : (D →ₒ A).toPFunctor.A) → MeasurableSpace ((D →ₒ A).toPFunctor.B q) :=
  fun _ => inferInstanceAs (MeasurableSpace A)

/-- The posterior ideal table given the currently stored answers. -/
noncomputable def reconstruction : Kernel (List (D × A)) (D → A) :=
  ⟨fun cache => Measure.uniformTable.map (complete cache), Measurable.of_discrete⟩

instance [Finite A] [Nonempty A] : IsMarkovKernel (reconstruction (D := D) (A := A)) := by
  constructor
  intro cache
  change IsProbabilityMeasure (Measure.uniformTable.map (complete cache))
  infer_instance

/-- The empty cache represents the independent infinite uniform table. -/
theorem reconstruction_nil : reconstruction ([] : List (D × A)) = Measure.uniformTable := by
  change Measure.uniformTable.map (complete []) = _
  have h : complete ([] : List (D × A)) = id := by funext g d; simp [complete]
  rw [h, Measure.map_id]

variable [Finite A] [Nonempty A] [MeasurableSingletonClass A]

/-- The kernel semantics of reusing a first binding or drawing and prepending on a miss. -/
noncomputable def cachedKernel (q : D) : Kernel (List (D × A)) (A × List (D × A)) :=
  ⟨fun cache => match cache.lookup q with
    | some r => Measure.dirac (r, cache)
    | none => (uniformOn (Set.univ : Set A)).map (fun r => (r, (q, r) :: cache)),
    Measurable.of_discrete⟩

instance (q : D) : IsMarkovKernel (cachedKernel (A := A) q) := by
  constructor
  intro cache
  change IsProbabilityMeasure (match cache.lookup q with
    | some r => Measure.dirac (r, cache)
    | none => (uniformOn (Set.univ : Set A)).map (fun r => (r, (q, r) :: cache)))
  cases cache.lookup q <;> infer_instance

omit [Finite A] [Nonempty A] in
/-- The concrete kernel is the measure of the existing executable association-list handler. -/
theorem cachedKernel_eq_evalDist [SampleableType A] (q : D) (cache : List (D × A)) :
    cachedKernel q cache = 𝒟[handler (fun _ => ($ᵗ A : ProbComp A)) q cache] := by
  simp only [cachedKernel, Kernel.coe_mk, handler]
  cases cache.lookup q with
  | some r => exact (evalDist_pure _).symm
  | none =>
      rw [evalDist_map_of_discrete, SampleableType.evalDist_uniformSample]

/-- The ideal service reads the persistent total table. -/
noncomputable def tableKernel (q : D) : Kernel (D → A) (A × (D → A)) :=
  Kernel.deterministic (fun g => (g q, g)) ((measurable_pi_apply q).prodMk measurable_id)

/-- One lazy cached query commutes with reconstructing the complete ideal table. -/
theorem cached_reconstruction_step (q : D) (cache : List (D × A)) :
    (reconstruction cache).bind (tableKernel q) =
      (cachedKernel q cache).bind (Kernel.retainLeft A reconstruction) := by
  change (Measure.uniformTable.map (complete cache)).bind
    (fun g => Measure.dirac (g q, g)) = _
  have hread : Measurable (fun g : D → A => (g q, g)) :=
    (measurable_pi_apply q).prodMk measurable_id
  rw [Measure.bind_dirac_eq_map _ hread,
    Measure.map_map hread (measurable_complete cache)]
  simp only [cachedKernel, Kernel.coe_mk]
  cases hc : cache.lookup q with
  | some r =>
      change _ = (Measure.dirac (r, cache)).bind (Kernel.retainLeft A reconstruction)
      rw [Measure.dirac_bind (Kernel.retainLeft A reconstruction).measurable,
        Kernel.retainLeft_apply]
      change _ = (Measure.uniformTable.map (complete cache)).map (Prod.mk r)
      rw [Measure.map_map measurable_prodMk_left (measurable_complete cache)]
      congr 1
      funext g
      simp [complete, hc]
  | none =>
      change _ = ((uniformOn (Set.univ : Set A)).map
        (fun r => (r, (q, r) :: cache))).bind (Kernel.retainLeft A reconstruction)
      rw [Measure.bind_map Measurable.of_discrete.aemeasurable
        (Kernel.retainLeft A reconstruction).aemeasurable]
      have hm : Measurable (fun p : A × (D → A) => (p.1, complete cache p.2)) :=
        measurable_fst.prodMk ((measurable_complete cache).comp measurable_snd)
      have h := congrArg (fun μ : Measure (A × (D → A)) =>
        μ.map (fun p => (p.1, complete cache p.2))) (Measure.uniformTable_bind_update (A := A) q)
      rw [Measure.map_bind Measurable.of_discrete.aemeasurable hm.aemeasurable,
        Measure.map_map hm hread] at h
      calc
        _ = Measure.uniformTable.map (fun g : D → A => (g q, complete cache g)) := by
          congr 1; funext g; simp [complete, hc]
        _ = _ := h.symm.trans (by
          apply Measure.bind_congr_right
          apply Filter.Eventually.of_forall
          intro r
          dsimp only
          rw [Kernel.retainLeft_apply]
          change (Measure.uniformTable.map (fun g => (r, Function.update g q r))).map
            (fun p => (p.1, complete cache p.2)) =
              (Measure.uniformTable.map (complete ((q, r) :: cache))).map (Prod.mk r)
          rw [Measure.map_map hm (by fun_prop),
            Measure.map_map measurable_prodMk_left (measurable_complete _)]
          simp only [Function.comp_def, complete_update cache hc, complete_cons])

/-- Infinite eager and finite lazy states satisfy the generic adaptive reconstruction rule. -/
theorem reconstructionContract :
    KernelHandler.ReconstructionContract (P := (D →ₒ A).toPFunctor)
      cachedKernel tableKernel reconstruction := by
  refine ⟨inferInstance, fun q => ?_⟩
  ext cache : 1
  exact cached_reconstruction_step q cache

/-- Every adaptive terminating client sees the same output law from either representation. -/
theorem infiniteTable_output_law {X : Type} [MeasurableSpace X]
    (client : FreeM (D →ₒ A).toPFunctor X) :
    (Measure.uniformTable.bind (FreeM.runKernel tableKernel client)).map Prod.fst =
      (FreeM.runKernel cachedKernel client []).map Prod.fst := by
  have h := (reconstructionContract (D := D) (A := A)).output_law
    (Measure.dirac []) client
  simpa only [Measure.dirac_bind reconstruction.measurable, reconstruction_nil,
    Measure.dirac_bind (FreeM.runKernel cachedKernel client).measurable] using h

end QueryImpl.ListCache
