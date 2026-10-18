/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import ToMathlib.MeasureTheory.MeasurableSpace.Sum
public import VCVio.EvalDist.MachineMeasure
public import VCVio.EvalDist.Trajectory
public import VCVio.EvalDist.StoppedObservation
public import PolyFun.PFunctor.Dynamical.DynComputation.History

/-!
# Infinite laws of resumable machine executions

A machine admits a path law when its initialized zero-fuel observation and its
interpreted one-step law are measurable. These obligations concern the selected
answer measures and residual observations; the syntax needs no measurable space.
Returned chunks are absorbing. Every coordinate has exactly the law of the
executable runner at that fuel, including its zero-fuel terminal observation.
-/

public section

open MeasureTheory ProbabilityTheory

namespace PFunctor.DynSystem.DynComputation

namespace Chunk

variable {S β : Type*} [MeasurableSpace S] [MeasurableSpace β]

/-- Residual observations use the coproduct measurable structure. -/
instance instMeasurableSpaceChunk : MeasurableSpace (Chunk S β) :=
  MeasurableSpace.comap sumEquiv inferInstance

/-- The residual representation agrees measurably with the standard coproduct. -/
def measurableSumEquiv : Chunk S β ≃ᵐ β ⊕ S where
  toEquiv := sumEquiv
  measurable_toFun := comap_measurable _
  measurable_invFun := measurable_comap_iff.mpr (by
    simpa only [Equiv.self_comp_symm] using measurable_id (α := β ⊕ S))

/-- The measurable equivalence uses the underlying residual sum representation. -/
@[simp] theorem measurableSumEquiv_apply (chunk : Chunk S β) :
    measurableSumEquiv chunk = sumEquiv chunk := by
  unfold measurableSumEquiv
  rfl

@[fun_prop] theorem measurable_done : Measurable (@Chunk.done S β) :=
  measurableSumEquiv.symm.measurable.comp measurable_inl

@[fun_prop] theorem measurable_paused : Measurable (@Chunk.paused S β) :=
  measurableSumEquiv.symm.measurable.comp measurable_inr

/-- A measurable observation may inspect returned values and retained states separately. -/
theorem measurable_elim {γ : Type*} [MeasurableSpace γ] {returned : β → γ} {paused : S → γ}
    (hreturned : Measurable returned) (hpaused : Measurable paused) :
    Measurable (fun chunk : Chunk S β => match chunk with
      | .done value => returned value
      | .paused state => paused state) := by
  have hsum : Measurable (Sum.elim returned paused) :=
    measurable_fun_sum hreturned hpaused
  have h := hsum.comp measurableSumEquiv.measurable
  convert h using 1
  funext chunk
  cases chunk <;> rfl

instance [MeasurableSingletonClass S] [MeasurableSingletonClass β] :
    MeasurableSingletonClass (Chunk S β) where
  measurableSet_singleton chunk := by
    have h := measurableSumEquiv.measurable (measurableSet_singleton (sumEquiv chunk))
    have heq : ⇑measurableSumEquiv ⁻¹' {sumEquiv chunk} = {chunk} := by
      ext value
      exact sumEquiv.injective.eq_iff
    rwa [heq] at h

/-- Forgetting the retained state is a measurable observation. -/
@[fun_prop] theorem measurable_result : Measurable (@result S β) := by
  have h : Measurable (fun value : β ⊕ S => value.elim some (fun _ => none)) :=
    measurable_fun_sum Option.measurable_some measurable_const
  have heq : @result S β =
      (fun value : β ⊕ S => value.elim some (fun _ => none)) ∘ measurableSumEquiv := by
    funext chunk
    cases chunk <;> rfl
  rw [heq]
  exact h.comp measurableSumEquiv.measurable

end Chunk

variable {P : PFunctor} [∀ a, MeasurableSpace (P.B a)] [P.AnswerMeasure] {α β : Type*}
  (machine : DynComputation P α β) [MeasurableSpace α]
  [MeasurableSpace (Chunk machine.State β)]

/-- Measurability of initialization and interpreted transitions for the chosen answer law. -/
structure MeasurableExecution : Prop where
  /-- Initialization includes terminal observation even when no fuel is available. -/
  initial : Measurable fun input => FreeM.denote (machine.unrollChunk 0 (machine.init input))
  /-- A returned chunk stays returned; a paused chunk performs at most one query. -/
  step : Measurable fun chunk => FreeM.denote (machine.resumeChunk 1 chunk)

namespace MeasurableExecution

variable {machine}

/-- Discrete input and residual observations discharge the measurability obligations. -/
theorem of_discrete [DiscreteMeasurableSpace α]
    [DiscreteMeasurableSpace (Chunk machine.State β)] : MeasurableExecution machine :=
  ⟨Measurable.of_discrete, Measurable.of_discrete⟩

/-- Countable separated inputs and observations need no manual measurability proofs. -/
theorem of_countable [Countable α] [MeasurableSingletonClass α]
    [Countable (Chunk machine.State β)] [MeasurableSingletonClass (Chunk machine.State β)] :
    MeasurableExecution machine :=
  ⟨measurable_of_countable _, measurable_of_countable _⟩

/-- The interpreted one-query transition, with absorbing returned outcomes. -/
noncomputable def stepKernel (h : MeasurableExecution machine) :
    Kernel (Chunk machine.State β) (Chunk machine.State β) :=
  ⟨fun chunk => FreeM.denote (machine.resumeChunk 1 chunk), h.step⟩

/-- Returned values are absorbing, independently of the residual measurable structure. -/
@[simp] theorem stepKernel_done (h : MeasurableExecution machine) (value : β) :
    h.stepKernel (.done value) = Measure.dirac (.done value) :=
  FreeM.denote_pure (P := P) _

variable [∀ a, DiscreteMeasurableSpace (P.B a)]

instance (h : MeasurableExecution machine) : IsMarkovKernel h.stepKernel :=
  ⟨fun _ => FreeM.isProbabilityMeasure_denote _⟩

/-- One more step of the path kernel is one more query of the executable runner. -/
theorem bind_stepKernel (h : MeasurableExecution machine) (fuel : ℕ) (state : machine.State) :
    (FreeM.denote (machine.unrollChunk fuel state)).bind h.stepKernel =
      FreeM.denote (machine.unrollChunk (fuel + 1) state) := by
  change (FreeM.denote (machine.unrollChunk fuel state)).bind
    (fun chunk => FreeM.denote (machine.resumeChunk 1 chunk)) = _
  rw [← FreeM.denote_bind _ _ h.step]
  exact congrArg FreeM.denote (machine.unrollChunk_add fuel 1 state)

/-- Every bounded runner law is measurable in its initialized input. -/
theorem measurable_unrollChunk (h : MeasurableExecution machine) (fuel : ℕ) :
    Measurable fun input => FreeM.denote (machine.unrollChunk fuel (machine.init input)) := by
  induction fuel with
  | zero => exact h.initial
  | succ fuel ih =>
      simp only [← h.bind_stepKernel fuel]
      exact (Measure.measurable_bind' h.stepKernel.measurable).comp ih

/-- The infinite law of actual residual execution, retaining divergence as an infinite path. -/
noncomputable def pathLaw (h : MeasurableExecution machine) (input : α) :
    Measure (ℕ → Chunk machine.State β) :=
  Kernel.pathLaw h.stepKernel (FreeM.denote (machine.unrollChunk 0 (machine.init input)))

instance (h : MeasurableExecution machine) (input : α) :
    IsProbabilityMeasure (h.pathLaw input) := by unfold pathLaw; infer_instance

/-- Every time marginal is the law of the corresponding executable chunk. -/
theorem pathLaw_map_time (h : MeasurableExecution machine) (input : α) (fuel : ℕ) :
    (h.pathLaw input).map (fun path => path fuel) =
      FreeM.denote (machine.unrollChunk fuel (machine.init input)) := by
  induction fuel with
  | zero => exact Kernel.pathLaw_map_zero _ _
  | succ fuel ih =>
      rw [pathLaw, Kernel.pathLaw_map_succ]
      change ((h.pathLaw input).map (fun path => path fuel)).bind h.stepKernel = _
      rw [ih, h.bind_stepKernel]

/-- Extending an observed history has a measurable joint law. -/
theorem measurable_historyStep (h : MeasurableExecution machine) (fuel : ℕ) :
    Measurable (fun history : Fin (fuel + 1) → Chunk machine.State β =>
      FreeM.denote (FreeM.map (Fin.snoc history : _ → Fin (fuel + 2) → _)
        (machine.resumeChunk 1 (history (Fin.last fuel))))) := by
  have hm := (h.stepKernel.comap
    (fun history : Fin (fuel + 1) → Chunk machine.State β => history (Fin.last fuel))
    (measurable_pi_apply _)).measurable_map_withInput (measurable_fin_snoc (fuel + 1))
  convert hm using 1
  funext history
  rw [FreeM.denote_map_of_measurable _ _ (measurable_fin_snoc_right history)]
  rfl

/-- Every finite joint path observation is the law of the executable saved-chunk history. -/
theorem pathLaw_map_history (h : MeasurableExecution machine) (input : α) (fuel : ℕ) :
    (h.pathLaw input).map (fun path (i : Fin (fuel + 1)) => path i) =
      FreeM.denote (machine.unrollHistory fuel (machine.init input)) := by
  induction fuel with
  | zero =>
    have hconst : Measurable (fun chunk : Chunk machine.State β => fun _ : Fin 1 => chunk) :=
      Measurable.of_eval fun _ => measurable_id
    rw [unrollHistory_zero, FreeM.denote_map_of_measurable _ _ hconst]
    have heq := congrArg (fun μ => μ.map (fun chunk => fun _ : Fin 1 => chunk))
      (h.pathLaw_map_time input 0)
    rw [Measure.map_map hconst (measurable_pi_apply 0)] at heq
    convert heq using 1
    congr 1
    funext path i
    have hi : i = 0 := Fin.ext (by omega)
    subst i
    rfl
  | succ fuel ih =>
    rw [unrollHistory_succ, ← FreeM.bind_eq_bind,
      FreeM.denote_bind _ _ (h.measurable_historyStep fuel)]
    rw [pathLaw, Kernel.pathLaw_map_fin_succ]
    change ((h.pathLaw input).map (fun path (i : Fin (fuel + 1)) => path i)).bind _ = _
    rw [ih]
    congr 1
    funext history
    exact (FreeM.denote_map_of_measurable _ _ (measurable_fin_snoc_right history)).symm

/-- Initialization and all finite joint histories vary measurably with the input. -/
theorem measurable_unrollHistory (h : MeasurableExecution machine) (fuel : ℕ) :
    Measurable fun input => FreeM.denote (machine.unrollHistory fuel (machine.init input)) := by
  induction fuel with
  | zero =>
    have hconst : Measurable (fun chunk : Chunk machine.State β => fun _ : Fin 1 => chunk) :=
      Measurable.of_eval fun _ => measurable_id
    simp only [unrollHistory_zero, FreeM.denote_map_of_measurable _ _ hconst]
    exact (Measure.measurable_map _ (Measurable.of_eval fun _ => measurable_id)).comp h.initial
  | succ fuel ih =>
    simp only [unrollHistory_succ, ← FreeM.bind_eq_bind,
      FreeM.denote_bind _ _ (h.measurable_historyStep fuel)]
    exact (Measure.measurable_bind' (h.measurable_historyStep fuel)).comp ih

/-- Executable finite histories uniquely determine the full measurable execution law. -/
theorem pathLaw_eq_of_histories (h : MeasurableExecution machine) (input : α)
    (law : Measure (ℕ → Chunk machine.State β)) [IsFiniteMeasure law]
    (hlaw : ∀ fuel, law.map (fun path (i : Fin (fuel + 1)) => path i) =
      FreeM.denote (machine.unrollHistory fuel (machine.init input))) :
    h.pathLaw input = law :=
  Measure.eq_of_fin_prefixes _ _ fun fuel => (h.pathLaw_map_history input fuel).trans
    (hlaw fuel).symm

/-- Forgetting residual states gives the coinductive cutoff observation at every fuel. -/
theorem pathLaw_map_result [MeasurableSpace β] (h : MeasurableExecution machine)
    (hresult : Measurable (@Chunk.result machine.State β)) (input : α) (fuel : ℕ) :
    (h.pathLaw input).map (fun path => (path fuel).result) =
      Resumption.truncateMeasure fuel (machine.denote input) := by
  rw [show (fun path : ℕ → Chunk machine.State β => (path fuel).result) =
    Chunk.result ∘ (fun path => path fuel) from rfl,
    ← Measure.map_map hresult (measurable_pi_apply fuel), h.pathLaw_map_time]
  exact machine.map_denote_unrollChunk hresult fuel (machine.init input)

/-- Returned observations persist almost surely along the actual machine path. -/
theorem pathLaw_ae_persistent [MeasurableSpace β] [MeasurableEq (Option β)]
    (h : MeasurableExecution machine) (hresult : Measurable (@Chunk.result machine.State β))
    (input : α) :
    ∀ᵐ path ∂h.pathLaw input, ∀ n m value, n ≤ m →
      (path n).result = some value → (path m).result = some value := by
  have hrel := Kernel.pathLaw_ae_rel h.stepKernel
    (FreeM.denote (machine.unrollChunk 0 (machine.init input)))
    (fun first second => first.result = none ∨ second.result = first.result)
    (((hresult.comp measurable_fst) Option.measurableSet_none).union
      (measurableSet_eq_fun (hresult.comp measurable_snd) (hresult.comp measurable_fst)))
    (fun chunk => ?_)
  · filter_upwards [hrel] with path hp
    intro n m value hnm hn
    induction m, hnm using Nat.le_induction with
    | base => exact hn
    | succ m hnm ih =>
        rcases hp m with hnone | heq
        · rw [ih] at hnone
          cases hnone
        · exact heq.trans ih
  · cases chunk with
    | paused state => exact Filter.Eventually.of_forall fun _ => Or.inl rfl
    | done value =>
        rw [h.stepKernel_done]
        refine (ae_dirac_iff (a := Chunk.done value) ?_).mpr ?_
        · simpa only [Chunk.result, Set.preimage, Set.mem_singleton_iff,
            Option.some_ne_none, false_or] using
            hresult (measurableSet_singleton (some value))
        · exact Or.inr rfl

/-- Eventual return on the actual execution path is the resumption's returned measure. -/
theorem returnedMeasure_eq_path_event [MeasurableSpace β] [MeasurableEq (Option β)]
    (h : MeasurableExecution machine) (hresult : Measurable (@Chunk.result machine.State β))
    (input : α) (event : Set β) (hevent : MeasurableSet event) :
    Resumption.returnedMeasure (machine.denote input) event =
      h.pathLaw input {path | ∃ n, (path n).result ∈ some '' event} :=
  Resumption.returnedMeasure_eq_observed_event_of_ae (machine.denote input)
    (h.pathLaw input) (fun n path => (path n).result)
    (fun n => hresult.comp (measurable_pi_apply n)) (h.pathLaw_ae_persistent hresult input)
    (h.pathLaw_map_result hresult input) event hevent

/-- Expected query cost counts unfinished prefixes of the actual execution path.
An infinite execution retains its waiting cost even though its returned measure has no mass. -/
theorem expectedQueries_eq_lintegral_pathCost [MeasurableSpace β]
    (h : MeasurableExecution machine) (hresult : Measurable (@Chunk.result machine.State β))
    (input : α) :
    Resumption.expectedQueries (machine.denote input) =
      ∫⁻ path, Resumption.observedQueryCost (fun n path => (path n).result) path
        ∂h.pathLaw input :=
  Resumption.expectedQueries_eq_lintegral_observedCost (machine.denote input)
    (h.pathLaw input) (fun n path => (path n).result)
    (fun n => hresult.comp (measurable_pi_apply n)) (h.pathLaw_map_result hresult input)

end MeasurableExecution
end PFunctor.DynSystem.DynComputation
