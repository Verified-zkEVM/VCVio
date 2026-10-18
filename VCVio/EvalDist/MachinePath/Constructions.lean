/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import VCVio.EvalDist.MachinePath
public import PolyFun.PFunctor.Dynamical.DynComputation.ResumableMap

/-!
# Measurable machine wrappers

Measurable input and result maps transport execution certificates. The syntax
laws retain exact residual states and all history coordinates; no new interpreter
or measurable structure on computation syntax is needed.
-/

public section

open MeasureTheory ProbabilityTheory

namespace PFunctor.DynSystem.DynComputation

namespace Chunk

/-- A measurable residual observation may also inspect an external parameter. -/
theorem measurable_elim_withInput {T S β γ : Type*}
    [MeasurableSpace T] [MeasurableSpace S] [MeasurableSpace β] [MeasurableSpace γ]
    {returned : T × β → γ} {paused : T × S → γ}
    (hreturned : Measurable returned) (hpaused : Measurable paused) :
    Measurable (fun input : T × Chunk S β => match input.2 with
      | .done value => returned (input.1, value)
      | .paused state => paused (input.1, state)) := by
  have hsum : Measurable (Sum.elim returned paused) := measurable_fun_sum hreturned hpaused
  have h := hsum.comp
    ((MeasurableEquiv.prodSumDistrib T β S).measurable.comp
      (measurable_fst.prodMk (measurableSumEquiv.measurable.comp measurable_snd)))
  convert h using 1
  funext input
  rcases input with ⟨param, chunk⟩
  cases chunk <;> simp only [Function.comp_apply, measurableSumEquiv_apply, sumEquiv] <;> rfl

/-- The two branches of a mapped chunk may depend measurably on external input. -/
theorem measurable_map_withInput {I S T β γ : Type*}
    [MeasurableSpace I] [MeasurableSpace S] [MeasurableSpace T]
    [MeasurableSpace β] [MeasurableSpace γ]
    {state : I × S → T} {result : I × β → γ}
    (hstate : Measurable state) (hresult : Measurable result) :
    Measurable (fun input : I × Chunk S β =>
      input.2.map (fun s => state (input.1, s)) (fun value => result (input.1, value))) := by
  convert measurable_elim_withInput (measurable_done.comp hresult)
    (measurable_paused.comp hstate) using 1
  funext input
  rcases input with ⟨param, chunk⟩
  cases chunk <;> rfl

/-- State and result observations may be mapped separately and measurably. -/
@[fun_prop] theorem measurable_map {S T β γ : Type*}
    [MeasurableSpace S] [MeasurableSpace T] [MeasurableSpace β] [MeasurableSpace γ]
    {state : S → T} {result : β → γ} (hstate : Measurable state) (hresult : Measurable result) :
    Measurable (Chunk.map state result) := by
  convert Chunk.measurable_elim (Chunk.measurable_done.comp hresult)
    (Chunk.measurable_paused.comp hstate) using 1
  funext chunk
  cases chunk <;> rfl

end Chunk

variable {P : PFunctor} [∀ a, MeasurableSpace (P.B a)] [P.AnswerMeasure] {α β γ : Type*}
  {machine : DynComputation P α β} [MeasurableSpace α] [MeasurableSpace β]
  [MeasurableSpace γ] [MeasurableSpace machine.State]

namespace MeasurableExecution

/-- A measurable input adapter reuses the same transition certificate. -/
theorem contramapInput (h : MeasurableExecution machine) (f : γ → α) (hf : Measurable f) :
    MeasurableExecution (machine.contramapInput f) where
  initial := by
    simp only [unrollChunk_contramapInput]
    exact h.initial.comp hf
  step := by
    simpa only [resumeChunk_contramapInput] using h.step

variable [∀ a, DiscreteMeasurableSpace (P.B a)]

/-- A measurable result adapter retains the original residual-state transitions. -/
theorem mapResult (h : MeasurableExecution machine) (f : β → γ) (hf : Measurable f) :
    MeasurableExecution (machine.mapResult f) where
  initial := by
    simp only [unrollChunk_mapResult,
      FreeM.denote_map_of_measurable _ _ (Chunk.measurable_map measurable_id hf)]
    exact (Measure.measurable_map _ (Chunk.measurable_map measurable_id hf)).comp h.initial
  step := by
    have hdone : Measurable (fun value : γ =>
        FreeM.denote ((machine.mapResult f).resumeChunk 1 (.done value))) := by
      change Measurable (fun value : γ => FreeM.denote (pure (.done value) :
        FreeM P (Chunk machine.State γ)))
      simp only [FreeM.denote_pure]
      exact Measure.measurable_dirac.comp
        (Chunk.measurable_done (S := machine.State) (β := γ))
    have hpaused : Measurable (fun state : machine.State =>
        FreeM.denote ((machine.mapResult f).resumeChunk 1 (.paused state))) := by
      have hm := (Measure.measurable_map (Chunk.map id f)
        (Chunk.measurable_map measurable_id hf)).comp (h.step.comp Chunk.measurable_paused)
      convert hm using 1
      funext state
      rw [resumeChunk_paused, unrollChunk_mapResult,
        FreeM.denote_map_of_measurable _ _ (Chunk.measurable_map measurable_id hf)]
      rfl
    convert Chunk.measurable_elim hdone hpaused using 1
    funext chunk
    cases chunk <;> rfl

/-- A measurable input adapter transports the whole path law by substitution. -/
theorem pathLaw_contramapInput (h : MeasurableExecution machine) (f : γ → α)
    (hf : Measurable f) (input : γ) :
    (h.contramapInput f hf).pathLaw input = h.pathLaw (f input) := by
  apply Measure.eq_of_fin_prefixes
  intro fuel
  rw [(h.contramapInput f hf).pathLaw_map_history,
    h.pathLaw_map_history, unrollHistory_contramapInput]
  rfl

/-- Mapping returned values acts pointwise on the full path, retaining every residual state. -/
theorem pathLaw_mapResult (h : MeasurableExecution machine) (f : β → γ)
    (hf : Measurable f) (input : α) :
    (h.mapResult f hf).pathLaw input =
      (h.pathLaw input).map (fun path n => (path n).map id f) := by
  have hpath : Measurable (fun path : ℕ → Chunk machine.State β =>
      fun n => (path n).map id f) :=
    Measurable.of_eval fun n =>
      (Chunk.measurable_map measurable_id hf).comp (measurable_pi_apply n)
  apply Measure.eq_of_fin_prefixes
  intro fuel
  have hprefix : Measurable (fun path : ℕ → Chunk machine.State γ =>
      fun i : Fin (fuel + 1) => path i) :=
    Measurable.of_eval fun i => measurable_pi_apply i.val
  have hmap : Measurable (fun history : Fin (fuel + 1) → Chunk machine.State β =>
      fun i => (history i).map id f) :=
    Measurable.of_eval fun i =>
      (Chunk.measurable_map measurable_id hf).comp (measurable_pi_apply i)
  rw [(h.mapResult f hf).pathLaw_map_history, unrollHistory_mapResult,
    FreeM.denote_map_of_measurable _ _ hmap, mapResult_init,
    ← h.pathLaw_map_history, Measure.map_map hprefix hpath,
    Measure.map_map hmap (Measurable.of_eval fun i => measurable_pi_apply i.val)]
  rfl

end MeasurableExecution
end PFunctor.DynSystem.DynComputation
