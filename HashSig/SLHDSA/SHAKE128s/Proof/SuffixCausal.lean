/-
Copyright (c) 2026 Tom Wambsgans. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Wambsgans
-/

module

public import HashSig.SLHDSA.SHAKE128s.Proof.FusedTape
import VCVio.OracleComp.EvalDist.Sum

/-!
# Reaching a target cell does not read any cell at or after it

Whether a run reaches target cell `index` does not move when any cell `cell ≥ index` of the
target tape is overwritten (`probEvent_length_setGe_cont`, with its fused and three-stage forms
`probEvent_length_setGe_fused` and `probEvent_length_setGe_threeStage`). The second-order
coverage charge (`FiredCoverage.prob_firedCovered_le`) needs this: the pair charge redraws the
*later* of two cells while holding the selection of the earlier one, and the later cell is read
only after the earlier was reached.

The one case worth noting is the step that consumes the head of the block: at `index = 0` the
run has reached its cell whatever the head is, and at `index = i + 1` the overwritten cell is
past the head too, so both drop by one together.
-/

@[expose] public section

open OracleComp OracleSpec ENNReal


namespace SlhDsaSecurity.SuffixCausal

variable {α β γ : Type}

open DigestTape TapeFactor NoticingTape RecorderView PhaseFusion FusedTape

variable {σ : Type} [CacheView σ]

open scoped Classical in
/-- **Overwriting a cell at or after the selected one does not move the selection**, with a
continuation. -/
theorem probEvent_length_setGe_cont (leftKeep rightKeep : Bytes → σ → Prop)
    {α γ : Type} (computation : OracleComp OracleWorld α)
    (after : α × SplitTapeState σ → ProbComp γ) (finalRight : γ → Record)
    (hgrow : ∀ (z : α × SplitTapeState σ) (w : γ), w ∈ support (after z) ->
      (rightOf z.2).length ≤ (finalRight w).length)
    (hfail : ∀ z, prFail (after z) = 0)
    (hafter : ∀ (index cell : Nat), index ≤ cell → ∀ (newValue : HashOutput)
        (z : α × SplitTapeState σ),
      Pr{let w ← after z}[(rightOf z.2).length + index < (finalRight w).length] =
        Pr{let w ← after (z.1, (z.2.1, (z.2.2.1.1, z.2.2.1.2.set cell newValue), z.2.2.2))}[
          (rightOf z.2).length + index < (finalRight w).length]) :
    ∀ (index cell : Nat), index ≤ cell → ∀ (newValue : HashOutput) (cache : σ)
      (leftTape rightTape : List HashOutput) (leftRecord rightRecord : Record),
      Pr{let w ← ((simulateQ (noticingSplitTapeRecorder leftKeep rightKeep) computation).run
            (cache, (leftTape, rightTape), (leftRecord, rightRecord)) >>= after)}[
          rightRecord.length + index < (finalRight w).length] =
        Pr{let w ← ((simulateQ (noticingSplitTapeRecorder leftKeep rightKeep) computation).run
            (cache, (leftTape, rightTape.set cell newValue), (leftRecord, rightRecord))
              >>= after)}[rightRecord.length + index < (finalRight w).length] := by
  classical
  induction computation using OracleComp.inductionOn with
  | pure value =>
    intro index cell hle newValue cache leftTape rightTape leftRecord rightRecord
    simp only [simulateQ_pure, StateT.run_pure, pure_bind]
    exact hafter index cell hle newValue
      (value, (cache, (leftTape, rightTape), (leftRecord, rightRecord)))
  | query_bind queried next ih =>
    intro index cell hle newValue cache leftTape rightTape leftRecord rightRecord
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, bind_assoc]
    rcases queried with coin | input
    · simp only [noticingSplitTapeRecorder_run_inl, splitTapeRecorder_run_inl, bind_assoc,
        pure_bind]
      rw [OracleComp.prEvent_bind_eq_tsum, OracleComp.prEvent_bind_eq_tsum]
      exact tsum_congr fun answer => congrArg _
        (ih answer index cell hle newValue cache leftTape rightTape leftRecord rightRecord)
    · simp only [noticingSplitTapeRecorder_run_inr]
      set noticed : σ := CacheView.onQuery cache input with hnoticed
      by_cases hfresh : CacheView.cacheOf noticed input = none
      · by_cases hleft : leftKeep input noticed
        · cases leftTape with
          | nil =>
            simp only [splitTapeRecorder_run_left_nil leftKeep rightKeep input noticed _
              leftRecord rightRecord hfresh hleft, bind_assoc, pure_bind]
            rw [OracleComp.prEvent_bind_eq_tsum, OracleComp.prEvent_bind_eq_tsum]
            exact tsum_congr fun answer => congrArg _
              (ih answer index cell hle newValue (CacheView.update noticed input answer) []
                rightTape (leftRecord ++ [(input, answer)]) rightRecord)
          | cons head rest =>
            simp only [splitTapeRecorder_run_left_cons leftKeep rightKeep input noticed head rest
              _ leftRecord rightRecord hfresh hleft, pure_bind]
            exact ih head index cell hle newValue (CacheView.update noticed input head) rest
              rightTape (leftRecord ++ [(input, head)]) rightRecord
        · by_cases hright : rightKeep input noticed
          · cases rightTape with
            | nil => simp only [List.set_nil]
            | cons head rest =>
              cases index with
              | zero =>
                cases cell with
                | zero =>
                  simp only [List.set_cons_zero,
                    splitTapeRecorder_run_right_cons leftKeep rightKeep input noticed leftTape _ _
                      leftRecord rightRecord hfresh hleft hright, pure_bind, Nat.add_zero]
                  rw [probEvent_length_eq_one_cont leftKeep rightKeep (next head) after
                      finalRight hgrow hfail (CacheView.update noticed input head)
                      (leftTape, rest) leftRecord rightRecord (input, head) rightRecord.length
                      (by simp),
                    probEvent_length_eq_one_cont leftKeep rightKeep (next newValue) after
                      finalRight hgrow hfail (CacheView.update noticed input newValue)
                      (leftTape, rest) leftRecord rightRecord (input, newValue)
                      rightRecord.length (by simp)]
                | succ later =>
                  simp only [List.set_cons_succ,
                    splitTapeRecorder_run_right_cons leftKeep rightKeep input noticed leftTape _ _
                      leftRecord rightRecord hfresh hleft hright, pure_bind, Nat.add_zero]
                  rw [probEvent_length_eq_one_cont leftKeep rightKeep (next head) after
                      finalRight hgrow hfail (CacheView.update noticed input head)
                      (leftTape, rest) leftRecord rightRecord (input, head) rightRecord.length
                      (by simp),
                    probEvent_length_eq_one_cont leftKeep rightKeep (next head) after
                      finalRight hgrow hfail (CacheView.update noticed input head)
                      (leftTape, rest.set later newValue) leftRecord rightRecord (input, head)
                      rightRecord.length (by simp)]
              | succ remaining =>
                cases cell with
                | zero => exact absurd hle (by omega)
                | succ later =>
                  simp only [List.set_cons_succ,
                    splitTapeRecorder_run_right_cons leftKeep rightKeep input noticed leftTape head
                      _ leftRecord rightRecord hfresh hleft hright, pure_bind]
                  have hlength : rightRecord.length + (remaining + 1) =
                      (rightRecord ++ [(input, head)]).length + remaining := by
                    simp only [List.length_append, List.length_cons, List.length_nil]
                    omega
                  rw [hlength]
                  exact ih head remaining later (by omega) newValue
                    (CacheView.update noticed input head) leftTape rest leftRecord
                    (rightRecord ++ [(input, head)])
          · simp only [splitTapeRecorder_run_other leftKeep rightKeep input noticed _
              (leftRecord, rightRecord) (fun h => hleft h.2) (fun h => hright h.2),
              bind_assoc, pure_bind]
            rw [OracleComp.prEvent_bind_eq_tsum, OracleComp.prEvent_bind_eq_tsum]
            exact tsum_congr fun step => congrArg _
              (ih step.1 index cell hle newValue step.2 leftTape rightTape leftRecord rightRecord)
      · simp only [splitTapeRecorder_run_other leftKeep rightKeep input noticed _
          (leftRecord, rightRecord) (fun h => hfresh h.1) (fun h => hfresh h.1),
          bind_assoc, pure_bind]
        rw [OracleComp.prEvent_bind_eq_tsum, OracleComp.prEvent_bind_eq_tsum]
        exact tsum_congr fun step => congrArg _
          (ih step.1 index cell hle newValue step.2 leftTape rightTape leftRecord rightRecord)

variable {ω : Type} [Monoid ω]

open scoped Classical in
/-- **The same, at the fused handler.** -/
theorem probEvent_length_setGe_fused (leftKeep rightKeep : Bytes → σ → Prop)
    (inner : QueryImpl (OracleWorld + Security.SigningSpec)
      (WriterT ω (StateT Security.SigningLog (OracleComp OracleWorld))))
    (before : Message → σ → σ) (afterMap : σ → σ)
    {α γ : Type} (phase : OracleComp (OracleWorld + Security.SigningSpec) α)
    (cont : α × (ω × Security.SigningLog × SplitTapeState σ) → ProbComp γ)
    (finalRight : γ → Record)
    (hgrow : ∀ (z : α × (ω × Security.SigningLog × SplitTapeState σ))
        (w : γ), w ∈ support (cont z) ->
      (rightOf z.2.2.2).length ≤ (finalRight w).length)
    (hfail : ∀ z, prFail (cont z) = 0)
    (hcont : ∀ (index cell : Nat), index ≤ cell → ∀ (newValue : HashOutput)
        (z : α × (ω × Security.SigningLog × SplitTapeState σ)),
      Pr{let w ← cont z}[(rightOf z.2.2.2).length + index < (finalRight w).length] =
        Pr{let w ← cont (z.1, (z.2.1, z.2.2.1, setRightTape cell newValue z.2.2.2))}[
          (rightOf z.2.2.2).length + index < (finalRight w).length]) :
    ∀ (index cell : Nat), index ≤ cell → ∀ (newValue : HashOutput) (accumulated : ω)
      (log : Security.SigningLog)
      (cache : σ) (leftTape rightTape : List HashOutput) (leftRecord rightRecord : Record),
      Pr{let w ← ((simulateQ (fuseServing (noticingSplitTapeRecorder leftKeep rightKeep) inner
            (fun request => onCarrierTape (before request)) (onCarrierTape afterMap))
            phase).run (accumulated, log, (cache, (leftTape, rightTape),
              (leftRecord, rightRecord))) >>= cont)}[
          rightRecord.length + index < (finalRight w).length] =
        Pr{let w ← ((simulateQ (fuseServing (noticingSplitTapeRecorder leftKeep rightKeep) inner
            (fun request => onCarrierTape (before request)) (onCarrierTape afterMap))
            phase).run (accumulated, log, (cache, (leftTape, rightTape.set cell newValue),
              (leftRecord, rightRecord))) >>= cont)}[
          rightRecord.length + index < (finalRight w).length] := by
  classical
  induction phase using OracleComp.inductionOn with
  | pure value =>
    intro index cell hle newValue accumulated log cache leftTape rightTape leftRecord
      rightRecord
    simp only [simulateQ_pure, StateT.run_pure, pure_bind]
    exact hcont index cell hle newValue
      (value, (accumulated, log, (cache, (leftTape, rightTape), (leftRecord, rightRecord))))
  | query_bind queried next ih =>
    intro index cell hle newValue accumulated log cache leftTape rightTape leftRecord
      rightRecord
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, bind_assoc]
    rcases queried with world | request
    · simp only [FusedTape.fuseServing_run_inl, bind_assoc, pure_bind]
      exact probEvent_length_setGe_cont leftKeep rightKeep
        (((inner (Sum.inl world)).run).run log)
        (fun z => (simulateQ (fuseServing (noticingSplitTapeRecorder leftKeep rightKeep) inner
            (fun r => onCarrierTape (before r)) (onCarrierTape afterMap)) (next z.1.1.1)).run
            (accumulated * z.1.1.2, z.1.2, z.2) >>= cont)
        finalRight
        (fun z w hw => by
          rw [mem_support_bind_iff] at hw
          obtain ⟨r, hr, hw2⟩ := hw
          exact le_trans (fusedRightOf_prefix leftKeep rightKeep inner before afterMap _
            (accumulated * z.1.1.2, z.1.2, z.2) r hr).length_le (hgrow r w hw2))
        (fun _ => prFail_eq_zero _)
        (fun idx c hc v z => ih z.1.1.1 idx c hc v (accumulated * z.1.1.2) z.1.2 z.2.1
          z.2.2.1.1 z.2.2.1.2 z.2.2.2.1 z.2.2.2.2)
        index cell hle newValue cache leftTape rightTape leftRecord rightRecord
    · simp only [FusedTape.fuseServing_run_inr, bind_assoc, pure_bind]
      exact probEvent_length_setGe_cont leftKeep rightKeep
        (((inner (Sum.inr request)).run).run log)
        (fun z => (simulateQ (fuseServing (noticingSplitTapeRecorder leftKeep rightKeep) inner
            (fun r => onCarrierTape (before r)) (onCarrierTape afterMap)) (next z.1.1.1)).run
            (accumulated * z.1.1.2, z.1.2, onCarrierTape afterMap z.2) >>= cont)
        finalRight
        (fun z w hw => by
          rw [mem_support_bind_iff] at hw
          obtain ⟨r, hr, hw2⟩ := hw
          exact le_trans (fusedRightOf_prefix leftKeep rightKeep inner before afterMap _
            (accumulated * z.1.1.2, z.1.2, onCarrierTape afterMap z.2) r hr).length_le
            (hgrow r w hw2))
        (fun _ => prFail_eq_zero _)
        (fun idx c hc v z => ih z.1.1.1 idx c hc v (accumulated * z.1.1.2) z.1.2
          (afterMap z.2.1) z.2.2.1.1 z.2.2.1.2 z.2.2.2.1 z.2.2.2.2)
        index cell hle newValue (before request cache) leftTape rightTape leftRecord rightRecord

open scoped Classical in
/-- **Across all three stages.** -/
theorem probEvent_length_setGe_threeStage (leftKeep rightKeep : Bytes → σ → Prop)
    {β α γ δ : Type}
    (inner : β → QueryImpl (OracleWorld + Security.SigningSpec)
      (WriterT ω (StateT Security.SigningLog (OracleComp OracleWorld))))
    (before : Message → σ → σ) (afterMap : σ → σ)
    (first : OracleComp OracleWorld β)
    (phase : β → OracleComp (OracleWorld + Security.SigningSpec) α)
    (last : β → α → OracleComp OracleWorld γ)
    (value : β → α → ω → Security.SigningLog → γ → σ → δ)
    (index cell : Nat) (hle : index ≤ cell) (newValue : HashOutput) (cache : σ)
    (leftRecord rightRecord : Record) (leftTape rightTape : List HashOutput) :
    Pr{let w ← (threeStageTapeRun leftKeep rightKeep inner before afterMap first phase last value
          cache leftRecord rightRecord leftTape rightTape)}[
        rightRecord.length + index < w.2.2.2.length] =
      Pr{let w ← (threeStageTapeRun leftKeep rightKeep inner before afterMap first phase last value
          cache leftRecord rightRecord leftTape (rightTape.set cell newValue))}[
        rightRecord.length + index < w.2.2.2.length] := by
  classical
  rw [threeStageTapeRun, threeStageTapeRun]
  refine probEvent_length_setGe_cont leftKeep rightKeep first
    (fun keys => (simulateQ (fuseServing (noticingSplitTapeRecorder leftKeep rightKeep)
          (inner keys.1) (fun request => onCarrierTape (before request))
          (onCarrierTape afterMap)) (phase keys.1)).run (1, [], keys.2) >>= fun middle =>
        (simulateQ (noticingSplitTapeRecorder leftKeep rightKeep)
            (last keys.1 middle.1)).run middle.2.2.2 >>= fun final =>
          (pure (value keys.1 middle.1 middle.2.1 middle.2.2.1 final.1 final.2.1,
            forgetViewTape final.2) : ProbComp (δ × SplitPrefix.SplitState)))
    (fun w => w.2.2.2) ?_ ?_ ?_ index cell hle newValue cache leftTape rightTape leftRecord
      rightRecord
  · intro z w hw
    rw [mem_support_bind_iff] at hw
    obtain ⟨middle, hmiddle, hrest⟩ := hw
    rw [mem_support_bind_iff] at hrest
    obtain ⟨final, hfinal, hpure⟩ := hrest
    rw [support_pure, Set.mem_singleton_iff] at hpure
    rw [hpure]
    refine le_trans (fusedRightOf_prefix leftKeep rightKeep (inner z.1) before afterMap _
      (1, [], z.2) middle hmiddle).length_le ?_
    exact (noticingRightOf_prefix leftKeep rightKeep _ middle.2.2.2 final hfinal).length_le
  · intro z
    exact prFail_eq_zero _
  · intro idx c hc v z
    refine probEvent_length_setGe_fused leftKeep rightKeep (inner z.1) before afterMap
      (phase z.1)
      (fun middle => (simulateQ (noticingSplitTapeRecorder leftKeep rightKeep)
            (last z.1 middle.1)).run middle.2.2.2 >>= fun final =>
          (pure (value z.1 middle.1 middle.2.1 middle.2.2.1 final.1 final.2.1,
            forgetViewTape final.2)
            :
            ProbComp (δ × SplitPrefix.SplitState)))
      (fun w => w.2.2.2) ?_ ?_ ?_ idx c hc v 1 [] z.2.1 z.2.2.1.1 z.2.2.1.2 z.2.2.2.1
      z.2.2.2.2
    · intro y w hw
      rw [mem_support_bind_iff] at hw
      obtain ⟨final, hfinal, hpure⟩ := hw
      rw [support_pure, Set.mem_singleton_iff] at hpure
      rw [hpure]
      exact (noticingRightOf_prefix leftKeep rightKeep _ y.2.2.2 final hfinal).length_le
    · intro y
      exact prFail_eq_zero _
    · intro idx2 c2 hc2 v2 y
      refine probEvent_length_setGe_cont leftKeep rightKeep (last z.1 y.1)
        (fun final => (pure (value z.1 y.1 y.2.1 y.2.2.1 final.1 final.2.1,
          forgetViewTape final.2) : ProbComp (δ × SplitPrefix.SplitState)))
        (fun w => w.2.2.2) ?_ ?_ ?_ idx2 c2 hc2 v2 y.2.2.2.1 y.2.2.2.2.1.1 y.2.2.2.2.1.2
        y.2.2.2.2.2.1 y.2.2.2.2.2.2
      · intro t w hw
        rw [support_pure, Set.mem_singleton_iff] at hw
        rw [hw]
        exact le_rfl
      · intro t
        exact prFail_eq_zero _
      · intro idx3 c3 hc3 v3 t
        rfl

/-- **Suffix causality at the three-stage run, in the shape the charge asks for.** -/
theorem threeStageCausalGe (leftKeep rightKeep : Bytes → σ → Prop)
    {β α γ δ : Type}
    (inner : β → QueryImpl (OracleWorld + Security.SigningSpec)
      (WriterT ω (StateT Security.SigningLog (OracleComp OracleWorld))))
    (before : Message → σ → σ) (afterMap : σ → σ)
    (first : OracleComp OracleWorld β)
    (phase : β → OracleComp (OracleWorld + Security.SigningSpec) α)
    (last : β → α → OracleComp OracleWorld γ)
    (value : β → α → ω → Security.SigningLog → γ → σ → δ)
    (cache : σ) (index cell : Nat) (leftTape rightTape : List HashOutput)
    (newValue : HashOutput) (hle : index ≤ cell) :
    Pr{let w ← (threeStageTapeRun leftKeep rightKeep inner before afterMap first phase last value
          cache [] [] leftTape (rightTape.set cell newValue))}[index < w.2.2.2.length] =
      Pr{let w ← (threeStageTapeRun leftKeep rightKeep inner before afterMap first phase last value
          cache [] [] leftTape rightTape)}[index < w.2.2.2.length] := by
  have h := probEvent_length_setGe_threeStage leftKeep rightKeep inner before afterMap first phase
    last value index cell hle newValue cache [] [] leftTape rightTape
  simpa only [List.length_nil, Nat.zero_add] using h.symm

end SlhDsaSecurity.SuffixCausal
