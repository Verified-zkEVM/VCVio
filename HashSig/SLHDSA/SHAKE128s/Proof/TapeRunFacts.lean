/-
Copyright (c) 2026 Tom Wambsgans. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Wambsgans
-/

module

public import HashSig.SLHDSA.SHAKE128s.Proof.SignedWatch

/-!
# What a tape run keeps, files and reaches

Three facts about the tape recorder with both blocks fixed, each the tape twin of a fact the
handler-level recorders already have:

* the cache only grows (`run_cache_persists`);
* every entry a run appends to the target recording was uncached when the run began, is cached
  at its end with the answer recorded, and passed the target test at a carrier the run reached —
  a carrier that still satisfies whatever the start did, for any property the notice and the
  installation keep (`run_right_suffix`);
* a supported result of the three-stage tape run, at blocks of any lengths, is a supported result
  of the handler run it factorises (`mem_support_threeStageHandlerRun_of_tape`) — so every fact
  proved about the handler's final results holds of the tape run's too.
-/

@[expose] public section

open OracleComp OracleSpec ENNReal

set_option backward.isDefEq.respectTransparency false

namespace SlhDsaSecurity.TapeRunFacts

open DigestTape TapeFactor NoticingTape RecorderView PhaseFusion FusedTape SignedWatch

variable {σ : Type} [CacheView σ]

/-- **The cache only grows, along a run.** -/
theorem run_cache_persists (leftKeep rightKeep : Bytes → σ → Prop) {α : Type}
    (computation : OracleComp OracleWorld α) (state : SplitTapeState σ)
    (result : α × SplitTapeState σ)
    (hresult : result ∈ support ((simulateQ (noticingSplitTapeRecorder leftKeep rightKeep)
      computation).run state))
    (input : Bytes) (answer : HashOutput)
    (hcached : CacheView.cacheOf state.1 input = some answer) :
    CacheView.cacheOf result.2.1 input = some answer := by
  induction computation using OracleComp.inductionOn generalizing state with
  | pure value =>
    rw [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hresult
    rw [hresult]
    exact hcached
  | query_bind queried next ih =>
    rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at hresult
    obtain ⟨step, hstep, hrest⟩ := hresult
    refine ih step.1 step.2 hrest ?_
    rcases queried with coin | queriedInput
    · rw [tapeStep_inl leftKeep rightKeep coin state step hstep]
      exact hcached
    · exact tapeStep_cache_persists leftKeep rightKeep queriedInput input answer state hcached
        step hstep

/-- A carrier property that the notice and the installation both keep. -/
def Kept (keepsProperty : σ → Prop) : Prop :=
  (∀ (carrier : σ) (input : Bytes), keepsProperty carrier →
      keepsProperty (CacheView.onQuery carrier input)) ∧
    ∀ (carrier : σ) (input : Bytes) (answer : HashOutput), keepsProperty carrier →
      keepsProperty (CacheView.update carrier input answer)

/-- **One step keeps such a property.** -/
theorem step_kept (leftKeep rightKeep : Bytes → σ → Prop) (property : σ → Prop)
    (hkept : Kept property) (queried : OracleWorld.Domain) (state : SplitTapeState σ)
    (hstate : property state.1)
    (step : OracleWorld.Range queried × SplitTapeState σ)
    (hstep : step ∈ support (((noticingSplitTapeRecorder leftKeep rightKeep) queried).run
      state)) :
    property step.2.1 := by
  rcases queried with coin | input
  · rw [tapeStep_inl leftKeep rightKeep coin state step hstep]
    exact hstate
  · have hnoticed := hkept.1 state.1 input hstate
    rcases tapeStep_inr_cases leftKeep rightKeep input state step hstep with
      ⟨-, hst⟩ | ⟨-, -, hst⟩ | ⟨-, -, -, hst⟩ | ⟨-, -, -, hst⟩ <;> rw [hst]
    · exact hnoticed
    all_goals exact hkept.2 _ _ _ hnoticed

/-- **What a run appends to the target recording**, entry by entry. -/
theorem run_right_suffix (leftKeep rightKeep : Bytes → σ → Prop) (property : σ → Prop)
    (hkept : Kept property) {α : Type}
    (computation : OracleComp OracleWorld α) (state : SplitTapeState σ)
    (hstate : property state.1)
    (result : α × SplitTapeState σ)
    (hresult : result ∈ support ((simulateQ (noticingSplitTapeRecorder leftKeep rightKeep)
      computation).run state)) :
    ∃ suffix : Record, result.2.2.2.2 = state.2.2.2 ++ suffix ∧
      ∀ entry ∈ suffix, CacheView.cacheOf state.1 entry.1 = none ∧
        CacheView.cacheOf result.2.1 entry.1 = some entry.2 ∧
        ∃ mid : σ, property mid ∧ CacheView.cacheOf mid entry.1 = none ∧
          ¬ leftKeep entry.1 mid ∧ rightKeep entry.1 mid := by
  induction computation using OracleComp.inductionOn generalizing state with
  | pure value =>
    rw [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hresult
    exact ⟨[], by rw [hresult, List.append_nil], fun entry hentry => absurd hentry (by simp)⟩
  | query_bind queried next ih =>
    rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at hresult
    obtain ⟨step, hstep, hrest⟩ := hresult
    obtain ⟨suffix, hsuffix, hentries⟩ := ih step.1 step.2
      (step_kept leftKeep rightKeep property hkept queried state hstate step hstep) hrest
    -- what the first step appended, if anything
    have hfirst : ∃ head : Record, step.2.2.2.2 = state.2.2.2 ++ head ∧
        ∀ entry ∈ head, CacheView.cacheOf state.1 entry.1 = none ∧
          CacheView.cacheOf step.2.1 entry.1 = some entry.2 ∧
          ∃ mid : σ, property mid ∧ CacheView.cacheOf mid entry.1 = none ∧
            ¬ leftKeep entry.1 mid ∧ rightKeep entry.1 mid := by
      rcases queried with coin | input
      · rw [tapeStep_inl leftKeep rightKeep coin state step hstep]
        exact ⟨[], by rw [List.append_nil], fun entry hentry => absurd hentry (by simp)⟩
      · have hnoticedCache : CacheView.cacheOf (CacheView.onQuery state.1 input) =
            CacheView.cacheOf state.1 := CacheView.cache_onQuery state.1 input
        rcases tapeStep_inr_cases leftKeep rightKeep input state step hstep with
          ⟨-, hst⟩ | ⟨-, -, hst⟩ | ⟨hfresh, hnotLeft, hright, hst⟩ | ⟨-, -, -, hst⟩
        · exact ⟨[], by rw [hst, List.append_nil], fun entry hentry => absurd hentry (by simp)⟩
        · exact ⟨[], by rw [hst, List.append_nil], fun entry hentry => absurd hentry (by simp)⟩
        · refine ⟨[(input, step.1)], by rw [hst], fun entry hentry => ?_⟩
          rw [List.mem_singleton] at hentry
          subst hentry
          refine ⟨by rw [← hnoticedCache]; exact hfresh, ?_,
            CacheView.onQuery state.1 input, hkept.1 _ _ hstate, hfresh, hnotLeft, hright⟩
          rw [hst]
          simp [CacheView.cache_update]
        · exact ⟨[], by rw [hst, List.append_nil], fun entry hentry => absurd hentry (by simp)⟩
    obtain ⟨head, hhead, hheadEntries⟩ := hfirst
    refine ⟨head ++ suffix, by rw [hsuffix, hhead, List.append_assoc], fun entry hentry => ?_⟩
    rcases List.mem_append.mp hentry with hin | hin
    · obtain ⟨hfresh, hcachedStep, hmid⟩ := hheadEntries entry hin
      exact ⟨hfresh, run_cache_persists leftKeep rightKeep _ step.2 result hrest entry.1
        entry.2 hcachedStep, hmid⟩
    · obtain ⟨hfreshStep, hcachedEnd, hmid⟩ := hentries entry hin
      refine ⟨?_, hcachedEnd, hmid⟩
      cases hstart : CacheView.cacheOf state.1 entry.1 with
      | none => rfl
      | some value =>
        have hpersist : CacheView.cacheOf step.2.1 entry.1 = some value := by
          rcases queried with coin | input
          · rw [tapeStep_inl leftKeep rightKeep coin state step hstep]
            exact hstart
          · exact tapeStep_cache_persists leftKeep rightKeep input entry.1 value state hstart
              step hstep
        rw [hfreshStep] at hpersist
        exact absurd hpersist (by simp)

/-! ## The tape run's results are the handler run's -/

/-- **Every list of the right length is a possible block.** -/
theorem mem_support_padding_of_length (tape : List HashOutput) :
    tape ∈ support (padding tape.length) := by
  induction tape with
  | nil => simp [padding]
  | cons head rest ih =>
    rw [List.length_cons, padding, mem_support_bind_iff]
    refine ⟨head, mem_support_uniformSample (α := HashOutput), ?_⟩
    rw [mem_support_bind_iff]
    exact ⟨rest, ih, by simp⟩

variable {ω : Type} [Monoid ω]

/-- **A supported result of the three-stage tape run is a supported result of the handler run**,
whatever the lengths of the two blocks. -/
theorem mem_support_threeStageHandlerRun_of_tape (leftKeep rightKeep : Bytes → σ → Prop)
    {β α γ δ : Type}
    (inner : β → QueryImpl (OracleWorld + Security.SigningSpec)
      (WriterT ω (StateT Security.SigningLog (OracleComp OracleWorld))))
    (before : Message → σ → σ) (afterMap : σ → σ)
    (first : OracleComp OracleWorld β)
    (phase : β → OracleComp (OracleWorld + Security.SigningSpec) α)
    (last : β → α → OracleComp OracleWorld γ)
    (value : β → α → ω → Security.SigningLog → γ → σ → δ)
    (cache : σ) (leftRecord rightRecord : Record) (leftTape rightTape : List HashOutput)
    (w : δ × SplitPrefix.SplitState)
    (hw : w ∈ support (threeStageTapeRun leftKeep rightKeep inner before afterMap first phase
      last value cache leftRecord rightRecord leftTape rightTape)) :
    w ∈ support (threeStageHandlerRun leftKeep rightKeep inner before afterMap first phase last
      value cache leftRecord rightRecord) := by
  have hlaw := evalDist_threeStageHandlerRun_eq leftKeep rightKeep inner before afterMap first
    phase last value cache leftRecord rightRecord leftTape.length rightTape.length
  rw [Averaging.support_eq_of_evalDistEq hlaw, support_map]
  refine ⟨((leftTape, rightTape), w), ?_, rfl⟩
  rw [NoticingTape.blockRunOf, mem_support_bind_iff]
  refine ⟨leftTape, mem_support_padding_of_length leftTape, ?_⟩
  rw [mem_support_bind_iff]
  refine ⟨rightTape, mem_support_padding_of_length rightTape, ?_⟩
  rw [support_map]
  exact ⟨w, hw, rfl⟩

end SlhDsaSecurity.TapeRunFacts
