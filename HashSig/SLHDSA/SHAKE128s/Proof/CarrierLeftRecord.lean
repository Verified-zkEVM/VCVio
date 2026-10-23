/-
Copyright (c) 2026 Tom Wambsgans. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Wambsgans
-/

module

public import HashSig.SLHDSA.SHAKE128s.Proof.CarrierRecordings
public import HashSig.SLHDSA.SHAKE128s.Proof.CarrierTail
public import HashSig.SLHDSA.SHAKE128s.Proof.RecordInvariant
public import HashSig.SLHDSA.SHAKE128s.Proof.CarrierServedLog

/-!
# What the disclosing recording holds

The signed-log hypothesis says every entry of the **disclosing** recording is in the signed log.
`CarrierRecordings` reads the target recording and not this one, so the disclosing one is read
here: an entry reaches it only by passing `CarriedWitness.disclosingKeep`, which is
`HandlerCarrier.FilesLeft` — *there is a request in flight and the input is that request's
message input.*

So every disclosing entry carries a **frame**, and its input is that frame's message input at
some randomiser. The file carries this further, at the carrier tail with no hypothesis: the
input is served by the carrier (`LeftServed`), and with the carrier-to-log invariants of
`CarrierServedLog` it is in the signed log (`servedLog_leftRecord_carrierTail`).

## How it is proved

As an invariant rather than a suffix. Nothing here needs the state an entry was filed at:
`FilesLeft` reads the framing alone, and the conclusion existentially quantifies the view, so
what survives a step survives the run. The brackets are free, since `BracketedRun.Bracket` fixes
the recordings outright. A predicate on one state that every step preserves composes by itself.
-/

@[expose] public section

open OracleComp OracleSpec

namespace SlhDsaSecurity.CarrierLeftRecord

variable {γ : Type}

open Security RecorderView HandlerCarrier CarriedWitness PhaseFusion RecordedQueries
open BracketedRun CarrierTail

variable (pk : PublicKey)

open scoped Classical in
/-- **A step appends at most its own query's entry to the disclosing recording**, and when it
does, the left test held at the state the notice had reached — which is `FilesLeft` at that
view. -/
theorem step_left_mem (rightKeep : Bytes → HandlerCarrier.State → Prop)
    (queried : OracleWorld.Domain) (state : CountedState)
    (step : OracleWorld.Range queried × CountedState)
    (hstep : step ∈ support
      (((CarrierFiles.countedCarrierRecorder pk rightKeep) queried).run state))
    (entry : Bytes × HashOutput) (hentry : entry ∈ step.2.2.1.1) :
    entry ∈ state.2.1.1 ∨
      (∃ view : HandlerCarrier.State, HandlerCarrier.FilesLeft pk view entry.1) ∧
        HandlerCarrier.Served step.2.1 entry.1 := by
  classical
  obtain ⟨inner, hinner, hvalue, hcarrier, hcarried⟩ :=
    CountedHandler.withCount_step _ queried state step hstep
  rw [hcarried] at hentry
  rcases queried with coin | input
  · rw [show inner.2.2 = (state.1, state.2.1).2 from
      congrArg Prod.snd (@recorderOf_step_inl HandlerCarrier.State (servingView pk)
        (disclosingKeep pk) rightKeep coin (state.1, state.2.1) inner
        (by rw [← @noticingRecorderOf_run_inl HandlerCarrier.State (servingView pk)]
            exact hinner))] at hentry
    exact Or.inl hentry
  · have hinr := hinner
    rw [@noticingRecorderOf_run_inr HandlerCarrier.State (servingView pk) (disclosingKeep pk)
      rightKeep input (state.1, state.2.1)] at hinr
    rw [@recorderOf_step_record HandlerCarrier.State (servingView pk) (disclosingKeep pk)
      rightKeep input _ inner hinr] at hentry
    rcases @appendedOf_left_mem HandlerCarrier.State (servingView pk) (disclosingKeep pk)
      rightKeep input _ inner.1 entry hentry with hprior | ⟨hself, -, hleft⟩
    · exact Or.inl hprior
    · have hinput : entry.1 = input := by rw [hself]
      have hnotice : HandlerCarrier.Served (servingNotice pk state.1 input) input := by
        obtain ⟨framed, hframing, randomizer, hin⟩ := hleft
        exact served_servingNotice_self pk state.1 input
          ⟨framed, by rw [← framing_servingNotice pk state.1 input]; exact hframing,
            randomizer, hin⟩
      refine Or.inr ⟨⟨servingNotice pk state.1 input, by rw [hinput]; exact hleft⟩, ?_⟩
      rw [hinput, hcarrier]
      rcases CarrierFiles.step_inr_cases pk rightKeep input (state.1, state.2.1) inner hinner with
        ⟨-, hstate⟩ | ⟨-, hstate⟩
      · rw [hstate]; exact hnotice
      · rw [hstate, HandlerCarrier.Served, HandlerCarrier.served_cacheAnswer]
        exact hnotice

/-! ## The served form

The entry's input is **served by the carrier**. The step that files it left also files it into
the served set (`CarriedWitness.served_servingNotice_self` is exactly that) and the served set
only grows afterwards, so the property survives. `step_left_mem` reports it alongside the frame,
the way `CarrierRecordings.step_right_mem` reports its entry's caching alongside its test. -/

/-- **Every disclosing entry is served by the carrier that holds it.** -/
def LeftServed (state : CountedState) : Prop :=
  ∀ entry ∈ state.2.1.1, HandlerCarrier.Served state.1 entry.1

theorem leftServed_start (cache : QueryCache HashSpec) :
    LeftServed (startAt cache, (([], []), 0)) := by
  intro entry hentry
  exact absurd hentry (by simp)

open scoped Classical in
theorem step_leftServed (rightKeep : Bytes → HandlerCarrier.State → Prop)
    (queried : OracleWorld.Domain) (state : CountedState)
    (step : OracleWorld.Range queried × CountedState)
    (hstep : step ∈ support
      (((CarrierFiles.countedCarrierRecorder pk rightKeep) queried).run state))
    (hinv : LeftServed state) : LeftServed step.2 := by
  classical
  intro entry hentry
  rcases step_left_mem pk rightKeep queried state step hstep entry hentry with
    hprior | ⟨-, hserved⟩
  · exact ((CarrierFiles.files_countedCarrierRecorder pk rightKeep).stepGrows queried state step
      hstep).2 entry.1 (hinv entry hprior)
  · exact hserved

theorem leftServed_startServingOn (request : Message) (state : CountedState)
    (hinv : LeftServed state) :
    LeftServed (ServedAgreement.startServingOn request state) := by
  rw [ServedAgreement.startServingOn]
  cases request.frame with
  | none => exact hinv
  | some framed => exact hinv

theorem leftServed_stopServingOn (state : CountedState) (hinv : LeftServed state) :
    LeftServed (ServedAgreement.stopServingOn state) := hinv

set_option maxHeartbeats 1000000 in
/-- **And every disclosing entry of the carrier tail is served by the carrier the tail ends
at.** Stated before the projection, because that carrier is what the containment reads. -/
theorem leftServed_carrierTail (rightKeep : Walk → Bytes → HandlerCarrier.State → Prop)
    (adversary : Adversary) (walk : Walk)
    (keys : (SecretKey × PublicKey) × CountedState)
    (hkeys : keys ∈ support ((simulateQ (handlerAt rightKeep walk)
      (Scheme.keygenInternal walk.1.1.1 walk.1.1.2.1 walk.1.1.2.2)).run
      (startAt walk.2, (([], []), 0))))
    (middle : Forgery × (Multiplicative Tally × SigningLog × CountedState))
    (hmiddle : middle ∈ support ((simulateQ (fuseServing (handlerAt rightKeep walk)
      (recordedAdversaryImpl + recordedSigningOracle (Scheme.sign keys.1.1))
      ServedAgreement.startServingOn ServedAgreement.stopServingOn)
      (adversary.main keys.1.2)).run (1, [], keys.2)))
    {γ : Type} (last : OracleComp OracleWorld γ) (final : γ × CountedState)
    (hfinal : final ∈ support ((simulateQ (handlerAt rightKeep walk) last).run middle.2.2.2)) :
    LeftServed final.2 := by
  have hfirst := RecordInvariant.run_invariant (Inv := LeftServed) _
    (fun queried state step hstep hinv =>
      step_leftServed (keyAt walk) (rightKeep walk) queried state step hstep hinv)
    _ (startAt walk.2, (([], []), 0)) keys hkeys (leftServed_start walk.2)
  have hsecond := RecordInvariant.phase_invariant (Inv := LeftServed) _
    (recordedAdversaryImpl + recordedSigningOracle (Scheme.sign keys.1.1))
    ServedAgreement.startServingOn ServedAgreement.stopServingOn
    (fun queried state step hstep hinv =>
      step_leftServed (keyAt walk) (rightKeep walk) queried state step hstep hinv)
    (fun request state hinv => leftServed_startServingOn request state hinv)
    (fun state hinv => leftServed_stopServingOn state hinv)
    _ 1 [] keys.2 middle hmiddle hfirst
  exact RecordInvariant.run_invariant (Inv := LeftServed) _
    (fun queried state step hstep hinv =>
      step_leftServed (keyAt walk) (rightKeep walk) queried state step hstep hinv)
    _ middle.2.2.2 final hfinal hsecond

/-! ## The disclosing recording is in the signed log

The served set contains every disclosing entry (`leftServed_carrierTail`), and
`CarrierServedLog` puts both of `ServedAgreement`'s invariants at the tail's final carrier. The
theorem below is the decomposition with the three facts about the walk: the key the run
generates, the good walk's separation, and the quiet start. -/

set_option maxHeartbeats 2000000 in
set_option linter.constructorNameAsVariable false in
/-- **Every disclosing entry of the carrier tail is in the signed log.** The served-agreement
hypothesis, with nothing assumed but a supported run and a good walk. -/
theorem servedLog_leftRecord_carrierTail
    (rightKeep : Walk → Bytes → HandlerCarrier.State → Prop)
    (adversary : Adversary) (walk : Walk)
    (hwalk : walk ∈ support WarmedGame.graphWalk)
    (hgood : ¬ HashSeparation.Possible
      (walk.1.1.2.2, walk.1.2 (.structural WalkDefects.topNode)))
    (result : ((Outcome × Multiset Bytes) × Nat) × SplitPrefix.SplitState)
    (hresult : result ∈ support (carrierTail rightKeep adversary walk)) (count : Nat) :
    ∀ entry ∈ result.2.2.1,
      ServedLog.servedLog (keyAt walk) ((result.1.1.1, count), result.2.1) entry.1 := by
  classical
  rw [carrierTail, mem_support_bind_iff] at hresult
  obtain ⟨keys, hkeys, hrest⟩ := hresult
  rw [mem_support_bind_iff] at hrest
  obtain ⟨middle, hmiddle, hrest⟩ := hrest
  rw [mem_support_bind_iff] at hrest
  obtain ⟨final, hlast, hpure⟩ := hrest
  rw [support_pure, Set.mem_singleton_iff] at hpure
  have hpk : keys.1.1.publicKey = keyAt walk :=
    CarrierRecord.keys_publicKey rightKeep walk hwalk keys hkeys
  have hpublic : ¬ HashSeparation.Possible
      (keys.1.1.publicKey.seed, keys.1.1.publicKey.root) := by
    rw [hpk]
    exact AnswerSide.not_possible_generatedKey hwalk hgood
  have hquiet : CarrierCap.Quiet keys.2.1 :=
    CarrierCap.quiet_run rightKeep walk _ (startAt walk.2, (([], []), 0)) keys hkeys
      (CarrierCap.quiet_startAt walk.2)
  have hclearMiddle : middle.2.2.2.1.framing = none :=
    CarrierClearFraming.clear_phase rightKeep walk keys.1.1 _ 1 [] keys.2 middle hmiddle hquiet.1
  have hlogged : ServedAgreement.CarrierLogged keys.1.1 ∅ middle.2.2.1 final.2.1 :=
    CarrierServedLog.carrierLogged_run keys.1.1 ∅ middle.2.2.1 rightKeep walk _
      middle.2.2.2 final hlast hclearMiddle
      (CarrierServedLog.carrierLogged_phase rightKeep walk keys.1.1 hpk hpublic _ 1 keys.2
        hquiet.1 hquiet.2 middle hmiddle)
  have hfiled : ServedAgreement.LogFiled keys.1.1 middle.2.2.1 final.2.1 :=
    CarrierServedLog.logFiled_run keys.1.1 middle.2.2.1 rightKeep walk _ middle.2.2.2 final
      hlast hclearMiddle
      (CarrierServedLog.logFiled_phase rightKeep walk keys.1.1 hpk _ 1 keys.2 middle hmiddle)
  intro entry hentry
  rw [hpure] at hentry ⊢
  exact CarrierServedLog.carrierBelowLog_of_invariants keys.1.1 (keyAt walk) hpk
    middle.2.2.1 final.2.1 hfiled hlogged _ rfl (fun _ _ hvalue => hvalue) entry.1
    (leftServed_carrierTail rightKeep adversary walk keys hkeys middle hmiddle _ final hlast
      entry hentry)

end SlhDsaSecurity.CarrierLeftRecord
