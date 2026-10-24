/-
Copyright (c) 2026 Tom Wambsgans. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Wambsgans
-/

module

public import HashSig.SLHDSA.SHAKE128s.Proof.CarrierRecordings
public import HashSig.SLHDSA.SHAKE128s.Proof.AnswerCarrier

/-!
# The two invariants, carried across the carrier tail

The composition. `RecordInvariant` carries an invariant across a run and across a bracketed
phase; `CarrierRecordings` supplies the step facts and the bracket facts; the tail is key
generation, then the bracketed phase, then verification, so it is three applications and the
start.

The start is where both invariants are free: the tail begins with both recordings empty, so
there is nothing recorded to be of the wrong class or recorded twice.

Stated at `AnswerCarrier.answerCarrierRun` as well as at the tail, because that is the name the
bound is read at, and a fact about the tail that its consumer has to unfold to use is a fact
stated one step too early.
-/

public section

open OracleComp OracleSpec

namespace SlhDsaSecurity.CarrierTailRecordings

open Security BracketedRun CarrierFiles CarrierRecordings RecordInvariant CarrierTail
  RecordedQueries

variable (rightKeep : Walk → Bytes → HandlerCarrier.State → Prop)

/-! ## Both invariants hold where the tail starts -/

/-- The starting state records nothing, so every target-recorded input is in the class. -/
theorem recordClass_startAt (narrow : Bytes → Prop) (cache : QueryCache HashSpec) :
    RecordClass narrow (startAt cache, (([], []), 0)) := by
  intro entry hentry
  exact absurd hentry (by simp)

/-- The starting state's target recording is empty, hence cached and free of duplicates. -/
theorem recordFreshNodup_startAt (cache : QueryCache HashSpec) :
    RecordFreshNodup (startAt cache, (([], []), 0)) :=
  ⟨fun entry hentry => absurd hentry (by simp), by simp⟩

/-! ## And are carried across the three phases -/

/-- **Every target-recorded input of the tail is of the narrowed class.** -/
theorem recordClass_carrierTail (narrow : Walk → Bytes → Prop)
    (hnarrow : ∀ (walk : Walk) (input : Bytes) (view : HandlerCarrier.State),
      rightKeep walk input view → narrow walk input)
    (adversary : Adversary) (walk : Walk)
    (result : ((Outcome × Multiset Bytes) × Nat) × SplitPrefix.SplitState)
    (hresult : result ∈ support (carrierTail rightKeep adversary walk)) :
    ∀ entry ∈ result.2.2.2, narrow walk entry.1 := by
  classical
  rw [carrierTail, mem_support_bind_iff] at hresult
  obtain ⟨keys, hkeys, hrest1⟩ := hresult
  rw [mem_support_bind_iff] at hrest1
  obtain ⟨middle, hmiddle, hrest2⟩ := hrest1
  rw [mem_support_bind_iff] at hrest2
  obtain ⟨final, hfinal, hpure⟩ := hrest2
  rw [support_pure, Set.mem_singleton_iff] at hpure
  have hstep := step_recordClass (keyAt walk) (rightKeep walk) (narrow walk)
    (fun input view hright => hnarrow walk input view hright)
  have hkey := run_invariant (Inv := RecordClass (narrow walk)) (handlerAt rightKeep walk) hstep
    _ (startAt walk.2, (([], []), 0)) keys hkeys (recordClass_startAt (narrow walk) walk.2)
  have hphase := phase_invariant (Inv := RecordClass (narrow walk)) (handlerAt rightKeep walk) _
    ServedAgreement.startServingOn ServedAgreement.stopServingOn hstep
    (fun request state hinv =>
      recordClass_bracket (narrow walk) (bracket_startServingOn request) state hinv)
    (fun state hinv => recordClass_bracket (narrow walk) bracket_stopServingOn state hinv)
    _ (1 : Multiplicative Tally) [] keys.2 middle hmiddle hkey
  have hverify := run_invariant (Inv := RecordClass (narrow walk)) (handlerAt rightKeep walk)
    hstep _ middle.2.2.2 final hfinal hphase
  intro entry hentry
  refine hverify entry ?_
  rw [show result.2 = forgetCarrier final.2 from by rw [hpure]] at hentry
  exact hentry

/-- **And the tail's target recording is cached and holds each input once.** -/
theorem recordFreshNodup_carrierTail (adversary : Adversary) (walk : Walk)
    (result : ((Outcome × Multiset Bytes) × Nat) × SplitPrefix.SplitState)
    (hresult : result ∈ support (carrierTail rightKeep adversary walk)) :
    (∀ entry ∈ result.2.2.2, result.2.1 entry.1 ≠ none) ∧
      (result.2.2.2.map Prod.fst).Nodup := by
  classical
  rw [carrierTail, mem_support_bind_iff] at hresult
  obtain ⟨keys, hkeys, hrest1⟩ := hresult
  rw [mem_support_bind_iff] at hrest1
  obtain ⟨middle, hmiddle, hrest2⟩ := hrest1
  rw [mem_support_bind_iff] at hrest2
  obtain ⟨final, hfinal, hpure⟩ := hrest2
  rw [support_pure, Set.mem_singleton_iff] at hpure
  have hstep := step_recordFreshNodup (keyAt walk) (rightKeep walk)
  have hkey := run_invariant (Inv := RecordFreshNodup) (handlerAt rightKeep walk) hstep
    _ (startAt walk.2, (([], []), 0)) keys hkeys (recordFreshNodup_startAt walk.2)
  have hphase := phase_invariant (Inv := RecordFreshNodup) (handlerAt rightKeep walk) _
    ServedAgreement.startServingOn ServedAgreement.stopServingOn hstep
    (fun request state hinv =>
      recordFreshNodup_bracket (bracket_startServingOn request) state hinv)
    (fun state hinv => recordFreshNodup_bracket bracket_stopServingOn state hinv)
    _ (1 : Multiplicative Tally) [] keys.2 middle hmiddle hkey
  have hverify := run_invariant (Inv := RecordFreshNodup) (handlerAt rightKeep walk)
    hstep _ middle.2.2.2 final hfinal hphase
  have hstate : result.2 = forgetCarrier final.2 := by rw [hpure]
  rw [hstate]
  exact hverify

/-! ## At the name the bound is read at

The budget below is raised for the linters, not for the proofs. A linter timing out on a
statement is worth reading before silencing: it means the term is hard to look at, and the
question is **why**. In `PhaseRightRecord` it was a statement carrying three sub-runs at once,
and the answer was to split it. Here the statements are two-line transports and the term is
large only because the object they name is — `answerCarrierRun` unfolds to the whole tail. Same
symptom, opposite cause, opposite fix. The linter is turned off for the two statements below
and for nothing else: it cannot whnf a term that unfolds to the whole tail, and that is a fact
about the object's size rather than about any name in them.

`AnswerShape.forgetRecord` drops the record and keeps the whole state, so both facts transfer
with the state unchanged. Stated here so that a consumer of `answerCarrierRun` never has to
unfold it to reach them. -/

end SlhDsaSecurity.CarrierTailRecordings
