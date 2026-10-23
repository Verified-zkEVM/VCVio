/-
Copyright (c) 2026 Tom Wambsgans. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Wambsgans
-/

module

public import HashSig.SLHDSA.SHAKE128s.Proof.CarrierTailRecordings
public import HashSig.SLHDSA.SHAKE128s.Proof.RecordInvariant

/-!
# No request in flight, stage by stage

The views the carrier recorder is run at must have no request in flight. `Clear` is that
invariant on a counted state. It holds at the tail's start, is kept by every handler step and by
a whole run under the handler, and is restored by the closing bracket, so the adversary's phase
is entered clear and left clear. `clear_stages` collects the three stages of the tail.

One region does not have it, by construction: a signing sub-run. The opening bracket's whole job
is to raise the framing, so the views inside a sub-run carry the request the sub-run is serving.
The statements here never read that region.
-/

@[expose] public section

open OracleComp OracleSpec

namespace SlhDsaSecurity.CarrierClearFraming

variable {α : Type}

open Security BracketedRun CarrierFiles CarrierTail PhaseFusion RecordInvariant RecordedQueries

variable (rightKeep : Walk → Bytes → HandlerCarrier.State → Prop)

/-- The invariant: nothing in flight at the carrier a counted state carries. -/
def Clear (state : CountedState) : Prop := state.1.framing = none

/-- **The tail starts with nothing in flight.** -/
theorem clear_startAt (cache : QueryCache HashSpec) :
    Clear (startAt cache, (([], []), 0)) := rfl

/-- **A handler step leaves the framing where it found it**, so it keeps the invariant. -/
theorem clear_step (walk : Walk) (queried : OracleWorld.Domain) (state : CountedState)
    (step : OracleWorld.Range queried × CountedState)
    (hstep : step ∈ support (((handlerAt rightKeep walk) queried).run state))
    (hclear : Clear state) : Clear step.2 := by
  rw [Clear, (files_countedCarrierRecorder (keyAt walk) (rightKeep walk)).stepFraming
    queried state step hstep]
  exact hclear

/-- **And so does a whole run under the handler**: key generation's and the verifier's. -/
theorem clear_run (walk : Walk) {α : Type} (computation : OracleComp OracleWorld α)
    (state : CountedState) (result : α × CountedState)
    (hresult : result ∈ support ((simulateQ (handlerAt rightKeep walk) computation).run state))
    (hclear : Clear state) : Clear result.2 :=
  run_invariant (Inv := Clear) (handlerAt rightKeep walk)
    (fun queried state step hstep hinv => clear_step rightKeep walk queried state step hstep hinv)
    computation state result hresult hclear

/-- **The closing bracket restores it**, whatever it is handed: `stopServingOn` writes `none`. -/
theorem clear_stopServingOn (state : CountedState) :
    Clear (ServedAgreement.stopServingOn state) := rfl

/-- **The adversary's phase is left with nothing in flight.** Its own steps keep the invariant and
its signing calls restore it, so the sub-runs inside — where it genuinely fails — are not a case
to be handled but a region the statement never reads. -/
theorem clear_phase (walk : Walk) (sk : SecretKey) {α : Type}
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (accumulated : Multiplicative Tally) (log : SigningLog) (carrier : CountedState)
    (result : α × (Multiplicative Tally × SigningLog × CountedState))
    (hresult : result ∈ support ((simulateQ (fuseServing (handlerAt rightKeep walk)
      (recordedAdversaryImpl + recordedSigningOracle (Scheme.sign sk))
      ServedAgreement.startServingOn ServedAgreement.stopServingOn) computation).run
        (accumulated, log, carrier)))
    (hclear : Clear carrier) : Clear result.2.2.2 :=
  phase_invariant_of_after (Inv := Clear) (handlerAt rightKeep walk) _
    ServedAgreement.startServingOn ServedAgreement.stopServingOn
    (fun queried state step hstep hinv => clear_step rightKeep walk queried state step hstep hinv)
    clear_stopServingOn computation accumulated log carrier result hresult hclear

/-! ## The three stages of the tail

Stated at the tail's own decomposition, so that a consumer reading one stage's `reaches` gets it
without unfolding anything. -/

/-- **Every stage of the carrier tail is entered with nothing in flight**, and the tail is left
that way. -/
theorem clear_stages (adversary : Adversary) (walk : Walk)
    (keys : (SecretKey × PublicKey) × CountedState)
    (hkeys : keys ∈ support ((simulateQ (handlerAt rightKeep walk)
      (Scheme.keygenInternal walk.1.1.1 walk.1.1.2.1 walk.1.1.2.2)).run
        (startAt walk.2, (([], []), 0))))
    (middle : Forgery × (Multiplicative Tally × SigningLog × CountedState))
    (hmiddle : middle ∈ support ((simulateQ (fuseServing (handlerAt rightKeep walk)
      (recordedAdversaryImpl + recordedSigningOracle (Scheme.sign keys.1.1))
      ServedAgreement.startServingOn ServedAgreement.stopServingOn)
        (adversary.main keys.1.2)).run (1, [], keys.2)))
    (final : (Bool × Tally) × CountedState)
    (hfinal : final ∈ support ((simulateQ (handlerAt rightKeep walk)
      (countRecorded verifierCost
        (Scheme.verify keys.1.2 middle.1.message middle.1.signature))).run middle.2.2.2)) :
    Clear (startAt walk.2, (([], []), 0)) ∧ Clear keys.2 ∧ Clear middle.2.2.2 ∧
      Clear final.2 := by
  have hkey := clear_run rightKeep walk _ _ keys hkeys (clear_startAt walk.2)
  have hphase := clear_phase rightKeep walk keys.1.1 _ _ _ keys.2 middle hmiddle hkey
  exact ⟨clear_startAt walk.2, hkey, hphase,
    clear_run rightKeep walk _ _ final hfinal hphase⟩

end SlhDsaSecurity.CarrierClearFraming
