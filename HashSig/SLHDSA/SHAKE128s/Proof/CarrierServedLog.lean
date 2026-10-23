/-
Copyright (c) 2026 Tom Wambsgans. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Wambsgans
-/

module

public import HashSig.SLHDSA.SHAKE128s.Proof.CarrierCap
public import HashSig.SLHDSA.SHAKE128s.Proof.CarrierClearFraming
public import HashSig.SLHDSA.SHAKE128s.Proof.CarrierCover

/-!
# From the carrier's served set to the log, before the projection

`ServedBridge.CarrierBelowLog` says every `HandlerCarrier.Served` input is a `ServedLog.servedLog`
input. It has to be established **before** `BracketedRun.forgetCarrier`, which drops the carrier
the tail ends at, so it is not a fact about a supported result of `CarrierTail.carrierTail`.

`ServedAgreement.carrierLogged_run_with` is the engine and is general in the start state: it
asks for nothing in flight and `CarrierLogged` there. This file supplies the two ends of the
tail.

**At the front**, `carrierLogged_of_served_zero` needs only an **empty served set**, which
`CarrierCap.quiet_run` delivers across key generation.

**At the back**, the verifier's stage runs after the phase, when the served set is no longer
empty. It files nothing, because `CarrierClearFraming` enters it with nothing in flight and
`HandlerCarrier.FilesLeft` cannot match a clear frame, so the served set comes out of it
**unchanged**, whatever it was: `served_run_of_clear`, `CarrierCap.quiet_run`'s argument with the
served set a parameter instead of zero.

Both are the same observation: *filing needs a frame in flight, and both of the tail's
unbracketed stages have none.*
-/

@[expose] public section

open OracleComp OracleSpec

namespace SlhDsaSecurity.CarrierServedLog

variable {α : Type}

open Security BracketedRun CarrierFiles CarrierTail PhaseFusion RecordInvariant
open RecordedQueries RecorderView CarriedWitness HandlerCarrier

/-- **A carrier that has served nothing is logged, vacuously.** What the argument uses is the
empty served set, not an empty cache. -/
theorem carrierLogged_of_served_zero (sk : SecretKey) (warm : QueryCache HashSpec)
    (log : SigningLog) (carrier : HandlerCarrier.State) (hserved : carrier.served = 0) :
    ServedAgreement.CarrierLogged sk warm log carrier := by
  intro _ _ _ input hservedAt
  rw [HandlerCarrier.Served, hserved] at hservedAt
  exact absurd hservedAt (by simp)

/-- The invariant the verifier's stage keeps: nothing in flight, and the served set it was
entered with. -/
def ClearWith (served : Multiset Bytes) (carrier : HandlerCarrier.State) : Prop :=
  carrier.framing = none ∧ carrier.served = served

theorem clearWith_cacheAnswer (served : Multiset Bytes) (carrier : HandlerCarrier.State)
    (input : Bytes) (answer : HashOutput) (hinv : ClearWith served carrier) :
    ClearWith served (HandlerCarrier.cacheAnswer carrier input answer) :=
  ⟨by rw [HandlerCarrier.framing_cacheAnswer]; exact hinv.1,
    by rw [HandlerCarrier.served_cacheAnswer]; exact hinv.2⟩

/-- **A run under the tail's handler with nothing in flight serves nothing new.**
`CarrierCap.quiet_run` with the served set a parameter instead of zero: the filing clause is
refuted by the clear frame either way, and only the `Quiet` version needed it to be zero. -/
theorem clearWith_run (rightKeep : Walk → Bytes → HandlerCarrier.State → Prop) (walk : Walk)
    (served : Multiset Bytes) {α : Type} (computation : OracleComp OracleWorld α)
    (state : CountedState) (result : α × CountedState)
    (hresult : result ∈ support
      ((simulateQ (handlerAt rightKeep walk) computation).run state))
    (hinv : ClearWith served state.1) : ClearWith served result.2.1 :=
  (files_countedCarrierRecorder (keyAt walk) (rightKeep walk)).invariant (ClearWith served)
    (clearWith_cacheAnswer served)
    (fun carrier input hcarrier hfiles =>
      absurd hfiles (HandlerCarrier.not_filesLeft_of_clear (keyAt walk) carrier hcarrier.1 input))
    computation state result hresult hinv

/-- **So the verifier's stage leaves the served set where the phase left it.** -/
theorem served_run_of_clear (rightKeep : Walk → Bytes → HandlerCarrier.State → Prop)
    (walk : Walk) {α : Type} (computation : OracleComp OracleWorld α)
    (state : CountedState) (result : α × CountedState)
    (hresult : result ∈ support ((simulateQ (handlerAt rightKeep walk) computation).run state))
    (hclear : state.1.framing = none) : result.2.1.served = state.1.served :=
  (clearWith_run rightKeep walk state.1.served computation state result hresult
    ⟨hclear, rfl⟩).2

/-! ## The middle stage, applied

The hypotheses `ServedAgreement.carrierLogged_run_with` asks for are about the **signer**, and
are read at `warm := fun _ => none`: nothing is stripped, so the pin of `signerPins_sign` holds at
every cache and the table is empty. `ServedAgreement.servingPhaseWith impl signer` is
`fuseServing impl (recordedAdversaryImpl + recordedSigningOracle signer) startServingOn
stopServingOn`, which is the carrier tail's middle stage on the nose. -/

/-- **The middle stage leaves the carrier logged.** -/
theorem carrierLogged_phase (rightKeep : Walk → Bytes → HandlerCarrier.State → Prop)
    (walk : Walk) (sk : SecretKey) (hpk : sk.publicKey = keyAt walk)
    (hpublic : ¬ HashSeparation.Possible (sk.publicKey.seed, sk.publicKey.root))
    {α : Type} (phase : OracleComp (OracleWorld + SigningSpec) α)
    (accumulated : Multiplicative Tally) (state : CountedState)
    (hclear : state.1.framing = none) (hserved : state.1.served = 0)
    (z : α × (Multiplicative Tally × SigningLog × CountedState))
    (hz : z ∈ support ((simulateQ (ServedAgreement.servingPhaseWith (handlerAt rightKeep walk)
      (Scheme.sign sk)) phase).run (accumulated, [], state))) :
    ServedAgreement.CarrierLogged sk ∅ z.2.2.1 z.2.2.2.1 :=
  ServedAgreement.carrierLogged_run_with (keyAt walk) (handlerAt rightKeep walk)
    (files_countedCarrierRecorder (keyAt walk) (rightKeep walk)) (Scheme.sign sk) sk hpk
    (ServedAgreement.signerShape_sign sk) ∅
    (ServedAgreement.signerPins_sign sk hpublic) phase (accumulated, [], state) hclear
    (carrierLogged_of_served_zero sk ∅ [] state.1 hserved) z hz

/-! ## And it survives the verifier's stage

`CarrierLogged` reads two things of the carrier: the caches that extend it, and what it has
served. The verifier's stage only grows the first and, entered with nothing in flight, leaves
the second alone. -/

/-- **A stage under the tail's handler only grows the cache.** -/
theorem cache_persists_run (rightKeep : Walk → Bytes → HandlerCarrier.State → Prop)
    (walk : Walk) {α : Type} (computation : OracleComp OracleWorld α)
    (state : CountedState) (result : α × CountedState)
    (hresult : result ∈ support ((simulateQ (handlerAt rightKeep walk) computation).run state))
    (input : Bytes) (value : HashOutput) (hentry : state.1.cache input = some value) :
    result.2.1.cache input = some value := by
  let : RecorderView.CacheView HandlerCarrier.State := servingView (keyAt walk)
  exact NoticingCover.cache_value_persists (disclosingKeep (keyAt walk)) (rightKeep walk)
    computation (CarrierCover.dropCount state) (result.1, CarrierCover.dropCount result.2)
    (CarrierCover.mem_support_dropCount_run (keyAt walk) (rightKeep walk) computation state
      result hresult) input value hentry

/-- **So a logged carrier stays logged across it.** -/
theorem carrierLogged_run (sk : SecretKey) (warm : QueryCache HashSpec) (log : SigningLog)
    (rightKeep : Walk → Bytes → HandlerCarrier.State → Prop) (walk : Walk)
    {α : Type} (computation : OracleComp OracleWorld α)
    (state : CountedState) (result : α × CountedState)
    (hresult : result ∈ support ((simulateQ (handlerAt rightKeep walk) computation).run state))
    (hclear : state.1.framing = none)
    (hlogged : ServedAgreement.CarrierLogged sk warm log state.1) :
    ServedAgreement.CarrierLogged sk warm log result.2.1 := by
  intro later hlater hwarm input hserved
  refine hlogged later
    (fun probe value hvalue => hlater probe value
      (cache_persists_run rightKeep walk computation state result hresult probe value hvalue))
    hwarm input ?_
  rw [HandlerCarrier.Served,
    served_run_of_clear rightKeep walk computation state result hresult hclear] at hserved
  exact hserved

/-- **A stage with nothing in flight grows the carrier and nothing more.** -/
theorem grows_run_of_clear (rightKeep : Walk → Bytes → HandlerCarrier.State → Prop)
    (walk : Walk) {α : Type} (computation : OracleComp OracleWorld α)
    (state : CountedState) (result : α × CountedState)
    (hresult : result ∈ support ((simulateQ (handlerAt rightKeep walk) computation).run state))
    (hclear : state.1.framing = none) : HandlerCarrier.Grows state.1 result.2.1 :=
  ⟨fun input value hvalue =>
      cache_persists_run rightKeep walk computation state result hresult input value hvalue,
    fun input hinput => by
      rw [HandlerCarrier.Served,
        served_run_of_clear rightKeep walk computation state result hresult hclear]
      exact hinput⟩

/-! ## The same application, at the other invariant

`servedLog_iff_logServed` asks for `LogFiled` where `carrierLogged_run_with` asked for
`CarrierLogged`. `logFiled_run_with` is the mirror law, started by `logFiled_nil` and wanting
`SignerFaithful`, which `signerFaithful_sign` supplies. The verifier's stage is `LogFiled.mono`
against the growth just proved. -/

/-- **The middle stage leaves the log filed.** -/
theorem logFiled_phase (rightKeep : Walk → Bytes → HandlerCarrier.State → Prop)
    (walk : Walk) (sk : SecretKey) (hpk : sk.publicKey = keyAt walk)
    {α : Type} (phase : OracleComp (OracleWorld + SigningSpec) α)
    (accumulated : Multiplicative Tally) (state : CountedState)
    (z : α × (Multiplicative Tally × SigningLog × CountedState))
    (hz : z ∈ support ((simulateQ (ServedAgreement.servingPhaseWith (handlerAt rightKeep walk)
      (Scheme.sign sk)) phase).run (accumulated, [], state))) :
    ServedAgreement.LogFiled sk z.2.2.1 z.2.2.2.1 :=
  ServedAgreement.logFiled_run_with (keyAt walk) (handlerAt rightKeep walk)
    (files_countedCarrierRecorder (keyAt walk) (rightKeep walk)) (Scheme.sign sk) sk hpk
    (ServedAgreement.signerShape_sign sk)
    (ServedAgreement.signerFaithful_sign (keyAt walk) (handlerAt rightKeep walk)
      (files_countedCarrierRecorder (keyAt walk) (rightKeep walk)) sk)
    phase (accumulated, [], state) (ServedAgreement.logFiled_nil sk _) z hz

/-- **And the verifier's stage keeps it.** -/
theorem logFiled_run (sk : SecretKey) (log : SigningLog)
    (rightKeep : Walk → Bytes → HandlerCarrier.State → Prop) (walk : Walk)
    {α : Type} (computation : OracleComp OracleWorld α)
    (state : CountedState) (result : α × CountedState)
    (hresult : result ∈ support ((simulateQ (handlerAt rightKeep walk) computation).run state))
    (hclear : state.1.framing = none)
    (hfiled : ServedAgreement.LogFiled sk log state.1) :
    ServedAgreement.LogFiled sk log result.2.1 :=
  hfiled.mono (grows_run_of_clear rightKeep walk computation state result hresult hclear)

/-! ## And the containment itself

`ServedBridge.CarrierBelowLog`, at a pre-projection carrier that is logged and a log that is
filed. No recorder, no stages, no run: the two invariants are the whole of it. -/

/-- **The carrier's served set is below the log's.** -/
theorem carrierBelowLog_of_invariants (sk : SecretKey) (pk : PublicKey)
    (hpk : sk.publicKey = pk) (log : SigningLog) (carrier : HandlerCarrier.State)
    (hfiled : ServedAgreement.LogFiled sk log carrier)
    (hlogged : ServedAgreement.CarrierLogged sk ∅ log carrier)
    (result : (Outcome × Nat) × QueryCache HashSpec)
    (hsigned : result.1.1.signed = log)
    (hcache : ∀ (input : Bytes) (value : HashOutput), carrier.cache input = some value →
      result.2 input = some value) :
    ServedBridge.CarrierBelowLog pk carrier result := by
  intro input hserved
  exact (ServedAgreement.servedLog_iff_logServed sk pk hpk log carrier hfiled result.2 hcache
    result hsigned input).mpr
    (hlogged result.2 hcache (fun _ _ hvalue => absurd hvalue (by simp)) input hserved)

end SlhDsaSecurity.CarrierServedLog
