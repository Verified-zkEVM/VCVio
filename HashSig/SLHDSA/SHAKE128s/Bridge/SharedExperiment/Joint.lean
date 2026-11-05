/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module
public import HashSig.SLHDSA.SHAKE128s.Bridge.SharedExperiment.Observation
public import HashSig.SLHDSA.SHAKE128s.Statement.FIPS205
public import VCVio.OracleComp.QueryTracking.Enforcement
public import HashSig.SLHDSA.SHAKE128s.Bridge.SharedExperiment.Factory
public import HashSig.SLHDSA.Security.ByteRouter
import VCVio.CryptoFoundations.SignatureAlg.CountedExperiment.CostMap

/-!
# Joint source recovery and resource observations

The same complete counted program is interpreted once by the shared random oracle.
Raw optional replies determine the same fresh pair, and the five counters are retained jointly.
Chronological encoding connects honest typed algorithms and the original raw adversary,
preserving complete keys, replies, verification, cache, paid costs and abort state.
-/

public section

open OracleComp OracleSpec SignatureAlg
open SLHDSA.SHAKE128s
open SLHDSA.Security

namespace SLHDSA.SHAKE128s.Bridge.SharedExperiment


open scoped Classical in
/-- Observe the shared counted program's winning bit and full original source vector. -/
@[expose] noncomputable def observedGame {Output PK SK : Type} [SampleableType Output]
    (scheme : Game.ExternalScheme Output PK SK) : SecurityGame Unit Unforgeability.QueryKind where
  Adversary := Game.Adversary Output PK
  experiment := fun _ adversary =>
    (fun result => (decide (SigningView.Wins id result.toOutcome), result.cost)) <$>
      RandomOracleModel.run (canonicalExperiment scheme adversary)

private theorem reconstruct
    (observed : SigningView.Observation Message Bytes (Option Bytes) SourceCounts) :
    (legacyObservation observed).2 = observed.cost :=
  Game.Counted.legacyObservation_counts observed

private theorem winning
    (observed : SigningView.Observation Message Bytes (Option Bytes) SourceCounts) :
    Game.Wins (legacyObservation observed).1 ↔ SigningView.Wins id observed.toOutcome := by
  simp only [Game.Wins, SigningView.Wins, legacyObservation, legacyOutcome]
  exact and_congr Iff.rfl
    (SigningView.optional_fresh_iff observed.rawLog observed.forgery.1 observed.forgery.2).symm

private theorem run_map {Output α β : Type} [SampleableType Output]
    (f : α → β) (program : OracleComp (Game.World Output) α) :
    RandomOracleModel.run (f <$> program) = f <$> RandomOracleModel.run program := by
  simp only [RandomOracleModel.run, simulateQ_map, StateT.run'_map']

/-- Both games have exactly the same joint winning-bit and five-source program. -/
theorem jointExperiment {Output PK SK : Type} [SampleableType Output]
    (scheme : Game.ExternalScheme Output PK SK) (adversary : Game.Adversary Output PK) :
    (observedGame scheme).experiment () adversary =
      (Game.securityGame scheme).experiment () adversary := by
  change _ = (fun result => (decide (Game.Wins result.1), result.2)) <$>
    RandomOracleModel.run (Game.experimentBySource scheme adversary)
  rw [fullProgram, run_map, Functor.map_map]
  apply congrArg (fun f => f <$> RandomOracleModel.run (canonicalExperiment scheme adversary))
  funext observed
  apply Prod.ext
  · exact decide_eq_decide.mpr (winning observed).symm
  · exact (reconstruct observed).symm

/-- Every selected actual joint budget is preserved at the same cap. -/
theorem jointBudget {Output PK SK : Type} [SampleableType Output]
    (scheme : Game.ExternalScheme Output PK SK) (adversary : Game.Adversary Output PK)
    (selected : Finset Unforgeability.QueryKind) (q : Nat) :
    (observedGame scheme).HasQueryBound () selected adversary q ↔
      (Game.securityGame scheme).HasQueryBound () selected adversary q := by
  simp only [SecurityGame.HasQueryBound, jointExperiment]

/-- The original probability-one signing limit is unchanged. -/
theorem lifetime {Output PK SK : Type} [SampleableType Output]
    (scheme : Game.ExternalScheme Output PK SK) (adversary : Game.Adversary Output PK) :
    (Pr{let result ← (observedGame scheme).experiment () adversary}[
      result.2 .sign ≤ 2 ^ 64] = 1) ↔ Game.WithinSigningLimit scheme adversary := by
  simp only [jointExperiment, Game.WithinSigningLimit, signingLimit]

end SLHDSA.SHAKE128s.Bridge.SharedExperiment

namespace SLHDSA.SHAKE128s.Bridge.SharedExperiment

/-- The actual real-byte source caps preserve its complete paired guarded observation. -/
theorem real_fips_marked_guard_eq_of_actual_joint_caps
    (adv : Game.Adversary FIPS205.Answer (PublicKeyCore FIPS205.core)) (q : Nat)
    (hlimit : Game.WithinSigningLimit FIPS205.scheme adv)
    (hbound : (Game.securityGame FIPS205.scheme).HasQueryBound () Game.adversaryWork adv q)
    (fallback : (input : (SigningView.Events.Spec
        (Game.World FIPS205.Answer) Message).Domain) →
      (SigningView.Events.Spec (Game.World FIPS205.Answer) Message).Range input) :
    let view := Game.Counted.externalView FIPS205.scheme
    let main := Game.Counted.externalMain adv
    let policy : SigningView.Event (Game.World FIPS205.Answer) Message → Nat × Nat :=
      fun event =>
        let counts := Game.Counted.sourcePolicy event
        ((∑ kind ∈ Game.adversaryWork, counts kind), counts .sign)
    let marked := SigningView.Events.fullExperiment view main
    let counted : SigningView.CostM (Game.World FIPS205.Answer) (Nat × Nat)
        (((PublicKeyCore FIPS205.core) × (SecretKeyCore FIPS205.core)) ×
          SigningView.Outcome Message Bytes (Option Bytes)) := do
      let keys ← SigningView.costed policy .keygen view.keygen
      let outcome ← SigningView.countedAfterKeygen policy view keys.1 keys.2 main
      return (keys, outcome)
    let handler := RandomOracleModel.impl Bytes FIPS205.Answer
    let guarded := (simulateQ (QueryImpl.guardQueryBudget (q, signingLimit)
      (Sum.elim (fun _ => (0, 0)) policy)
      (SigningView.Events.handlerWithEvents handler) fallback) marked).run
        (∅, ((0, 0), false))
    let source := (simulateQ handler counted.runAdd).run ∅
    (fun result => (if result.2.2.2 then none else some result.1, result.2)) <$>
      guarded =ᵈ
      (fun result => (some result.1.1, (result.2, (result.1.2, false)))) <$> source := by
  intro view main policy marked counted handler guarded source
  let project : SourceCounts →+ Nat × Nat := {
    toFun := fun counts => ((∑ kind ∈ Game.adversaryWork, counts kind), counts .sign)
    map_zero' := by simp
    map_add' := fun left right => by simp [Finset.sum_add_distrib] }
  have hpolicy : (fun event => project (sourcePolicy event)) = policy := rfl
  have mapped := SigningView.countedExperiment_mapCost project sourcePolicy view main
  rw [hpolicy] at mapped
  have work := (jointBudget FIPS205.scheme adv Game.adversaryWork q).mpr hbound
  have limit := (lifetime FIPS205.scheme adv).mpr hlimit
  simp only [SecurityGame.HasQueryBound, observedGame, prEvent_map] at work
  simp only [observedGame, prEvent_map] at limit
  have both : Pr{let observed ← (RandomOracleModel.run
      (canonicalExperiment FIPS205.scheme adv))}[
      (project observed.cost).1 ≤ q ∧ (project observed.cost).2 ≤ signingLimit] = 1 := by
    apply (prEvent_eq_one_iff _ _).mpr
    intro observed member
    exact ⟨(prEvent_eq_one_iff _ _).mp work observed member,
      (prEvent_eq_one_iff _ _).mp limit observed member⟩
  have paired : Pr{let observed ← (RandomOracleModel.run
      (SigningView.countedExperiment policy view main))}[
      observed.cost.1 ≤ q ∧ observed.cost.2 ≤ signingLimit] = 1 := by
    rw [← mapped, run_map, prEvent_map]
    exact both
  have dropKeys : (fun result =>
      ({ toOutcome := result.1.2, cost := result.2 } :
        SigningView.Observation Message Bytes (Option Bytes) (Nat × Nat))) <$>
      counted.runAdd = SigningView.countedExperiment policy view main := by
    simp only [counted, SigningView.countedExperiment, AddWriterT.runAdd_bind,
      AddWriterT.runAdd_pure, map_bind, map_pure, Functor.map_map,
      Prod.map, id_eq, add_zero]
    simp only [map_eq_bind_pure_comp]
    rfl
  have sourceCap : Pr{let result ← source}[
      result.1.2.1 ≤ q ∧ result.1.2.2 ≤ signingLimit] = 1 := by
    rw [← dropKeys, run_map, prEvent_map] at paired
    simpa only [RandomOracleModel.run, StateT.run'_eq, prEvent_map, source, handler] using paired
  let cost : (SigningView.Events.Spec (Game.World FIPS205.Answer) Message).Domain →
      Nat × Nat := Sum.elim (fun _ => (0, 0)) policy
  have sourceEq : ((simulateQ
      ((SigningView.Events.handlerWithEvents handler).withAddCost cost) marked).runAdd).run
        ∅ = source := by
    have observed := SigningView.Events.runObs_fullKeys_eq_counted view main policy handler ∅
    change (fun result => ((result.1.1, Multiplicative.toAdd result.1.2), result.2)) <$>
      (runObs handler (fun event => Multiplicative.ofAdd (policy event)) marked).run ∅ =
        source at observed
    have handlers : (SigningView.Events.handlerWithEvents handler).withAddCost cost =
        (eraseObsImpl handler).withCost
          (obsCostFn (fun event => Multiplicative.ofAdd (policy event))) := by
      funext input
      cases input <;>
        simp [QueryImpl.withAddCost, SigningView.Events.handlerWithEvents,
          eraseObsImpl, obsCostFn, cost,
          show (0, 0) = (0 : Nat × Nat) from rfl, ofAdd_zero]
    rw [handlers, AddWriterT.runAdd, StateT.run_map]
    simpa only [runObs, Prod.map, id_eq] using observed
  have gate := QueryImpl.evalDist_guardQueryBudget_eq_of_ae_caps (q, signingLimit) cost
    (SigningView.Events.handlerWithEvents handler) fallback marked (pure ∅)
    (by simpa only [pure_bind, sourceEq, Prod.le_def] using sourceCap)
  let : MeasurableSpace
      (Option (((PublicKeyCore FIPS205.core) × (SecretKeyCore FIPS205.core)) ×
        SigningView.Outcome Message Bytes (Option Bytes)) ×
        (QueryCache (RandomOracleModel.HashSpec Bytes FIPS205.Answer) ×
          ((Nat × Nat) × Bool))) := ⊤
  exact EvalDistEq.of_evalDist_eq (by
    simpa only [pure_bind, sourceEq, guarded, cost, Prod.zero_eq_mk] using gate)

/-! ## Encoding the honest typed and original raw source -/

private abbrev PK := PublicKeyCore FIPS205.core
private abbrev SK := SecretKeyCore FIPS205.core
private abbrev Raw := shakeSpec FIPS205.params
private abbrev H := hashSpec FIPS205.core
private abbrev R := Game.World FIPS205.Answer
private abbrev Ev := SigningView.Event R Message
private abbrev O := ObsSpec Ev
private abbrev Native := unifSpec + (H + Raw)
private abbrev Common := Native + O
private abbrev Alpha := (PK × SK) × SigningView.Outcome Message (List Byte) (Option (List Byte))

private noncomputable def encoding (pkSeed : FIPS205.core.PkSeed) :
    RandomOracleEncoding H (List Byte) FIPS205.Answer :=
  shakeEncoding FIPS205.params (by decide) (by decide) pkSeed


/-- Lift complete raw fallback answers to the mixed typed/raw interface coherently. -/
@[expose] noncomputable def mixedFallback (pkSeed : FIPS205.core.PkSeed)
    (originalFallback : (input : (SigningView.Events.Spec
      (Game.World FIPS205.Answer) Message).Domain) →
      (SigningView.Events.Spec (Game.World FIPS205.Answer) Message).Range input) :
    (input : ((unifSpec + (hashSpec FIPS205.core + shakeSpec FIPS205.params)) +
      ObsSpec (SigningView.Event (Game.World FIPS205.Answer) Message)).Domain) →
      ((unifSpec + (hashSpec FIPS205.core + shakeSpec FIPS205.params)) +
        ObsSpec (SigningView.Event (Game.World FIPS205.Answer) Message)).Range input
  | .inl (.inl n) => originalFallback (.inl (.inl n))
  | .inl (.inr (.inr raw)) => originalFallback (.inl (.inr raw))
  | .inl (.inr (.inl typed)) =>
      (shakeEncoding FIPS205.params (by decide) (by decide) pkSeed).trunc typed
        (originalFallback (.inl (.inr
          ((shakeEncoding FIPS205.params (by decide) (by decide) pkSeed).encode typed))))
  | .inr _ => PUnit.unit

/-- Encoding a free guarded common program preserves its complete guarded raw observation. -/
private theorem encodeFreeGuardedProgram :
  ∀
    {α : Type} (pkSeed : FIPS205.core.PkSeed)
    (caps : Nat × Nat) (policy : Ev → Nat × Nat)
    (fallback : (input : (R + O).Domain) → (R + O).Range input)
    (program : OracleComp Common α) (initialCache : QueryCache Raw),
    let encodeObserved : QueryImpl Common (OracleComp (R + O)) :=
      QueryImpl.add (spec₁ := Native) (spec₂ := O)
        (fun input => simulateQ (QueryImpl.ofLift R (OracleComp (R + O)))
          ((encoding pkSeed).encodeImpl input))
        (fun event => liftM ((R + O).query (.inr event)))
    let rawHandler := SigningView.Events.handlerWithEvents (Request := Message)
      (RandomOracleModel.impl (List Byte) FIPS205.Answer)
    let forwarder : QueryImpl Common (StateT PUnit (OracleComp Common)) :=
      (QueryImpl.id' Common).liftTarget (StateT PUnit (OracleComp Common))
    let guarded := (simulateQ (QueryImpl.guardQueryBudget caps
      (Sum.elim (fun _ => (0, 0)) policy) forwarder
      (mixedFallback pkSeed fallback)) program).run (PUnit.unit, ((0, 0), false))
    (fun result : (α × (PUnit × ((Nat × Nat) × Bool))) × QueryCache Raw =>
      (result.1.1, (result.2, result.1.2.2))) <$>
      (simulateQ rawHandler (simulateQ encodeObserved guarded)).run initialCache =
      (simulateQ (QueryImpl.guardQueryBudget caps
        (Sum.elim (fun _ => (0, 0)) policy) rawHandler fallback)
        (simulateQ encodeObserved program)).run (initialCache, ((0, 0), false))
 := by
  intro α pkSeed caps policy fallback program initialCache
    encodeObserved rawHandler forwarder guarded
  let commonCost : Common.Domain → Nat × Nat := Sum.elim (fun _ => (0, 0)) policy
  let rawCost : (R + O).Domain → Nat × Nat := Sum.elim (fun _ => (0, 0)) policy
  let rawForward : QueryImpl (R + O) (StateT PUnit (OracleComp (R + O))) :=
    (QueryImpl.id' (R + O)).liftTarget (StateT PUnit (OracleComp (R + O)))
  let commonGuard := QueryImpl.guardQueryBudget caps commonCost forwarder
    (mixedFallback pkSeed fallback)
  let rawGuard := QueryImpl.guardQueryBudget caps rawCost rawForward fallback
  let explicit : QueryImpl Common (OracleComp (R + O))
    | .inl (.inl n) => liftM ((R + O).query (.inl (.inl n)))
    | .inl (.inr (.inl typed)) => (encoding pkSeed).trunc typed <$>
        (liftM ((R + O).query (.inl (.inr ((encoding pkSeed).encode typed)))))
    | .inl (.inr (.inr raw)) => liftM ((R + O).query (.inl (.inr raw)))
    | .inr event => liftM ((R + O).query (.inr event))
  have normalize : encodeObserved = explicit := by
    funext input
    rcases input with (n | typed | raw) | event <;>
      simp [encodeObserved, explicit, QueryImpl.add, RandomOracleEncoding.encodeImpl,
        encoding] <;> rfl
  have step : encodeObserved.mapStateTBase commonGuard = rawGuard ∘ₛ encodeObserved := by
    rw [normalize]
    funext input
    apply StateT.ext
    intro state
    rcases state with ⟨token, counts, flag⟩
    rcases input with native | event
    · rcases native with n | typedOrRaw
      · cases flag <;> by_cases admitted : counts + (0, 0) ≤ caps <;>
          simp [admitted, QueryImpl.mapStateTBase, commonGuard, rawGuard,
            QueryImpl.guardQueryBudget, forwarder, rawForward, commonCost, rawCost,
            mixedFallback, explicit, QueryImpl.apply_compose]
      · rcases typedOrRaw with typed | raw
        · cases flag <;> by_cases admitted : counts + (0, 0) ≤ caps <;>
            simp [admitted, QueryImpl.mapStateTBase, commonGuard, rawGuard,
              QueryImpl.guardQueryBudget, forwarder, rawForward, commonCost, rawCost,
              mixedFallback, explicit, encoding, QueryImpl.apply_compose]
        · cases flag <;> by_cases admitted : counts + (0, 0) ≤ caps <;>
            simp [admitted, QueryImpl.mapStateTBase, commonGuard, rawGuard,
              QueryImpl.guardQueryBudget, forwarder, rawForward, commonCost, rawCost,
              mixedFallback, explicit, QueryImpl.apply_compose]
    · have hf := Subsingleton.elim (α := PUnit) (fallback (.inr event)) PUnit.unit
      cases flag <;> by_cases admitted : counts + policy event ≤ caps <;>
        simp [admitted, QueryImpl.mapStateTBase, commonGuard, rawGuard,
          QueryImpl.guardQueryBudget, forwarder, rawForward, commonCost, rawCost,
          mixedFallback, explicit, QueryImpl.apply_compose, hf]
  have free : simulateQ encodeObserved
        ((simulateQ commonGuard program).run (PUnit.unit, ((0, 0), false))) =
      (simulateQ rawGuard (simulateQ encodeObserved program)).run
        (PUnit.unit, ((0, 0), false)) := by
    rw [QueryImpl.simulateQ_mapStateTBase_run, step, QueryImpl.simulateQ_compose]
  change (fun result : (α × (PUnit × ((Nat × Nat) × Bool))) × QueryCache Raw =>
      (result.1.1, (result.2, result.1.2.2))) <$>
    (simulateQ rawHandler (simulateQ encodeObserved
      ((simulateQ commonGuard program).run (PUnit.unit, ((0, 0), false))))).run
        initialCache = _
  rw [free]
  exact QueryImpl.map_run_simulateQ_guardQueryBudget_free_eq caps rawCost rawHandler
    fallback (simulateQ encodeObserved program) initialCache (0, 0) false

/-- Expose the actual public-seed prefix of the complete chronological FIPS source. -/
private theorem actualMarkedSource_publicSeed
    (adv : Game.Adversary FIPS205.Answer PK) :
    SigningView.Events.fullExperiment (Game.Counted.externalView FIPS205.scheme)
        (Game.Counted.externalMain adv) = (do
      let seed ← simulateQ (SigningView.Events.phaseImpl R Message .keygen)
        (liftM ($ᵗ FIPS205.core.PkSeed) : OracleComp R FIPS205.core.PkSeed)
      SigningView.Events.fullExperiment
        (Bridge.SharedExperiment.pureShakeView FIPS205.params FIPS205.deterministicRand
          (pure seed)) (Game.Counted.externalMain adv)) := by
  let byteView (seed : FIPS205.core.PkSeed) :=
    Bridge.SharedExperiment.pureShakeView FIPS205.params FIPS205.deterministicRand (pure seed)
  have draw :
      (Bridge.SharedExperiment.pureShakeView FIPS205.params FIPS205.deterministicRand
        ($ᵗ FIPS205.core.PkSeed)).keygen = (do
      let seed ← (liftM ($ᵗ FIPS205.core.PkSeed) : OracleComp R FIPS205.core.PkSeed)
      (byteView seed).keygen) := by
    simp only [byteView, Bridge.SharedExperiment.pureShakeView_keygen, shakeRomScheme,
      SignatureAlg.map_keygen, romScheme, simulateQ_bind, simulateQ_encImpl_liftM,
      liftM_pure, pure_bind]
  have seedFields (first second : ProbComp FIPS205.core.PkSeed) :
      (Bridge.SharedExperiment.pureShakeView FIPS205.params FIPS205.deterministicRand
        first).sign = (Bridge.SharedExperiment.pureShakeView FIPS205.params
          FIPS205.deterministicRand second).sign ∧
      (Bridge.SharedExperiment.pureShakeView FIPS205.params FIPS205.deterministicRand
        first).verify = (Bridge.SharedExperiment.pureShakeView FIPS205.params
          FIPS205.deterministicRand second).verify := by
    constructor <;> rfl
  rw [← Bridge.SharedExperiment.fullExperiment_pureShakeView_fips205]
  unfold SigningView.Events.fullExperiment
  simp only [SigningView.Events.viewWithEvents]
  rw [draw, simulateQ_bind]
  simp only [bind_assoc]
  apply bind_congr
  intro seed
  apply bind_congr
  intro keys
  obtain ⟨seedSigning, seedVerifying⟩ := seedFields ($ᵗ FIPS205.core.PkSeed) (pure seed)
  simp only [SigningView.runWithSigningOracle, SigningView.signingOracle,
    seedSigning, seedVerifying]


/-- The genuine mixed source recovers the original guarded byte experiment under one policy. -/
theorem mixedSourceRecovery :
  ∀
    (caps : Nat × Nat) (policy : SigningView.Event (Game.World FIPS205.Answer) Message → Nat × Nat)
    (hfreeKeygenUniform : ∀ n : unifSpec.Domain,
      policy (.ambient .keygen (.inl n)) = (0, 0))
    (adv : Game.Adversary FIPS205.Answer (PublicKeyCore FIPS205.core))
    (fallback : (input : (SigningView.Events.Spec (Game.World FIPS205.Answer) Message).Domain) →
      (SigningView.Events.Spec (Game.World FIPS205.Answer) Message).Range input)
    (initialCache : QueryCache (shakeSpec FIPS205.params)),
    let Raw := shakeSpec FIPS205.params
    let H := hashSpec FIPS205.core
    let R := Game.World FIPS205.Answer
    let Ev := SigningView.Event R Message
    let O := ObsSpec Ev
    let Native := unifSpec + (H + Raw)
    let Common := Native + O
    let Alpha := ((PublicKeyCore FIPS205.core) × (SecretKeyCore FIPS205.core)) ×
      SigningView.Outcome Message (List Byte) (Option (List Byte))
    let Sign := Message →ₒ Option (List Byte)
    let rawEvent : SigningView.Event Native Message → Ev := fun event => match event with
      | .signingAttempt request => .signingAttempt request
      | .ambient phase (.inl n) => .ambient phase (.inl n)
      | .ambient phase (.inr (.inl typed)) =>
          .ambient phase (.inr (encode FIPS205.params typed))
      | .ambient phase (.inr (.inr raw)) => .ambient phase (.inr raw)
    let markerProjection : QueryImpl (SigningView.Events.Spec Native Message)
        (OracleComp Common) :=
      QueryImpl.add (spec₁ := Native)
        (spec₂ := ObsSpec (SigningView.Event Native Message))
        (QueryImpl.ofLift Native (OracleComp Common))
        (fun event => liftM (Common.query (.inr (rawEvent event))))
    let rawMain : PublicKeyCore FIPS205.core →
        OracleComp (Native + Sign) (Message × List Byte) := fun pk =>
      simulateQ (QueryImpl.add (spec₁ := R) (spec₂ := Sign)
        (fun input => simulateQ (QueryImpl.ofLift Native (OracleComp (Native + Sign)))
          (liftRawImpl (hs := H) input))
        (fun request => liftM ((Native + Sign).query (.inr request))))
        (Game.Counted.externalMain adv pk)
    let rawHandler := SigningView.Events.handlerWithEvents (Request := Message)
      (RandomOracleModel.impl (List Byte) FIPS205.Answer)
    (do
      let pkSeed ← ($ᵗ FIPS205.core.PkSeed : ProbComp FIPS205.core.PkSeed)
      let typedAlg := romScheme FIPS205.core (Equiv.refl _) FIPS205.deterministicRand
        (pure pkSeed)
      let view := SLHDSA.SigningView.fromInternalPure FIPS205.params
        (SLHDSA.Concrete.shakeWireCodec FIPS205.params.params)
        (typedAlg.map (simulateQ' (liftTypedImpl (hs := H) (ext := Raw))))
        (fun request : Message =>
          (SLHDSA.External.encodePureMessage request.context request.message).toOption)
      let mixed := simulateQ markerProjection (SigningView.Events.fullExperiment view rawMain)
      let forwarder : QueryImpl Common (StateT PUnit (OracleComp Common)) :=
        (QueryImpl.id' Common).liftTarget (StateT PUnit (OracleComp Common))
      let guarded := (simulateQ (QueryImpl.guardQueryBudget caps
        (Sum.elim (fun _ => (0, 0)) policy) forwarder
        (mixedFallback pkSeed fallback)) mixed).run (PUnit.unit, ((0, 0), false))
      let encodeObserved : QueryImpl Common (OracleComp (R + O)) :=
        QueryImpl.add (spec₁ := Native) (spec₂ := O)
          (fun input => simulateQ (QueryImpl.ofLift R (OracleComp (R + O)))
            ((shakeEncoding FIPS205.params (by decide) (by decide) pkSeed).encodeImpl input))
          (fun event => liftM ((R + O).query (.inr event)))
      (fun result : (Alpha × (PUnit × ((Nat × Nat) × Bool))) × QueryCache Raw =>
        (result.1.1, (result.2, result.1.2.2))) <$>
        (simulateQ rawHandler (simulateQ encodeObserved guarded)).run initialCache) =
      (simulateQ (QueryImpl.guardQueryBudget caps
        (Sum.elim (fun _ => (0, 0)) policy) rawHandler fallback)
        (SigningView.Events.fullExperiment (Game.Counted.externalView FIPS205.scheme)
          (Game.Counted.externalMain adv))).run (initialCache, ((0, 0), false))
 := by
  intro caps policy hfree adv fallback initialCache Raw H R Ev O Native Common Alpha
    Sign rawEvent markerProjection rawMain rawHandler
  let encodeObserved (seed : FIPS205.core.PkSeed) : QueryImpl Common (OracleComp (R + O)) :=
    QueryImpl.add (spec₁ := Native) (spec₂ := O)
      (fun input => simulateQ (QueryImpl.ofLift R (OracleComp (R + O)))
        ((encoding seed).encodeImpl input))
      (fun event => liftM ((R + O).query (.inr event)))
  let eventMap (seed : FIPS205.core.PkSeed) := encodeObserved seed ∘ₛ markerProjection
  let typedView (seed : FIPS205.core.PkSeed) :=
    SLHDSA.SigningView.fromInternalPure FIPS205.params
      (SLHDSA.Concrete.shakeWireCodec FIPS205.params.params)
      ((romScheme FIPS205.core (Equiv.refl _) FIPS205.deterministicRand (pure seed)).map
        (simulateQ' (liftTypedImpl (hs := H) (ext := Raw))))
      (fun request : Message =>
        (SLHDSA.External.encodePureMessage request.context request.message).toOption)
  let byteView (seed : FIPS205.core.PkSeed) :=
    Bridge.SharedExperiment.pureShakeView FIPS205.params FIPS205.deterministicRand (pure seed)
  have phase (seed : FIPS205.core.PkSeed) (p : SigningView.Phase)
      {β : Type} (body : OracleComp Native β) :
      simulateQ (eventMap seed) (simulateQ (SigningView.Events.phaseImpl Native Message p) body) =
        simulateQ (SigningView.Events.phaseImpl R Message p)
          (simulateQ (encoding seed).encodeImpl body) := by
    rw [← QueryImpl.simulateQ_compose (SigningView.Events.phaseImpl R Message p)
      (encoding seed).encodeImpl]
    apply QueryImpl.simulateQ_simulateQ_eq_of_apply
    intro input
    rcases input with n | typed | raw <;>
      simp [eventMap, encodeObserved, markerProjection, rawEvent,
        SigningView.Events.phaseImpl, SigningView.Events.emit, QueryImpl.apply_compose,
        QueryImpl.add, RandomOracleEncoding.encodeImpl] <;> rfl
  have honest (seed : FIPS205.core.PkSeed) (p : SigningView.Phase)
      {β : Type} (body : OracleComp (unifSpec + H) β) :
      simulateQ (eventMap seed) (simulateQ (SigningView.Events.phaseImpl Native Message p)
        (simulateQ (liftTypedImpl (hs := H) (ext := Raw)) body)) =
      simulateQ (SigningView.Events.phaseImpl R Message p)
        (simulateQ (encImpl FIPS205.params) body) := by
    have encoded : (encoding seed).encodeImpl ∘ₛ liftTypedImpl (hs := H) (ext := Raw) =
        encImpl FIPS205.params :=
      encodeImpl_shakeEncoding_compose_liftTypedImpl (vp := FIPS205.params)
        (by decide) (by decide) seed
    rw [phase, ← QueryImpl.simulateQ_compose (encoding seed).encodeImpl
      (liftTypedImpl (hs := H) (ext := Raw)), encoded]
  have keygen (seed : FIPS205.core.PkSeed) :
      simulateQ (eventMap seed) (SigningView.Events.viewWithEvents (typedView seed)).keygen =
        (SigningView.Events.viewWithEvents (byteView seed)).keygen := by
    simpa only [SigningView.Events.viewWithEvents, typedView, byteView,
      Bridge.SharedExperiment.pureShakeView, SLHDSA.SigningView.fromInternalPure,
      SigningView.rejectingEncoding_keygen, SignatureAlg.map_keygen, shakeRomScheme,
      simulateQ'_apply] using honest seed .keygen
        (romScheme FIPS205.core (Equiv.refl _) FIPS205.deterministicRand (pure seed)).keygen
  have signing (seed : FIPS205.core.PkSeed) (pk : PK) (sk : SK) (request : Message) :
      simulateQ (eventMap seed)
          ((SigningView.Events.viewWithEvents (typedView seed)).sign pk sk request) =
        (SigningView.Events.viewWithEvents (byteView seed)).sign pk sk request := by
    simp only [SigningView.Events.viewWithEvents, typedView, byteView,
      Bridge.SharedExperiment.pureShakeView, SLHDSA.SigningView.fromInternalPure,
      SigningView.rejectingEncoding_sign, SignatureAlg.map_sign, shakeRomScheme,
      simulateQ_bind]
    rw [show simulateQ (eventMap seed) (SigningView.Events.emit Native Message
        (.signingAttempt request)) = SigningView.Events.emit R Message
        (.signingAttempt request) by simp [eventMap, encodeObserved, markerProjection,
          rawEvent, SigningView.Events.emit, QueryImpl.apply_compose, QueryImpl.add]]
    congr 1
    funext _
    split
    · simp only [simulateQ_pure]
    · simp only [simulateQ_map]
      exact congrArg (fun body => (some ∘ encodeSignature FIPS205.params
        (Concrete.shakeWireCodec FIPS205.params.params)) <$> body)
        (honest seed .signer _)
  have verification (seed : FIPS205.core.PkSeed) (pk : PK)
      (request : Message) (wire : List Byte) :
      simulateQ (eventMap seed)
          ((SigningView.Events.viewWithEvents (typedView seed)).verify pk request wire) =
        (SigningView.Events.viewWithEvents (byteView seed)).verify pk request wire := by
    let frame := fun request : Message =>
      (External.encodePureMessage request.context request.message).toOption
    let decode := fun wire : List Byte => (SLHDSA.decodeSignature FIPS205.params
      (SLHDSA.Concrete.shakeWireCodec FIPS205.params.params) wire).toOption
    change simulateQ (eventMap seed)
      (simulateQ (SigningView.Events.phaseImpl Native Message .verification)
        (SigningView.Encoding.verify frame decode
          (fun pk message signature => simulateQ (liftTypedImpl (hs := H) (ext := Raw))
            (GeneralScheme.verifyInternalM FIPS205.params FIPS205.core message signature pk))
          pk request wire)) =
      simulateQ (SigningView.Events.phaseImpl R Message .verification)
        (SigningView.Encoding.verify frame decode
          (fun pk message signature => simulateQ (encImpl FIPS205.params)
            (GeneralScheme.verifyInternalM FIPS205.params FIPS205.core message signature pk))
          pk request wire)
    unfold SigningView.Encoding.verify
    split
    · simp
    · split
      · simp
      · exact honest seed .verification _
  let embed : QueryImpl (R + O) (OracleComp ((R + O) + Sign)) :=
    fun input => liftM (((R + O) + Sign).query (.inl input))
  let mappedClient (seed : FIPS205.core.PkSeed) :
      QueryImpl (SigningView.Events.Spec Native Message + Sign)
        (OracleComp ((R + O) + Sign)) :=
    QueryImpl.add (fun native => simulateQ embed (eventMap seed native))
      (fun request => liftM (((R + O) + Sign).query (.inr request)))
  have client (seed : FIPS205.core.PkSeed) (pk : PK) (sk : SK)
      {β : Type} (body : OracleComp (SigningView.Events.Spec Native Message + Sign) β) :
      simulateQ (eventMap seed)
          ((SigningView.Events.viewWithEvents (typedView seed)).runWithSigningOracle pk sk body) =
        (SigningView.Events.viewWithEvents (byteView seed)).runWithSigningOracle pk sk
          (simulateQ (mappedClient seed) body) := by
    let targetLog : QueryImpl ((R + O) + Sign)
        (WriterT (QueryLog Sign) (OracleComp (R + O))) :=
      (R + O).passthrough +
        (SigningView.Events.viewWithEvents (byteView seed)).signingOracle pk sk
    have pass : targetLog ∘ₛ embed =
        (QueryImpl.id' (R + O)).liftTarget (WriterT (QueryLog Sign) (OracleComp (R + O))) := by
      funext input
      simp [targetLog, embed, QueryImpl.apply_compose]
    simp only [SigningView.runWithSigningOracle]
    rw [simulateQ_WriterT_compose
      ((SigningView.Events.Spec Native Message).passthrough +
        (SigningView.Events.viewWithEvents (typedView seed)).signingOracle pk sk)
      (eventMap seed) (targetLog ∘ₛ mappedClient seed), QueryImpl.simulateQ_compose]
    rintro (native | request)
    · simp only [QueryImpl.apply_compose, mappedClient, QueryImpl.add]
      rw [← QueryImpl.simulateQ_compose, pass, writerT_run_simulateQ_liftTarget,
        simulateQ_id']
      simp
    · simp [QueryImpl.apply_compose, mappedClient, targetLog, QueryImpl.add,
        SigningView.signingOracle, signing]
  have main (seed : FIPS205.core.PkSeed) (pk : PK) :
      simulateQ (mappedClient seed)
          (SigningView.Events.mainWithEvents rawMain pk) =
        SigningView.Events.mainWithEvents (Game.Counted.externalMain adv) pk := by
    unfold SigningView.Events.mainWithEvents
    dsimp only [rawMain]
    simp only [← QueryImpl.simulateQ_compose]
    apply congrArg (fun handler : QueryImpl (R + Sign) (OracleComp ((R + O) + Sign)) =>
      simulateQ handler (Game.Counted.externalMain adv pk))
    funext input
    rcases input with (n | raw) | request <;>
      simp [eventMap, encodeObserved, markerProjection, rawEvent, liftRawImpl,
        SigningView.Events.phaseImpl, SigningView.Events.emit, embed, mappedClient,
        QueryImpl.apply_compose, QueryImpl.add, RandomOracleEncoding.encodeImpl] <;> rfl
  have source (seed : FIPS205.core.PkSeed) :
      simulateQ (eventMap seed) (SigningView.Events.fullExperiment (typedView seed) rawMain) =
        SigningView.Events.fullExperiment (byteView seed) (Game.Counted.externalMain adv) := by
    unfold SigningView.Events.fullExperiment
    simp only [simulateQ_bind, simulateQ_pure]
    rw [keygen]
    apply bind_congr
    intro keys
    rw [client, main]
    apply bind_congr
    intro result
    rw [verification]
  let initial := (initialCache, ((0, 0), false))
  let controlled := QueryImpl.guardQueryBudget caps
    (Sum.elim (fun _ => (0, 0)) policy) rawHandler fallback
  let uniformInput := QueryImpl.ofLift unifSpec (OracleComp R)
  let markedUniform := SigningView.Events.phaseImpl R Message .keygen ∘ₛ uniformInput
  have uniformLift {β : Type} (body : ProbComp β) :
      simulateQ uniformInput body = (liftM body : OracleComp R β) := by
    change OracleComp.liftComp body R = _
    exact OracleComp.liftComp_eq_liftM body
  have samplePrefix {β : Type} (body : ProbComp β) :
      (simulateQ controlled
        (simulateQ (SigningView.Events.phaseImpl R Message .keygen)
          (liftM body : OracleComp R β))).run initial =
        (fun value => (value, initial)) <$> body := by
    let plain := (QueryImpl.id' unifSpec).liftTarget (StateT PUnit ProbComp)
    have admissible : ((0, 0) : Nat × Nat) ≤ caps := bot_le
    have step : ∀ n (token : PUnit),
        Prod.map id (fun _ : PUnit => initial) <$> (plain n).run token =
          ((controlled ∘ₛ markedUniform) n).run initial := by
      intro n token
      change _ = (simulateQ controlled
        (simulateQ (SigningView.Events.phaseImpl R Message .keygen)
          (liftM (R.query (.inl n))))).run initial
      rw [simulateQ_spec_query]
      simp [plain, controlled, initial, SigningView.Events.phaseImpl, SigningView.Events.emit,
        QueryImpl.guardQueryBudget, rawHandler, SigningView.Events.handlerWithEvents,
        RandomOracleModel.impl, unifFwdImpl, hfree, admissible]
    have projected := OracleComp.map_run_simulateQ_eq_of_query_map_eq plain
      (controlled ∘ₛ markedUniform) (fun _ : PUnit => initial) step body PUnit.unit
    simpa [plain, markedUniform, QueryImpl.simulateQ_compose, uniformLift,
      simulateQ_liftTarget, simulateQ_id',
      StateT.run_monadLift, Function.comp_def] using projected.symm
  calc
    _ = (do
      let seed ← ($ᵗ FIPS205.core.PkSeed : ProbComp FIPS205.core.PkSeed)
      (simulateQ controlled (SigningView.Events.fullExperiment (byteView seed)
        (Game.Counted.externalMain adv))).run initial) := by
      apply bind_congr
      intro seed
      have embeddedSource : simulateQ (encodeObserved seed) (simulateQ markerProjection
          (SigningView.Events.fullExperiment (typedView seed) rawMain)) =
          SigningView.Events.fullExperiment (byteView seed) (Game.Counted.externalMain adv) := by
        rw [← QueryImpl.simulateQ_compose]
        exact source seed
      exact (encodeFreeGuardedProgram (α := Alpha) seed caps policy fallback
        (simulateQ markerProjection (SigningView.Events.fullExperiment (typedView seed) rawMain))
        initialCache).trans
          (congrArg (fun program => (simulateQ controlled program).run initial) embeddedSource)
    _ = _ := by
      rw [actualMarkedSource_publicSeed]
      dsimp only [controlled, initial] at samplePrefix
      dsimp only [R, SLHDSA.SHAKE128s.Bridge.SharedExperiment.R]
        at samplePrefix ⊢
      simp only [simulateQ_bind, StateT.run_bind, samplePrefix, bind_map_left]
      rfl

end SLHDSA.SHAKE128s.Bridge.SharedExperiment
