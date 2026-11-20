/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module

public import HashSig.SLHDSA.SHAKE128s.Bridge.SharedExperiment.Joint
import VCVio.OracleComp.SimSemantics.StateT.StateProjection
public import HashSig.SLHDSA.Security.KeyReconstruction
public import HashSig.SLHDSA.SigningView.Encoding
import VCVio.OracleComp.SimSemantics.StateT.PreservesInv
import VCVio.OracleComp.SimSemantics.StateT.StateSeparating
import all VCVio.OracleComp.Coercions.Add.Basic
import all VCVio.OracleComp.Coercions.SubSpec.Basic
import all Cslib.Foundations.Data.PFunctor.Free

/-! # Fixed-secret simulation of the guarded FIPS key sampler -/

public section

section

open OracleComp OracleSpec SignatureAlg
open SLHDSA SLHDSA.Security SLHDSA.SHAKE128s
open SLHDSA.SHAKE128s.Bridge.SharedExperiment.Guarded
namespace SLHDSA.SHAKE128s.Bridge.SharedExperiment.Native
/-- The FIPS secret-key record used by the physical SHAKE-128s experiment. -/
abbrev SK := SecretKeyCore FIPS205.core
/-- The uniformly sampled secret seed pair. -/
abbrev Secret := FIPS205.core.SkSeed × FIPS205.core.SkPrf
/-- The joint state of the typed hash cache and the raw byte-query cache. -/
abbrev TypedPV := H.QueryCache × Raw.QueryCache
/-- Canonical raw fallback lifted through the actual typed truncations. -/
@[expose] noncomputable def mixedFallback (pkSeed : FIPS205.core.PkSeed) :
    (input : Common.Domain) → Common.Range input
  | .inl (.inl n) => rawFallback (.inl (.inl n))
  | .inl (.inr (.inl typed)) =>
      (encoding pkSeed).trunc typed
        (rawFallback (.inl (.inr ((encoding pkSeed).encode typed))))
  | .inl (.inr (.inr bytes)) => rawFallback (.inl (.inr bytes))
  | .inr _ => PUnit.unit

/-- Original byte labels of resolved native observations. -/
@[expose] def rawEvent : SigningView.Event Native Message → Ev
  | .signingAttempt request => .signingAttempt request
  | .ambient phase (.inl n) => .ambient phase (.inl n)
  | .ambient phase (.inr (.inl typed)) =>
      .ambient phase (.inr (encode FIPS205.params typed))
  | .ambient phase (.inr (.inr bytes)) => .ambient phase (.inr bytes)

/-- Resolved native queries with their original-source event labels. -/
@[expose] def resolvedProjection :
    QueryImpl (SigningView.Events.Spec Native Message) (OracleComp Common) :=
  QueryImpl.add (QueryImpl.ofLift Native (OracleComp Common))
    (fun event => liftM (Common.query (.inr (rawEvent event))))

/-- Public native observations before their unresolved native query. -/
@[expose] def sparsePhase (phase : SigningView.Phase) : QueryImpl DNative (OracleComp DCommon) :=
  QueryImpl.preInsert
    (fun input => (liftM (DCommon.query (.inl input)) : OracleComp DCommon (DNative.Range input)))
    (fun input => match nativeObservation input with
      | some label => liftM (DCommon.query (.inr (.ambient phase label)))
      | none => pure PUnit.unit)

/-- Existing secret derivations resolved into the native typed/raw interface. -/
@[expose] noncomputable def resolveNative (pkSeed : FIPS205.core.PkSeed) (secret : Secret) :
    QueryImpl DNative (OracleComp Native) :=
  QueryImpl.add
    (fun input => simulateQ (liftTypedImpl (hs := H) (ext := Raw))
      ((secretEncoding FIPS205.core (Equiv.refl _) pkSeed).deriveImpl secret input))
    (fun bytes => liftM (Native.query (.inr (.inr bytes))))

/-- The actual external raw client at the resolved native interface. -/
@[expose] def rawMain (adv : Game.Adversary FIPS205.Answer PK) (pk : PK) :
    OracleComp (Native + Sign) (Message × List Byte) :=
  simulateQ (QueryImpl.add
    (fun input => simulateQ (QueryImpl.ofLift Native (OracleComp (Native + Sign)))
      (liftRawImpl (hs := H) input))
    (fun request => liftM ((Native + Sign).query (.inr request))))
    (Game.Counted.externalMain adv pk)

/-- Strict FIPS framing and canonical signatures around the real seeded scheme. -/
@[expose] noncomputable def realView (pkSeed : FIPS205.core.PkSeed) :
    SigningView (OracleComp Native) Message PK SK (List Byte) (Option (List Byte)) :=
  SLHDSA.SigningView.fromInternalPure FIPS205.params
    (SLHDSA.Concrete.shakeWireCodec FIPS205.params.params)
    ((romScheme FIPS205.core (Equiv.refl _) (fun pk => pure pk.pkSeed) (pure pkSeed)).map
      (simulateQ' (liftTypedImpl (hs := H) (ext := Raw))))
    (fun request => (External.encodePureMessage request.context request.message).toOption)

end SLHDSA.SHAKE128s.Bridge.SharedExperiment.Native
end

namespace SLHDSA.SHAKE128s.Bridge.SharedExperiment.Native

open SLHDSA.SHAKE128s.Bridge.SharedExperiment.Guarded

/-- Full source result retaining the actual secret key and complete optional reply log. -/
abbrev SecretFull := (PK × SK) × RawOutcome

end SLHDSA.SHAKE128s.Bridge.SharedExperiment.Native

section

open SLHDSA.SHAKE128s.Bridge.SharedExperiment.Guarded
open OracleComp OracleSpec SignatureAlg
open SLHDSA SLHDSA.Security SLHDSA.SHAKE128s

namespace SLHDSA.SHAKE128s.Bridge.SharedExperiment.Native
/-- Marked and sparse phases expose their actual one-query blocks. -/
theorem phase_query_normalforms :
  (∀ (phase : SigningView.Phase) (input : Native.Domain),
    simulateQ resolvedProjection
      (simulateQ (SigningView.Events.phaseImpl Native Message phase)
        (liftM (Native.query input) : OracleComp Native (Native.Range input))) =
      (do
        let _ ← (liftM (Common.query (.inr (rawEvent (.ambient phase input)))) :
          OracleComp Common PUnit)
        (liftM (Common.query (.inl input)) : OracleComp Common (Native.Range input)))) ∧
  ∀ (phase : SigningView.Phase) (input : DNative.Domain),
    sparsePhase phase input = (do
      let _ ← match nativeObservation input with
        | some label => (liftM (DCommon.query (.inr (.ambient phase label))) :
            OracleComp DCommon PUnit)
        | none => pure PUnit.unit
      (liftM (DCommon.query (.inl input)) : OracleComp DCommon (DNative.Range input))) := by
  constructor
  · intro phase input
    rw [simulateQ_spec_query]
    simp only [SigningView.Events.phaseImpl, QueryImpl.preInsert_apply, monadLift_self,
      SigningView.Events.emit, simulateQ_bind, simulateQ_spec_query]
    simp only [resolvedProjection, QueryImpl.add_eq_hAdd, QueryImpl.add_apply_inl,
      QueryImpl.add_apply_inr,
      QueryImpl.ofLift_apply]
    have queryForward :
        (liftM (Native.query input) : OracleQuery Common (Native.Range input)) =
          Common.query (.inl input) := by
      change (liftM (liftM (liftM (Native.query input) :
        OracleQuery (unifSpec + (H + (Raw + O))) (Native.Range input)) :
        OracleQuery (unifSpec + ((H + Raw) + O)) (Native.Range input)) :
        OracleQuery Common (Native.Range input)) = _
      rcases input with n | (typed | bytes)
      · rw [OracleQuery.liftM_right_add_right_add_query,
          OracleQuery.liftM_right_add_right_add_query, OracleQuery.liftM_add_assoc_query]
      · simp only [OracleQuery.liftM_right_add_right_add_query,
          OracleQuery.liftM_add_assoc_query, OracleQuery.liftM_add_right_query]
      · simp only [OracleQuery.liftM_right_add_right_add_query,
          OracleQuery.liftM_add_left_query, OracleQuery.liftM_add_right_query,
          OracleQuery.liftM_add_assoc_query]
    have forward :
        (liftM (Native.query input) : OracleComp Common (Native.Range input)) =
          (liftM (Common.query (.inl input)) : OracleComp Common (Native.Range input)) := by
      exact (OracleComp.liftM_eq_liftM_liftM (spec := Native) (superSpec := Common)
        (Native.query input)).trans (congrArg
          (fun q : OracleQuery Common (Native.Range input) =>
            (liftM q : OracleComp Common (Native.Range input))) queryForward)
    exact congrArg (fun next : OracleComp Common (Native.Range input) => ((do
      let _ ← (liftM (Common.query (.inr (rawEvent (.ambient phase input)))) :
        OracleComp Common PUnit)
      next) : OracleComp Common (Native.Range input))) forward
  · intro phase input
    unfold sparsePhase
    rw [QueryImpl.preInsert_apply]
    cases nativeObservation input <;> simp

end SLHDSA.SHAKE128s.Bridge.SharedExperiment.Native

namespace SLHDSA.SHAKE128s.Bridge.SharedExperiment.Native

/-- Native resolution forwards public ports and resolves both private query constructors. -/
theorem resolve_native_blocks :
  ∀ (pkSeed : FIPS205.core.PkSeed) (secret : Secret),
    (∀ n : unifSpec.Domain,
      resolveNative pkSeed secret (.inl (.inl (.inl n))) =
        (liftM (Native.query (.inl n)) : OracleComp Native (Fin (n + 1)))) ∧
    (∀ typed : H.Domain,
      resolveNative pkSeed secret (.inl (.inl (.inr typed))) =
        (liftM (Native.query (.inr (.inl typed))) : OracleComp Native (H.Range typed))) ∧
    (∀ key : PrfKey FIPS205.core,
      resolveNative pkSeed secret (.inl (.inr (.inl key))) =
        (liftM (Native.query (.inr (.inl (.inl (.thash pkSeed key.1 [secret.1]))))) :
          OracleComp Native FIPS205.core.Y)) ∧
    (∀ (salt : FIPS205.core.Y) (message : List Byte),
      resolveNative pkSeed secret (.inl (.inr (.inr (salt, message)))) =
        (liftM (Native.query (.inr (.inl (.inr ⟨secret.2, salt, message⟩)))) :
          OracleComp Native FIPS205.core.Y)) ∧
    ∀ bytes : List Byte,
      resolveNative pkSeed secret (.inr bytes) =
        (liftM (Native.query (.inr (.inr bytes))) : OracleComp Native FIPS205.Answer) := by
  intro pkSeed secret
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  all_goals intros; rfl

/-- Canonical byte fallbacks agree with resolution, and honest private markers are free. -/
theorem canonical_fallback_and_private_marker :
  ∀ (pkSeed : FIPS205.core.PkSeed) (secret : Secret)
    (reserve trackRaw : Bool),
    (∀ input : DNative.Domain,
      simulateQ (fun native => (pure (mixedFallback pkSeed (.inl native)) :
        ProbComp (Native.Range native))) (resolveNative pkSeed secret input) =
          pure (deriveFallback pkSeed (.inl input))) ∧
    ∀ (derivation : DeriveQuery FIPS205.core) (phase : SigningView.Phase),
      phase = .keygen ∨ phase = .signer →
      let query := (secretEncoding FIPS205.core (Equiv.refl _) pkSeed).enc secret derivation
      let event : Ev := .ambient phase (.inr (encode FIPS205.params query))
      policy reserve pkSeed event = (0, 0) ∧ metadataCost trackRaw pkSeed event = 0 := by
  intro pkSeed secret reserve trackRaw
  constructor
  · intro input
    rcases input with ((n | typed) | (key | ⟨salt, message⟩)) | bytes
    all_goals rfl
  · intro derivation phase privatePhase
    rcases privatePhase with rfl | rfl
    all_goals
      simp [policy, originalPolicy, reserveExtra, metadataCost, selectedRaw,
        Game.Counted.sourcePolicy, Game.Counted.sourceKind, Game.hashCost,
        RandomOracleModel.hashCost]

end SLHDSA.SHAKE128s.Bridge.SharedExperiment.Native

namespace SLHDSA.SHAKE128s.Bridge.SharedExperiment.Native
/-- A private phase marker is free and preserves ready FIPS metadata. -/
theorem actual_private_marker_inert :
  ∀ {Cache : Type} (handler : QueryImpl Native (StateT Cache ProbComp))
    (pkSeed : FIPS205.core.PkSeed) (secret : Secret) (reserve trackRaw : Bool)
    (derivation : DeriveQuery FIPS205.core) (phase : SigningView.Phase)
    (_privatePhase : phase = .keygen ∨ phase = .signer)
    (caps initialCounts : Nat × Nat) (initialAborted : Bool)
    (initialCache : Cache) (initialMetadata : Meta)
    (_phaseReady : initialAborted = false → initialCounts ≤ caps →
      initialMetadata.2 = phase),
    let charge := metadataCost trackRaw pkSeed
    let observed := (eraseObsImpl (Ev := Ev) handler).extendState (aux charge)
    let query := (secretEncoding FIPS205.core (Equiv.refl _) pkSeed).enc secret derivation
    let event : Ev := .ambient phase (.inr (encode FIPS205.params query))
    policy reserve pkSeed event = (0, 0) ∧
      (initialAborted = false → initialCounts ≤ caps →
        (observed (.inr event)).run (initialCache, initialMetadata) =
          pure (PUnit.unit, (initialCache, initialMetadata))) := by
  intro Cache handler pkSeed secret reserve trackRaw derivation phase privatePhase caps
    initialCounts initialAborted initialCache initialMetadata phaseReady charge observed query event
  have marker :=
    (SLHDSA.SHAKE128s.Bridge.SharedExperiment.Native.canonical_fallback_and_private_marker
    pkSeed secret reserve trackRaw).2 derivation phase privatePhase
  refine ⟨marker.1, ?_⟩
  intro hfalse hfits
  dsimp only [observed]
  rw [QueryImpl.extendState_apply, eraseObsImpl_inr, StateT.run_pure, pure_bind]
  change pure (PUnit.unit, (initialCache,
      (initialMetadata.1 + metadataCost trackRaw pkSeed event, phase))) =
    pure (PUnit.unit, (initialCache, initialMetadata))
  rw [marker.2, Nat.add_zero, ← phaseReady hfalse hfits]

end SLHDSA.SHAKE128s.Bridge.SharedExperiment.Native

namespace SLHDSA.SHAKE128s.Bridge.SharedExperiment.Native

/-- Resolved marked and sparse unresolved blocks preserve the entire guarded state. -/
theorem guarded_phase_query_square :
  ∀ {Cache : Type}
    (handler : QueryImpl Native (StateT Cache ProbComp))
    (pkSeed : FIPS205.core.PkSeed) (secret : Secret)
    (reserve trackRaw : Bool) (phase : SigningView.Phase)
    (input : DNative.Domain)
    (_privatePhase : nativeObservation input = none → phase = .keygen ∨ phase = .signer)
    (caps initialCounts : Nat × Nat) (initialAborted : Bool)
    (initialCache : Cache) (initialMetadata : Meta)
    (_phaseReady : nativeObservation input = none → initialAborted = false →
      initialCounts ≤ caps → initialMetadata.2 = phase),
    let charge := metadataCost trackRaw pkSeed
    let oldHandler := (eraseObsImpl (Ev := Ev) handler).extendState (aux charge)
    let newHandler :=
      (eraseObsImpl (Ev := Ev) (handler ∘ₛ resolveNative pkSeed secret)).extendState (aux charge)
    let oldGuard := QueryImpl.guardQueryBudget caps
      (Sum.elim (fun _ : Native.Domain => (0, 0)) (policy reserve pkSeed))
      oldHandler (mixedFallback pkSeed)
    let newGuard := QueryImpl.guardQueryBudget caps
      (Sum.elim (fun _ : DNative.Domain => (0, 0)) (policy reserve pkSeed))
      newHandler (deriveFallback pkSeed)
    let resolvedMarked := simulateQ resolvedProjection
      (simulateQ (SigningView.Events.phaseImpl Native Message phase)
        (resolveNative pkSeed secret input))
    let unresolvedSparse := sparsePhase phase input
    ((simulateQ oldGuard resolvedMarked).run
        ((initialCache, initialMetadata), (initialCounts, initialAborted)) =
      (simulateQ newGuard unresolvedSparse).run
        ((initialCache, initialMetadata), (initialCounts, initialAborted))) ∧
    ∀ request : Message,
      (oldGuard (.inr (.signingAttempt request))).run
          ((initialCache, initialMetadata), (initialCounts, initialAborted)) =
        (newGuard (.inr (.signingAttempt request))).run
          ((initialCache, initialMetadata), (initialCounts, initialAborted)) := by
  intro Cache handler pkSeed secret reserve trackRaw phase input privatePhase caps initialCounts
    initialAborted initialCache initialMetadata phaseReady charge oldHandler newHandler
    oldGuard newGuard resolvedMarked unresolvedSparse
  have blocks := resolve_native_blocks pkSeed secret
  have nativeTransfer (unresolved : DNative.Domain) (native : Native.Domain)
      (decode : Native.Range native → DNative.Range unresolved)
      (resolution : resolveNative pkSeed secret unresolved =
        decode <$> (liftM (Native.query native) : OracleComp Native (Native.Range native)))
      (fallback : deriveFallback pkSeed (.inl unresolved) =
        decode (mixedFallback pkSeed (.inl native))) :
      simulateQ (fun q => oldGuard (.inl q)) (resolveNative pkSeed secret unresolved) =
        newGuard (.inl unresolved) := by
    apply StateT.ext
    intro state
    rw [resolution, simulateQ_map, simulateQ_spec_query, StateT.run_map]
    symm
    refine QueryImpl.guarded_query_transport (Nat × Nat)
      (.inl unresolved) (.inl native) decode newHandler oldHandler
      (deriveFallback pkSeed) (mixedFallback pkSeed)
      (Sum.elim (fun _ : DNative.Domain => (0, 0)) (policy reserve pkSeed))
      (Sum.elim (fun _ : Native.Domain => (0, 0)) (policy reserve pkSeed))
      rfl ?_ fallback caps state.2.1 state.2.2 state.1
    intro physical
    dsimp only [newHandler, oldHandler]
    rw [QueryImpl.extendState_apply, QueryImpl.extendState_apply]
    simp only [eraseObsImpl_inl, QueryImpl.apply_compose, resolution, simulateQ_map,
      simulateQ_spec_query, StateT.run_map, aux, map_bind, bind_map_left, map_pure]; rfl
  have nativeRuns (unresolved : DNative.Domain) :
      simulateQ (fun q => oldGuard (.inl q)) (resolveNative pkSeed secret unresolved) =
        newGuard (.inl unresolved) := by
    rcases unresolved with ((n | typed) | (key | ⟨salt, message⟩)) | bytes
    · exact nativeTransfer _ (.inl n) id
        (by simpa only [id_map] using blocks.1 n) rfl
    · exact nativeTransfer _ (.inr (.inl typed)) id
        (by simpa only [id_map] using blocks.2.1 typed) rfl
    · exact nativeTransfer _ (.inr (.inl (.inl (.thash pkSeed key.1 [secret.1])))) id
        (by simpa only [id_map] using blocks.2.2.1 key) rfl
    · exact nativeTransfer _ (.inr (.inl (.inr ⟨secret.2, salt, message⟩))) id
        (by simpa only [id_map] using blocks.2.2.2.1 salt message) rfl
    · exact nativeTransfer _ (.inr (.inr bytes)) id
        (by simpa only [id_map] using blocks.2.2.2.2 bytes) rfl
  have markerRuns (event : Ev) : oldGuard (.inr event) = newGuard (.inr event) := by
    have step (physical : Cache × Meta) :
        (oldHandler (.inr event)).run physical = (newHandler (.inr event)).run physical := by
      dsimp only [oldHandler, newHandler]
      rw [QueryImpl.extendState_apply, QueryImpl.extendState_apply]
      simp only [eraseObsImpl_inr, StateT.run_pure, pure_bind, aux]
      cases event <;> rfl
    apply StateT.ext
    intro state
    simpa only [Prod.map_id, id_map] using
      (QueryImpl.guarded_query_transport (Nat × Nat)
        (.inr event) (.inr event) id oldHandler newHandler
        (mixedFallback pkSeed) (deriveFallback pkSeed)
        (Sum.elim (fun _ : Native.Domain => (0, 0)) (policy reserve pkSeed))
        (Sum.elim (fun _ : DNative.Domain => (0, 0)) (policy reserve pkSeed))
        (by simp only [Sum.elim_inr])
        (fun physical => by simpa only [Prod.map_id, id_map] using step physical)
        (by simp only [mixedFallback, deriveFallback, id_eq])
        caps state.2.1 state.2.2 state.1)
  have privateErase (derivation : DeriveQuery FIPS205.core)
      (privatePhase' : phase = .keygen ∨ phase = .signer)
      (ready : initialAborted = false → initialCounts ≤ caps → initialMetadata.2 = phase) :
      let query := (secretEncoding FIPS205.core (Equiv.refl _) pkSeed).enc secret derivation
      let event : Ev := .ambient phase (.inr (encode FIPS205.params query))
      let native : Native.Domain := .inr (.inl query)
      (simulateQ oldGuard (do
        let _ ← (liftM (Common.query (.inr event)) : OracleComp Common PUnit)
        (liftM (Common.query (.inl native)) :
          OracleComp Common (Native.Range native)))).run
            ((initialCache, initialMetadata), (initialCounts, initialAborted)) =
        (oldGuard (.inl native)).run
          ((initialCache, initialMetadata), (initialCounts, initialAborted)) := by
    intro query event native
    have certificate := SLHDSA.SHAKE128s.Bridge.SharedExperiment.Native.actual_private_marker_inert
      handler pkSeed secret reserve trackRaw derivation phase privatePhase' caps
      initialCounts initialAborted initialCache initialMetadata ready
    exact QueryImpl.guarded_inert_observation (Nat × Nat)
      oldHandler (mixedFallback pkSeed)
      (Sum.elim (fun _ : Native.Domain => (0, 0)) (policy reserve pkSeed))
      event native certificate.1 rfl caps initialCounts initialAborted
      (initialCache, initialMetadata) certificate.2
  constructor
  · rcases input with ((n | typed) | (key | ⟨salt, message⟩)) | bytes
    · have transfer := nativeRuns (.inl (.inl (.inl n)))
      rw [blocks.1 n, simulateQ_spec_query] at transfer
      dsimp only [resolvedMarked, unresolvedSparse]
      rw [blocks.1 n, SLHDSA.SHAKE128s.Bridge.SharedExperiment.Native.phase_query_normalforms.1,
        SLHDSA.SHAKE128s.Bridge.SharedExperiment.Native.phase_query_normalforms.2]
      simp only [nativeObservation, simulateQ_bind, simulateQ_spec_query]
      rw [markerRuns]
      exact congrArg (fun step => (newGuard (.inr (.ambient phase (.inl n))) >>= fun _ =>
        step).run ((initialCache, initialMetadata), (initialCounts, initialAborted))) transfer
    · have transfer := nativeRuns (.inl (.inl (.inr typed)))
      rw [blocks.2.1 typed, simulateQ_spec_query] at transfer
      dsimp only [resolvedMarked, unresolvedSparse]
      rw [blocks.2.1 typed,
        SLHDSA.SHAKE128s.Bridge.SharedExperiment.Native.phase_query_normalforms.1,
        SLHDSA.SHAKE128s.Bridge.SharedExperiment.Native.phase_query_normalforms.2]
      simp only [nativeObservation, simulateQ_bind, simulateQ_spec_query]
      rw [markerRuns]
      exact congrArg (fun step => (newGuard (.inr
        (.ambient phase (.inr (encode FIPS205.params typed)))) >>= fun _ => step).run
          ((initialCache, initialMetadata), (initialCounts, initialAborted))) transfer
    · have transfer := nativeRuns (.inl (.inr (.inl key)))
      rw [blocks.2.2.1 key, simulateQ_spec_query] at transfer
      have erase := privateErase (.inl key) (privatePhase rfl) (phaseReady rfl)
      dsimp only [resolvedMarked, unresolvedSparse]
      rw [blocks.2.2.1 key,
        SLHDSA.SHAKE128s.Bridge.SharedExperiment.Native.phase_query_normalforms.1,
        SLHDSA.SHAKE128s.Bridge.SharedExperiment.Native.phase_query_normalforms.2]
      simp only [nativeObservation, simulateQ_spec_query]
      exact erase.trans (congrArg (fun step => step.run
        ((initialCache, initialMetadata), (initialCounts, initialAborted))) transfer)
    · have transfer := nativeRuns (.inl (.inr (.inr (salt, message))))
      rw [blocks.2.2.2.1 salt message, simulateQ_spec_query] at transfer
      have erase := privateErase (.inr (salt, message)) (privatePhase rfl) (phaseReady rfl)
      dsimp only [resolvedMarked, unresolvedSparse]
      rw [blocks.2.2.2.1 salt message,
        SLHDSA.SHAKE128s.Bridge.SharedExperiment.Native.phase_query_normalforms.1,
        SLHDSA.SHAKE128s.Bridge.SharedExperiment.Native.phase_query_normalforms.2]
      simp only [nativeObservation, simulateQ_spec_query]
      exact erase.trans (congrArg (fun step => step.run
        ((initialCache, initialMetadata), (initialCounts, initialAborted))) transfer)
    · have transfer := nativeRuns (.inr bytes)
      rw [blocks.2.2.2.2 bytes, simulateQ_spec_query] at transfer
      dsimp only [resolvedMarked, unresolvedSparse]
      rw [blocks.2.2.2.2 bytes,
        SLHDSA.SHAKE128s.Bridge.SharedExperiment.Native.phase_query_normalforms.1,
        SLHDSA.SHAKE128s.Bridge.SharedExperiment.Native.phase_query_normalforms.2]
      simp only [nativeObservation, simulateQ_bind, simulateQ_spec_query]
      rw [markerRuns]
      exact congrArg (fun step => (newGuard (.inr (.ambient phase (.inr bytes))) >>= fun _ =>
        step).run ((initialCache, initialMetadata), (initialCounts, initialAborted))) transfer
  · intro request
    exact congrArg (fun step => step.run
      ((initialCache, initialMetadata), (initialCounts, initialAborted)))
      (markerRuns (.signingAttempt request))

end SLHDSA.SHAKE128s.Bridge.SharedExperiment.Native

end

section

open SLHDSA.SHAKE128s.Bridge.SharedExperiment.Guarded
open OracleComp OracleSpec SignatureAlg
open SLHDSA SLHDSA.Security SLHDSA.SHAKE128s
namespace SLHDSA.SHAKE128s.Bridge.SharedExperiment.Native

/-- The current phase matters only on an admitted source prefix. -/
private def Ready {Cache : Type} (caps : Nat × Nat) (phase : SigningView.Phase)
    (state : (Cache × Meta) × Paid) : Prop :=
  state.2.2 = false → state.2.1 ≤ caps → state.1.2.2 = phase

/-- Native steps do not change passive metadata, including on a warm or stopped prefix. -/
private theorem native_preserves_ready {Cache : Type}
    (handler : QueryImpl DNative (StateT Cache ProbComp))
    (pkSeed : FIPS205.core.PkSeed) (reserve trackRaw : Bool)
    (caps : Nat × Nat) (phase : SigningView.Phase) (input : DNative.Domain) :
    let charge := metadataCost trackRaw pkSeed
    let interpreted := (eraseObsImpl (Ev := Ev) handler).extendState (aux charge)
    let guarded := QueryImpl.guardQueryBudget caps
      (Sum.elim (fun _ : DNative.Domain => (0, 0)) (policy reserve pkSeed))
      interpreted (deriveFallback pkSeed)
    ∀ state, Ready caps phase state →
      ∀ result ∈ support ((guarded (.inl input)).run state), Ready caps phase result.2 := by
  intro charge interpreted guarded state ready result member
  rcases state with ⟨⟨cache, metadata⟩, counts, flag⟩
  cases flag with
  | true =>
    simp only [guarded, QueryImpl.guardQueryBudget, StateT.run_mk, ite_true,
      support_pure, Set.mem_singleton_iff] at member
    subst result
    simp [Ready]
  | false =>
    have zeroCost : counts + ((0, 0) : Nat × Nat) = counts := by
      cases counts
      rfl
    by_cases fits : counts ≤ caps
    · simp only [guarded, QueryImpl.guardQueryBudget, StateT.run_mk, Sum.elim_inl,
        Bool.false_eq_true, ite_false, zeroCost, fits, ite_true, support_map] at member
      obtain ⟨inner, innerMember, rfl⟩ := member
      dsimp only [interpreted] at innerMember
      rw [QueryImpl.extendState_apply, eraseObsImpl_inl, mem_support_bind_iff] at innerMember
      obtain ⟨answer, _answerMember, member⟩ := innerMember
      simp only [aux, support_pure, Set.mem_singleton_iff] at member
      subst inner
      exact ready
    · simp only [guarded, QueryImpl.guardQueryBudget, StateT.run_mk, Sum.elim_inl,
        Bool.false_eq_true, ite_false, zeroCost, fits, support_pure,
        Set.mem_singleton_iff] at member
      subst result
      simp [Ready]

/-- Any admitted marker sets its declared phase, while a rejected marker stops the guard. -/
private theorem marker_establishes_ready {Cache : Type}
    (handler : QueryImpl DNative (StateT Cache ProbComp))
    (pkSeed : FIPS205.core.PkSeed) (reserve trackRaw : Bool)
    (caps : Nat × Nat) (phase : SigningView.Phase) (event : Ev)
    (setsPhase : ∀ metadata : Meta,
      (aux (spec := DNative) (metadataCost trackRaw pkSeed) (.inr event)
        (PUnit.unit : PUnit) PUnit.unit PUnit.unit metadata).2 = phase) :
    let charge := metadataCost trackRaw pkSeed
    let interpreted := (eraseObsImpl (Ev := Ev) handler).extendState (aux charge)
    let guarded := QueryImpl.guardQueryBudget caps
      (Sum.elim (fun _ : DNative.Domain => (0, 0)) (policy reserve pkSeed))
      interpreted (deriveFallback pkSeed)
    ∀ state, ∀ result ∈ support ((guarded (.inr event)).run state),
      Ready caps phase result.2 := by
  intro charge interpreted guarded state result member
  rcases state with ⟨⟨cache, metadata⟩, counts, flag⟩
  cases flag with
  | true =>
    simp only [guarded, QueryImpl.guardQueryBudget, StateT.run_mk, ite_true,
      support_pure, Set.mem_singleton_iff] at member
    subst result
    simp [Ready]
  | false =>
    by_cases fits : counts + policy reserve pkSeed event ≤ caps
    · simp only [guarded, QueryImpl.guardQueryBudget, StateT.run_mk, Sum.elim_inr,
        Bool.false_eq_true, ite_false, fits, ite_true] at member
      dsimp only [interpreted] at member
      rw [QueryImpl.extendState_apply, eraseObsImpl_inr] at member
      simp only [StateT.run_pure, pure_bind] at member
      subst result
      intro _ _
      exact setsPhase metadata
    · simp only [guarded, QueryImpl.guardQueryBudget, StateT.run_mk, Sum.elim_inr,
        Bool.false_eq_true, ite_false, fits, support_pure,
        Set.mem_singleton_iff] at member
      subst result
      simp [Ready]

/-- A sparse phase block preserves the exact local readiness needed by private derivations. -/
private theorem sparse_preserves_ready {Cache : Type}
    (handler : QueryImpl DNative (StateT Cache ProbComp))
    (pkSeed : FIPS205.core.PkSeed) (reserve trackRaw : Bool)
    (caps : Nat × Nat) (phase : SigningView.Phase) :
    let interpreted := (eraseObsImpl (Ev := Ev) handler).extendState
      (aux (metadataCost trackRaw pkSeed))
    let guarded := QueryImpl.guardQueryBudget caps
      (Sum.elim (fun _ : DNative.Domain => (0, 0)) (policy reserve pkSeed))
      interpreted (deriveFallback pkSeed)
    QueryImpl.PreservesInv (guarded ∘ₛ sparsePhase phase) (Ready caps phase) := by
  intro interpreted guarded input state ready result member
  rw [QueryImpl.apply_compose, phase_query_normalforms.2 phase input] at member
  cases observed : nativeObservation input with
  | none =>
    simp only [observed, simulateQ_spec_query] at member
    exact native_preserves_ready handler pkSeed reserve trackRaw caps phase input
      state ready result member
  | some label =>
    simp only [observed, simulateQ_bind, simulateQ_spec_query, StateT.run_bind,
      mem_support_bind_iff] at member
    obtain ⟨afterMarker, markerMember, nativeMember⟩ := member
    have established := marker_establishes_ready handler pkSeed reserve trackRaw caps
      phase (.ambient phase label) (fun _ => rfl) state afterMarker markerMember
    exact native_preserves_ready handler pkSeed reserve trackRaw caps phase input
      afterMarker.2 established result nativeMember

/-- Whole honest phases commute with guarded resolution at every structurally ready state. -/
theorem guarded_phase_block {Cache α : Type}
    (handler : QueryImpl Native (StateT Cache ProbComp))
    (pkSeed : FIPS205.core.PkSeed) (secret : Secret) (reserve trackRaw : Bool)
    (caps : Nat × Nat) (phase : SigningView.Phase)
    (privatePhase : phase = .keygen ∨ phase = .signer)
    (body : OracleComp DNative α)
    (state : (Cache × Meta) × Paid)
    (ready : state.2.2 = false → state.2.1 ≤ caps → state.1.2.2 = phase) :
    let charge := metadataCost trackRaw pkSeed
    let oldHandler := (eraseObsImpl (Ev := Ev) handler).extendState (aux charge)
    let newHandler :=
      (eraseObsImpl (Ev := Ev) (handler ∘ₛ resolveNative pkSeed secret)).extendState (aux charge)
    let oldGuard := QueryImpl.guardQueryBudget caps
      (Sum.elim (fun _ : Native.Domain => (0, 0)) (policy reserve pkSeed))
      oldHandler (mixedFallback pkSeed)
    let newGuard := QueryImpl.guardQueryBudget caps
      (Sum.elim (fun _ : DNative.Domain => (0, 0)) (policy reserve pkSeed))
      newHandler (deriveFallback pkSeed)
    (simulateQ oldGuard (simulateQ resolvedProjection
      (simulateQ (SigningView.Events.phaseImpl Native Message phase)
        (simulateQ (resolveNative pkSeed secret) body)))).run state =
      (simulateQ newGuard (simulateQ (sparsePhase phase) body)).run state := by
  intro charge oldHandler newHandler oldGuard newGuard
  let left := ((oldGuard ∘ₛ resolvedProjection) ∘ₛ
    SigningView.Events.phaseImpl Native Message phase) ∘ₛ resolveNative pkSeed secret
  let right := newGuard ∘ₛ sparsePhase phase
  have preserves : QueryImpl.PreservesInv right (Ready caps phase) :=
    sparse_preserves_ready (handler ∘ₛ resolveNative pkSeed secret)
      pkSeed reserve trackRaw caps phase
  have step (input : DNative.Domain) (s : (Cache × Meta) × Paid)
      (ready : Ready caps phase s) :
      Prod.map id id <$> (right input).run s = (left input).run s := by
    have square := (guarded_phase_query_square handler pkSeed secret reserve trackRaw phase
      input (fun _ => privatePhase) caps s.2.1 s.2.2 s.1.1 s.1.2
      (fun _ => ready)).1
    simpa only [left, right, QueryImpl.apply_compose, QueryImpl.simulateQ_compose,
      Prod.map_id, id_map] using square.symm
  have whole := map_run_simulateQ_eq_of_query_map_eq_inv'
    right left (Ready caps phase) id preserves step body state ready
  simpa only [left, right, QueryImpl.simulateQ_compose, Prod.map_id, id_map, id_eq] using
    whole.symm

/-- Callback entry establishes signer readiness even for a rejected request. -/
theorem signing_attempt_ready {Cache : Type}
    (handler : QueryImpl DNative (StateT Cache ProbComp))
    (pkSeed : FIPS205.core.PkSeed) (reserve trackRaw : Bool)
    (caps : Nat × Nat) (request : Message) (state : (Cache × Meta) × Paid) :
    let interpreted := (eraseObsImpl (Ev := Ev) handler).extendState
      (aux (metadataCost trackRaw pkSeed))
    let guarded := QueryImpl.guardQueryBudget caps
      (Sum.elim (fun _ : DNative.Domain => (0, 0)) (policy reserve pkSeed))
      interpreted (deriveFallback pkSeed)
    ∀ result ∈ support ((guarded (.inr (.signingAttempt request))).run state),
      result.2.2.2 = false → result.2.2.1 ≤ caps → result.2.1.2.2 = .signer :=
  marker_establishes_ready handler pkSeed reserve trackRaw caps .signer
    (.signingAttempt request) (fun _ => rfl) state

/-- Public-hash computations transport from every incoming phase, including a pure verifier. -/
theorem guarded_public_phase_block {Cache α : Type}
    (handler : QueryImpl Native (StateT Cache ProbComp))
    (pkSeed : FIPS205.core.PkSeed) (secret : Secret) (reserve trackRaw : Bool)
    (caps : Nat × Nat) (phase : SigningView.Phase)
    (body : OracleComp (publicHashSpec FIPS205.core) α)
    (state : (Cache × Meta) × Paid) :
    let publicLift := QueryImpl.ofLift (publicHashSpec FIPS205.core) (OracleComp DNative)
    let charge := metadataCost trackRaw pkSeed
    let oldHandler := (eraseObsImpl (Ev := Ev) handler).extendState (aux charge)
    let newHandler :=
      (eraseObsImpl (Ev := Ev) (handler ∘ₛ resolveNative pkSeed secret)).extendState (aux charge)
    let oldGuard := QueryImpl.guardQueryBudget caps
      (Sum.elim (fun _ : Native.Domain => (0, 0)) (policy reserve pkSeed))
      oldHandler (mixedFallback pkSeed)
    let newGuard := QueryImpl.guardQueryBudget caps
      (Sum.elim (fun _ : DNative.Domain => (0, 0)) (policy reserve pkSeed))
      newHandler (deriveFallback pkSeed)
    (simulateQ oldGuard (simulateQ resolvedProjection
      (simulateQ (SigningView.Events.phaseImpl Native Message phase)
        (simulateQ (resolveNative pkSeed secret) (simulateQ publicLift body))))).run state =
      (simulateQ newGuard
        (simulateQ (sparsePhase phase) (simulateQ publicLift body))).run state := by
  intro publicLift charge oldHandler newHandler oldGuard newGuard
  let left := (((oldGuard ∘ₛ resolvedProjection) ∘ₛ
    SigningView.Events.phaseImpl Native Message phase) ∘ₛ resolveNative pkSeed secret) ∘ₛ
      publicLift
  let right := (newGuard ∘ₛ sparsePhase phase) ∘ₛ publicLift
  have publicQuery (input : (publicHashSpec FIPS205.core).Domain) :
      publicLift input =
        (liftM (DNative.query (.inl (.inl (.inr (.inl input))))) :
          OracleComp DNative ((publicHashSpec FIPS205.core).Range input)) := by
    dsimp only [publicLift]
    rw [QueryImpl.ofLift_apply]
    cases input <;> rfl
  have step (input : (publicHashSpec FIPS205.core).Domain)
      (s : (Cache × Meta) × Paid) :
      Prod.map id id <$> (right input).run s = (left input).run s := by
    have square := (guarded_phase_query_square handler pkSeed secret reserve trackRaw phase
      (.inl (.inl (.inr (.inl input))))
      (by simp [nativeObservation]) caps s.2.1 s.2.2 s.1.1 s.1.2
      (by simp [nativeObservation])).1
    simpa only [left, right, QueryImpl.apply_compose, publicQuery, simulateQ_spec_query,
      QueryImpl.simulateQ_compose, Prod.map_id, id_map] using square.symm
  have whole := map_run_simulateQ_eq_of_query_map_eq right left id step body state
  simpa only [left, right, QueryImpl.simulateQ_compose, Prod.map_id, id_map, id_eq] using
    whole.symm

end SLHDSA.SHAKE128s.Bridge.SharedExperiment.Native

end

section

open SLHDSA.SHAKE128s.Bridge.SharedExperiment.Guarded
open OracleComp OracleSpec SignatureAlg
open SLHDSA SLHDSA.Security SLHDSA.SHAKE128s
namespace SLHDSA.SHAKE128s.Bridge.SharedExperiment.Native

/-- The genuine initial marked uniform prefix preserves its complete guarded state. -/
theorem uniform_prefix_forwarding :
  ∀ (pkSeed : FIPS205.core.PkSeed) (reserve trackRaw : Bool) (caps : Nat × Nat)
    (initialTyped : H.QueryCache) (initialPrivate : Raw.QueryCache),
    let E := encoding pkSeed
    let charge := metadataCost trackRaw pkSeed
    let actualHandler :=
      (eraseObsImpl (Ev := Ev) E.typedImpl).extendState (aux charge)
    let actualGuard := QueryImpl.guardQueryBudget caps
      (Sum.elim (fun _ : Native.Domain => (0, 0)) (policy reserve pkSeed))
      actualHandler (mixedFallback pkSeed)
    let initial : (TypedPV × Meta) × Paid :=
      (((initialTyped, initialPrivate), (0, .keygen)), ((0, 0), false))
    let secretPrefix := simulateQ resolvedProjection
      (simulateQ (SigningView.Events.phaseImpl Native Message .keygen)
        (liftM ($ᵗ Secret) : OracleComp Native Secret))
    (simulateQ actualGuard secretPrefix).run initial =
      (fun secret => (secret, initial)) <$> ($ᵗ Secret : ProbComp Secret) := by
  intro pkSeed reserve trackRaw caps initialTyped initialPrivate E charge actualHandler
    actualGuard initial secretPrefix
  let S := (TypedPV × Meta) × Paid
  let nativeHandler : QueryImpl Native (StateT S ProbComp) :=
    (actualGuard ∘ₛ resolvedProjection) ∘ₛ SigningView.Events.phaseImpl Native Message .keygen
  let uniformHandler : QueryImpl unifSpec (StateT S ProbComp) :=
    fun n => nativeHandler (.inl n)
  let reference : QueryImpl unifSpec (StateT S ProbComp) :=
    (QueryImpl.id' unifSpec).liftTarget (StateT S ProbComp)
  have keygenFree (native : R.Domain) :
      policy reserve pkSeed (.ambient .keygen native) = (0, 0) := by
    simp [policy, originalPolicy, reserveExtra, Game.Counted.sourcePolicy,
      Game.Counted.sourceKind]
  have metadataFree (n : Nat) : charge (.ambient .keygen (.inl n)) = 0 := by
    simp [charge, metadataCost, selectedRaw]
  have markerStep (n : Nat) :
      (actualHandler (.inr (.ambient .keygen (.inl n)))).run
        ((initialTyped, initialPrivate), (0, .keygen)) =
      pure (PUnit.unit, ((initialTyped, initialPrivate), (0, .keygen))) := by
    dsimp only [actualHandler]
    rw [QueryImpl.extendState_apply, eraseObsImpl_inr, StateT.run_pure, pure_bind]
    simp only [aux, metadataFree, Nat.add_zero]
  have nativeStep (n : Nat) :
      (actualHandler (.inl (.inl n))).run
        ((initialTyped, initialPrivate), (0, .keygen)) =
      (fun u => (u, ((initialTyped, initialPrivate), (0, .keygen)))) <$>
        (unifSpec.query n : ProbComp (Fin (n + 1))) := by
    dsimp only [actualHandler]
    rw [QueryImpl.extendState_apply, eraseObsImpl_inl, E.typedImpl_inl_run]
    simp only [OracleSpec.romImpl, QueryImpl.add_apply_inl, unifFwdImpl,
      QueryImpl.liftTarget_apply_run, QueryImpl.ofLift_apply, aux,
      bind_pure_comp, Functor.map_map]
  have fits : ((0, 0) : Nat × Nat) ≤ caps := zero_le
  have guardedNative (n : Nat) :
      (actualGuard (.inl (.inl n))).run initial =
      (fun u => (u, initial)) <$> (unifSpec.query n : ProbComp (Fin (n + 1))) := by
    dsimp only [actualGuard]
    simp only [QueryImpl.guardQueryBudget, StateT.run_mk, initial, Sum.elim_inl,
      Bool.false_eq_true, ite_false, Prod.mk_add_mk, Nat.zero_add, fits, ite_true]
    rw [nativeStep]
    simp only [Functor.map_map]
  have step (n : Nat) :
      (uniformHandler n).run initial =
        (fun u => (u, initial)) <$> (unifSpec.query n : ProbComp (Fin (n + 1))) := by
    have erase := QueryImpl.guarded_inert_observation (Nat × Nat) actualHandler (mixedFallback
      pkSeed)
      (Sum.elim (fun _ : Native.Domain => (0, 0)) (policy reserve pkSeed))
      (.ambient .keygen (.inl n)) (.inl n) (keygenFree (.inl n)) rfl caps
      (0, 0) false ((initialTyped, initialPrivate), (0, .keygen))
      (fun _ _ => markerStep n)
    dsimp only [uniformHandler, nativeHandler]
    rw [QueryImpl.apply_compose, QueryImpl.simulateQ_compose]
    have normal := phase_query_normalforms.1 .keygen (.inl n)
    simp only [simulateQ_spec_query] at normal
    rw [normal]
    exact erase.trans (guardedNative n)
  have liftStep (n : Nat) :
      simulateQ nativeHandler
        (liftM (liftM (unifSpec.query n) : ProbComp (Fin (n + 1))) :
          OracleComp Native (Fin (n + 1))) = uniformHandler n := by
    rw [← OracleComp.liftComp_eq_liftM, OracleComp.liftComp_liftM_query,
      OracleComp.liftM_eq_liftM_liftM, OracleQuery.liftM_add_left_query,
      simulateQ_spec_query]
  have prefixRun : simulateQ actualGuard secretPrefix =
      simulateQ uniformHandler ($ᵗ Secret : ProbComp Secret) := by
    dsimp only [secretPrefix]
    rw [← QueryImpl.simulateQ_compose, ← QueryImpl.simulateQ_compose]
    exact QueryImpl.simulateQ_liftM_eq_of_query nativeHandler uniformHandler liftStep _
  rw [prefixRun]
  have invariant (n : unifSpec.Domain) (state : S) (hs : state = initial) :
      ∀ result ∈ support ((uniformHandler n).run state), result.2 = initial := by
    subst state
    intro result hr
    rw [step, support_map] at hr
    rcases hr with ⟨u, _, rfl⟩
    rfl
  have query (n : unifSpec.Domain) (state : S) (hs : state = initial) :
      Prod.map id id <$> (uniformHandler n).run state = (reference n).run (id state) := by
    subst state
    simp only [Prod.map_id, id_map, id_eq, step, reference, QueryImpl.liftTarget_apply_run,
      QueryImpl.id'_apply]
  have whole := map_run_simulateQ_eq_of_query_map_eq_inv'
    uniformHandler reference (fun state => state = initial) id invariant query
    ($ᵗ Secret : ProbComp Secret) initial rfl
  simpa only [Prod.map_id, id_map, reference, simulateQ_liftTarget, simulateQ_id',
    StateT.run_monadLift, monadLift_self, id_eq, bind_pure_comp] using whole

end SLHDSA.SHAKE128s.Bridge.SharedExperiment.Native

end

section

open SLHDSA.SHAKE128s.Bridge.SharedExperiment.Guarded
open OracleComp OracleSpec SignatureAlg
open SLHDSA SLHDSA.Security SLHDSA.SHAKE128s
open SLHDSA.SHAKE128s.Bridge.SharedExperiment
namespace SLHDSA.SHAKE128s.Bridge.SharedExperiment.Native

/-- The derivation scheme resolved at an actual seed, with the original strict wire interface. -/
private noncomputable def resolvedView (pkSeed : FIPS205.core.PkSeed) (secret : Secret) :
    SigningView (OracleComp Native) Message PK PK (List Byte) (Option (List Byte)) :=
  SigningView.rejectingEncoding
    (((deriveScheme FIPS205.core (fun pk => pure pk.pkSeed) pkSeed).map
      (simulateQ' ((secretEncoding FIPS205.core (Equiv.refl _) pkSeed).deriveImpl secret))).map
        (simulateQ' (liftTypedImpl (hs := H) (ext := Raw))))
    (fun request => (External.encodePureMessage request.context request.message).toOption)
    (SLHDSA.encodeSignature FIPS205.params
      (SLHDSA.Concrete.shakeWireCodec FIPS205.params.params))
    (fun wire => (SLHDSA.decodeSignature FIPS205.params
      (SLHDSA.Concrete.shakeWireCodec FIPS205.params.params) wire).toOption)

/-- Resolution commutes with the public lift of each internal component. -/
private theorem resolved_components (pkSeed : FIPS205.core.PkSeed) (secret : Secret) :
    (resolvedView pkSeed secret).keygen =
      simulateQ (resolveNative pkSeed secret) (unresolvedView pkSeed).keygen ∧
    (∀ pk sk request, (resolvedView pkSeed secret).sign pk sk request =
      simulateQ (resolveNative pkSeed secret) ((unresolvedView pkSeed).sign pk sk request)) ∧
    ∀ pk request signature, (resolvedView pkSeed secret).verify pk request signature =
      simulateQ (resolveNative pkSeed secret)
        ((unresolvedView pkSeed).verify pk request signature) := by
  have component {α : Type} (body : OracleComp (deriveSpec FIPS205.core) α) :
      simulateQ (resolveNative pkSeed secret)
        (simulateQ (QueryImpl.ofLift (deriveSpec FIPS205.core) (OracleComp DNative)) body) =
      simulateQ (liftTypedImpl (hs := H) (ext := Raw))
        (simulateQ ((secretEncoding FIPS205.core (Equiv.refl _) pkSeed).deriveImpl secret)
          body) := by
    let combined := (liftTypedImpl (hs := H) (ext := Raw)) ∘ₛ
      (secretEncoding FIPS205.core (Equiv.refl _) pkSeed).deriveImpl secret
    have injected (input : (deriveSpec FIPS205.core).Domain) :
        QueryImpl.ofLift (deriveSpec FIPS205.core) (OracleComp DNative) input =
          (liftM (DNative.query (.inl input)) :
            OracleComp DNative ((deriveSpec FIPS205.core).Range input)) := by
      rw [QueryImpl.ofLift_apply]
      rcases input with (n | typed) | derivation <;> rfl
    have query (input : (deriveSpec FIPS205.core).Domain) :
        simulateQ (resolveNative pkSeed secret)
          (QueryImpl.ofLift (deriveSpec FIPS205.core) (OracleComp DNative) input) =
        combined input := by
      rw [injected, simulateQ_spec_query]
      rfl
    exact (QueryImpl.simulateQ_simulateQ_eq_of_apply query body).trans
      (QueryImpl.simulateQ_compose (liftTypedImpl (hs := H) (ext := Raw))
        ((secretEncoding FIPS205.core (Equiv.refl _) pkSeed).deriveImpl secret) body)
  constructor
  · simpa only [resolvedView, unresolvedView, SigningView.rejectingEncoding_keygen,
      map_keygen] using (component _).symm
  constructor
  · intro pk sk request
    simp only [resolvedView, unresolvedView, SigningView.rejectingEncoding_sign, map_sign]
    cases (External.encodePureMessage request.context request.message).toOption with
    | none => simp
    | some message => simp only [simulateQ_map, component]
  · intro pk request signature
    simp only [resolvedView, unresolvedView, SigningView.rejectingEncoding_verify, map_verify]
    cases (External.encodePureMessage request.context request.message).toOption with
    | none => simp
    | some message =>
      cases (SLHDSA.decodeSignature FIPS205.params
        (SLHDSA.Concrete.shakeWireCodec FIPS205.params.params) signature).toOption with
      | none => simp
      | some decoded => exact (component _).symm

/-- The strict unresolved verifier is a public-hash computation, even when it rejects purely. -/
private theorem unresolved_verify_public (pkSeed : FIPS205.core.PkSeed)
    (pk : PK) (request : Message) (signature : List Byte) :
    ∃ body : OracleComp (publicHashSpec FIPS205.core) Bool,
      (unresolvedView pkSeed).verify pk request signature =
        simulateQ (QueryImpl.ofLift (publicHashSpec FIPS205.core) (OracleComp DNative)) body := by
  simp only [unresolvedView, SigningView.rejectingEncoding_verify, map_verify]
  cases (External.encodePureMessage request.context request.message).toOption with
  | none => exact ⟨pure false, rfl⟩
  | some message =>
    cases (SLHDSA.decodeSignature FIPS205.params
      (SLHDSA.Concrete.shakeWireCodec FIPS205.params.params) signature).toOption with
    | none => exact ⟨pure false, rfl⟩
    | some decoded =>
      refine ⟨GeneralScheme.verifyInternalM FIPS205.params FIPS205.core
        message decoded pk, ?_⟩
      simp only [deriveScheme]
      let liftHom : HasQuery.QueryHom (publicHashSpec FIPS205.core)
          (OracleComp (deriveSpec FIPS205.core)) (OracleComp DNative) :=
        { toMonadHom := simulateQ'
            (QueryImpl.ofLift (deriveSpec FIPS205.core) (OracleComp DNative))
          map_query' := fun input => by cases input <;> rfl }
      have first := GeneralScheme.verifyInternalM_natural FIPS205.params FIPS205.core
        liftHom message decoded pk
      have second := GeneralScheme.verifyInternalM_natural FIPS205.params FIPS205.core
        (HasQuery.QueryHom.ofSimulateQ (spec := publicHashSpec FIPS205.core)
          (m := OracleComp DNative)) message decoded pk
      exact first.trans second.symm

/-- Sparse observations commute with the phase wrapper on every unresolved native program. -/
private theorem sparse_phase {α : Type} (phase : SigningView.Phase)
    (body : OracleComp DNative α) :
    simulateQ sparseProjection
      (simulateQ (SigningView.Events.phaseImpl DNative Message phase) body) =
      simulateQ (sparsePhase phase) body := by
  apply QueryImpl.simulateQ_simulateQ_eq_of_apply
  intro input
  simp only [SigningView.Events.phaseImpl, QueryImpl.preInsert_apply,
    SigningView.Events.emit, monadLift_self, simulateQ_bind, simulateQ_spec_query,
    sparseProjection, QueryImpl.add_eq_hAdd, QueryImpl.add_apply_inl,
    QueryImpl.add_apply_inr, QueryImpl.ofLift_apply]
  have forward : (liftM (DNative.query input) : OracleComp DCommon (DNative.Range input)) =
      (liftM (DCommon.query (.inl input)) : OracleComp DCommon (DNative.Range input)) := by
    rw [OracleComp.liftM_eq_liftM_liftM]
    rcases input with ((n | typed) | derivation) | bytes <;> rfl
  simp only [sparsePhase, QueryImpl.preInsert_apply, monadLift_self, forward]
  cases nativeObservation input <;> rfl

/-- Actual signing callbacks transport from every incoming state and retain rejection replies. -/
private theorem guarded_signing_callback {Cache : Type}
    (handler : QueryImpl Native (StateT Cache ProbComp))
    (pkSeed : FIPS205.core.PkSeed) (secret : Secret) (reserve trackRaw : Bool)
    (caps : Nat × Nat) (pk sk : PK) (request : Message)
    (state : (Cache × Meta) × Paid) :
    let oldHandler := (eraseObsImpl (Ev := Ev) handler).extendState
      (aux (metadataCost trackRaw pkSeed))
    let newHandler :=
      (eraseObsImpl (Ev := Ev) (handler ∘ₛ resolveNative pkSeed secret)).extendState
        (aux (metadataCost trackRaw pkSeed))
    let oldGuard := QueryImpl.guardQueryBudget caps
      (Sum.elim (fun _ : Native.Domain => (0, 0)) (policy reserve pkSeed))
      oldHandler (mixedFallback pkSeed)
    let newGuard := QueryImpl.guardQueryBudget caps
      (Sum.elim (fun _ : DNative.Domain => (0, 0)) (policy reserve pkSeed))
      newHandler (deriveFallback pkSeed)
    (simulateQ oldGuard (simulateQ resolvedProjection
      ((SigningView.Events.viewWithEvents (resolvedView pkSeed secret)).sign pk sk request))).run
        state =
      (simulateQ newGuard (simulateQ sparseProjection
        ((SigningView.Events.viewWithEvents (unresolvedView pkSeed)).sign pk sk request))).run
          state := by
  intro oldHandler newHandler oldGuard newGuard
  have marker := (guarded_phase_query_square handler pkSeed secret reserve trackRaw .signer
    (.inl (.inl (.inl 0))) (by simp [nativeObservation]) caps state.2.1 state.2.2
    state.1.1 state.1.2 (by simp [nativeObservation])).2 request
  have oldEmit : simulateQ resolvedProjection
      (SigningView.Events.emit Native Message (.signingAttempt request)) =
        (liftM (Common.query (.inr (.signingAttempt request))) : OracleComp Common PUnit) := by
    simp [SigningView.Events.emit, resolvedProjection, QueryImpl.add_eq_hAdd, rawEvent]
  have newEmit : simulateQ sparseProjection
      (SigningView.Events.emit DNative Message (.signingAttempt request)) =
        (liftM (DCommon.query (.inr (.signingAttempt request))) : OracleComp DCommon PUnit) := by
    simp [SigningView.Events.emit, sparseProjection, QueryImpl.add_eq_hAdd]
  simp only [SigningView.Events.viewWithEvents, simulateQ_bind, StateT.run_bind,
    oldEmit, newEmit, simulateQ_spec_query]
  rw [marker]
  apply OracleComp.bind_congr_of_forall_mem_support
  intro afterMarker member
  have ready := signing_attempt_ready (handler ∘ₛ resolveNative pkSeed secret)
    pkSeed reserve trackRaw caps request state afterMarker member
  rw [(resolved_components pkSeed secret).2.1]
  have phase := guarded_phase_block handler pkSeed secret reserve trackRaw caps .signer
    (Or.inr rfl) ((unresolvedView pkSeed).sign pk sk request) afterMarker.2 ready
  rw [sparse_phase]
  exact phase

/-- Public raw-client ports use no private derivation. -/
private def rawLiftD : QueryImpl R (OracleComp DNative) :=
  QueryImpl.add
    (fun n => liftM (DNative.query (.inl (.inl (.inl n)))))
    (fun bytes => liftM (DNative.query (.inr bytes)))

/-- The existing logged external client transports as a whole, including each optional reply. -/
private theorem guarded_external_client {Cache : Type}
    (handler : QueryImpl Native (StateT Cache ProbComp))
    (pkSeed : FIPS205.core.PkSeed) (secret : Secret) (reserve trackRaw : Bool)
    (caps : Nat × Nat) (adv : Game.Adversary FIPS205.Answer PK)
    (pk sk : PK) (state : (Cache × Meta) × Paid) :
    let oldHandler := (eraseObsImpl (Ev := Ev) handler).extendState
      (aux (metadataCost trackRaw pkSeed))
    let newHandler :=
      (eraseObsImpl (Ev := Ev) (handler ∘ₛ resolveNative pkSeed secret)).extendState
        (aux (metadataCost trackRaw pkSeed))
    let oldGuard := QueryImpl.guardQueryBudget caps
      (Sum.elim (fun _ : Native.Domain => (0, 0)) (policy reserve pkSeed))
      oldHandler (mixedFallback pkSeed)
    let newGuard := QueryImpl.guardQueryBudget caps
      (Sum.elim (fun _ : DNative.Domain => (0, 0)) (policy reserve pkSeed))
      newHandler (deriveFallback pkSeed)
    let oldMarked := SigningView.Events.viewWithEvents (resolvedView pkSeed secret)
    let newMarked := SigningView.Events.viewWithEvents (unresolvedView pkSeed)
    (simulateQ oldGuard (simulateQ resolvedProjection
      (oldMarked.runWithSigningOracle pk sk
        (SigningView.Events.mainWithEvents (rawMain adv) pk)))).run state =
      (simulateQ newGuard (simulateQ sparseProjection
        (newMarked.runWithSigningOracle pk sk
          (SigningView.Events.mainWithEvents (rawMainD adv) pk)))).run state := by
  intro oldHandler newHandler oldGuard newGuard oldMarked newMarked
  let Log := QueryLog Sign
  let State := (Cache × Meta) × Paid
  let oldLogged : QueryImpl (R + Sign)
      (WriterT Log (OracleComp (SigningView.Events.Spec Native Message))) :=
    QueryImpl.add
      (((SigningView.Events.phaseImpl Native Message .adversary) ∘ₛ
        (liftRawImpl (hs := H))).liftTarget
          (WriterT Log (OracleComp (SigningView.Events.Spec Native Message))))
      (oldMarked.signingOracle pk sk)
  let newLogged : QueryImpl (R + Sign)
      (WriterT Log (OracleComp (SigningView.Events.Spec DNative Message))) :=
    QueryImpl.add
      (((SigningView.Events.phaseImpl DNative Message .adversary) ∘ₛ rawLiftD).liftTarget
        (WriterT Log (OracleComp (SigningView.Events.Spec DNative Message))))
      (newMarked.signingOracle pk sk)
  have nativeToClient (input : Native.Domain) :
      (liftM (Native.query input) : OracleComp (Native + Sign) (Native.Range input)) =
        (liftM ((Native + Sign).query (.inl input)) :
          OracleComp (Native + Sign) (Native.Range input)) := by
    rw [OracleComp.liftM_eq_liftM_liftM]
    rcases input with n | (typed | bytes) <;> rfl
  have oldCollapse : oldMarked.runWithSigningOracle pk sk
      (SigningView.Events.mainWithEvents (rawMain adv) pk) =
      (simulateQ oldLogged (Game.Counted.externalMain adv pk)).run := by
    simp only [SigningView.runWithSigningOracle, SigningView.Events.mainWithEvents,
      rawMain, ← QueryImpl.simulateQ_compose]
    congr 2
    funext input
    rcases input with (n | bytes) | request
    all_goals apply WriterT.ext
    all_goals
      simp [oldLogged, QueryImpl.apply_compose, QueryImpl.add_eq_hAdd,
        SigningView.Events.phaseImpl, SigningView.Events.emit, QueryImpl.passthrough_add,
        liftRawImpl, monadLift_self, nativeToClient, seqRight_eq_bind]
    all_goals rfl
  have newCollapse : newMarked.runWithSigningOracle pk sk
      (SigningView.Events.mainWithEvents (rawMainD adv) pk) =
      (simulateQ newLogged (Game.Counted.externalMain adv pk)).run := by
    simp only [SigningView.runWithSigningOracle, SigningView.Events.mainWithEvents,
      rawMainD, ← QueryImpl.simulateQ_compose]
    congr 2
    funext input
    rcases input with (n | bytes) | request
    all_goals apply WriterT.ext
    all_goals
      simp [newLogged, rawLiftD, QueryImpl.apply_compose, QueryImpl.add_eq_hAdd,
        SigningView.Events.phaseImpl, SigningView.Events.emit, QueryImpl.passthrough_add,
        monadLift_self, seqRight_eq_bind]
    all_goals rfl
  let oldGame : QueryImpl (R + Sign) (WriterT Log (StateT State ProbComp)) :=
    fun input => WriterT.mk (simulateQ (oldGuard ∘ₛ resolvedProjection) (oldLogged input).run)
  let newGame : QueryImpl (R + Sign) (WriterT Log (StateT State ProbComp)) :=
    fun input => WriterT.mk (simulateQ (newGuard ∘ₛ sparseProjection) (newLogged input).run)
  have gameEq : oldGame = newGame := by
    funext input
    apply WriterT.ext
    funext s
    change (oldGame input).run.run s = (newGame input).run.run s
    rcases input with (n | bytes) | request
    · have square := (guarded_phase_query_square handler pkSeed secret reserve trackRaw
        .adversary (.inl (.inl (.inl n))) (by simp [nativeObservation])
        caps s.2.1 s.2.2 s.1.1 s.1.2 (by simp [nativeObservation])).1
      have resolved := (resolve_native_blocks pkSeed secret).1 n
      rw [resolved] at square
      simp only [simulateQ_spec_query] at square
      have sparseQuery := sparse_phase .adversary
        (liftM (DNative.query (.inl (.inl (.inl n)))) : OracleComp DNative (Fin (n + 1)))
      simp only [simulateQ_spec_query] at sparseQuery
      have mapped := congrArg
        (fun action => (fun result => ((result.1, ([] : Log)), result.2)) <$> action) square
      simp only [oldGame, newGame, oldLogged, newLogged, rawLiftD,
        QueryImpl.add_eq_hAdd, QueryImpl.add_apply_inl, QueryImpl.liftTarget_apply,
        WriterT.run_monadLift', WriterT.run_mk, QueryImpl.apply_compose,
        QueryImpl.simulateQ_compose,
        simulateQ_map, StateT.run_map, liftRawImpl, simulateQ_HasQuery_query,
        simulateQ_spec_query, sparseQuery]
      convert mapped using 1 <;> rfl
    · have square := (guarded_phase_query_square handler pkSeed secret reserve trackRaw
        .adversary (.inr bytes) (by simp [nativeObservation])
        caps s.2.1 s.2.2 s.1.1 s.1.2 (by simp [nativeObservation])).1
      have resolved := (resolve_native_blocks pkSeed secret).2.2.2.2 bytes
      rw [resolved] at square
      simp only [simulateQ_spec_query] at square
      have sparseQuery := sparse_phase .adversary
        (liftM (DNative.query (.inr bytes)) : OracleComp DNative FIPS205.Answer)
      simp only [simulateQ_spec_query] at sparseQuery
      have mapped := congrArg
        (fun action => (fun result => ((result.1, ([] : Log)), result.2)) <$> action) square
      simp only [oldGame, newGame, oldLogged, newLogged, rawLiftD,
        QueryImpl.add_eq_hAdd, QueryImpl.add_apply_inl, QueryImpl.add_apply_inr,
        QueryImpl.liftTarget_apply, WriterT.run_monadLift', WriterT.run_mk, QueryImpl.apply_compose,
        QueryImpl.simulateQ_compose, simulateQ_map, StateT.run_map, liftRawImpl,
        simulateQ_HasQuery_query, simulateQ_spec_query, sparseQuery]
      convert mapped using 1 <;> rfl
    · have callback := guarded_signing_callback handler pkSeed secret reserve trackRaw
        caps pk sk request s
      have mapped := congrArg
        (fun action : ProbComp (Option (List Byte) × State) =>
          (fun result => ((result.1, ([⟨request, result.1⟩] : Log)), result.2)) <$>
            action) callback
      simp only [oldGame, newGame, oldLogged, newLogged,
        QueryImpl.add_eq_hAdd, QueryImpl.add_apply_inr, WriterT.run_mk,
        SigningView.signingOracle]
      rw [QueryImpl.run_withLogging_apply, QueryImpl.run_withLogging_apply]
      simpa only [QueryImpl.simulateQ_compose, simulateQ_bind, simulateQ_pure,
        StateT.run_bind, StateT.run_pure, bind_pure_comp, simulateQ_map, StateT.run_map,
        oldMarked, newMarked] using mapped
  rw [oldCollapse, newCollapse]
  have oldFold := simulateQ_WriterT_compose oldLogged (oldGuard ∘ₛ resolvedProjection) oldGame
    (fun _ => rfl) (Game.Counted.externalMain adv pk)
  have newFold := simulateQ_WriterT_compose newLogged (newGuard ∘ₛ sparseProjection) newGame
    (fun _ => rfl) (Game.Counted.externalMain adv pk)
  rw [← QueryImpl.simulateQ_compose, ← QueryImpl.simulateQ_compose]
  rw [oldFold, newFold, gameEq]

/-- Complete resolved and sparse experiments agree under the same source guard. -/
private theorem guarded_resolved_full {Cache : Type}
    (handler : QueryImpl Native (StateT Cache ProbComp))
    (pkSeed : FIPS205.core.PkSeed) (secret : Secret) (reserve trackRaw : Bool)
    (caps : Nat × Nat) (adv : Game.Adversary FIPS205.Answer PK)
    (state : (Cache × Meta) × Paid)
    (ready : state.2.2 = false → state.2.1 ≤ caps → state.1.2.2 = .keygen) :
    let oldHandler := (eraseObsImpl (Ev := Ev) handler).extendState
      (aux (metadataCost trackRaw pkSeed))
    let newHandler :=
      (eraseObsImpl (Ev := Ev) (handler ∘ₛ resolveNative pkSeed secret)).extendState
        (aux (metadataCost trackRaw pkSeed))
    let oldGuard := QueryImpl.guardQueryBudget caps
      (Sum.elim (fun _ : Native.Domain => (0, 0)) (policy reserve pkSeed))
      oldHandler (mixedFallback pkSeed)
    let newGuard := QueryImpl.guardQueryBudget caps
      (Sum.elim (fun _ : DNative.Domain => (0, 0)) (policy reserve pkSeed))
      newHandler (deriveFallback pkSeed)
    (simulateQ oldGuard (simulateQ resolvedProjection
      (SigningView.Events.fullExperiment (resolvedView pkSeed secret) (rawMain adv)))).run
        state =
      (simulateQ newGuard (fixedSource pkSeed adv)).run state := by
  intro oldHandler newHandler oldGuard newGuard
  have keygen :
      (simulateQ oldGuard (simulateQ resolvedProjection
        (simulateQ (SigningView.Events.phaseImpl Native Message .keygen)
          (resolvedView pkSeed secret).keygen))).run state =
      (simulateQ newGuard (simulateQ sparseProjection
        (simulateQ (SigningView.Events.phaseImpl DNative Message .keygen)
          (unresolvedView pkSeed).keygen))).run state := by
    rw [(resolved_components pkSeed secret).1, sparse_phase]
    exact guarded_phase_block handler pkSeed secret reserve trackRaw caps .keygen
      (Or.inl rfl) (unresolvedView pkSeed).keygen state ready
  have verify (pk : PK) (request : Message) (signature : List Byte)
      (s : (Cache × Meta) × Paid) :
      (simulateQ oldGuard (simulateQ resolvedProjection
        (simulateQ (SigningView.Events.phaseImpl Native Message .verification)
          ((resolvedView pkSeed secret).verify pk request signature)))).run s =
      (simulateQ newGuard (simulateQ sparseProjection
        (simulateQ (SigningView.Events.phaseImpl DNative Message .verification)
          ((unresolvedView pkSeed).verify pk request signature)))).run s := by
    rw [(resolved_components pkSeed secret).2.2, sparse_phase]
    obtain ⟨body, publicOnly⟩ := unresolved_verify_public pkSeed pk request signature
    rw [publicOnly]
    exact guarded_public_phase_block handler pkSeed secret reserve trackRaw caps
      .verification body s
  simp only [fixedSource, SigningView.Events.fullExperiment, simulateQ_bind, simulateQ_pure,
    StateT.run_bind, StateT.run_pure]
  change ((simulateQ oldGuard (simulateQ resolvedProjection
    (simulateQ (SigningView.Events.phaseImpl Native Message .keygen)
      (resolvedView pkSeed secret).keygen))).run state >>= _) =
    ((simulateQ newGuard (simulateQ sparseProjection
      (simulateQ (SigningView.Events.phaseImpl DNative Message .keygen)
        (unresolvedView pkSeed).keygen))).run state >>= _)
  rw [keygen]
  apply bind_congr
  rintro ⟨keys, afterKeygen⟩
  rw [guarded_external_client handler pkSeed secret reserve trackRaw caps adv
    keys.1 keys.2 afterKeygen]
  apply bind_congr
  rintro ⟨⟨forgery, log⟩, afterClient⟩
  dsimp only [SigningView.Events.viewWithEvents]
  rw [verify keys.1 forgery.1 forgery.2 afterClient]

/-- The real marked source factors through one secret-free, already guarded program. -/
theorem actual_guarded_fixed_source_factor :
  ∀ (pkSeed : FIPS205.core.PkSeed)
    (adv : Game.Adversary FIPS205.Answer PK)
    (reserve trackRaw : Bool) (caps : Nat × Nat)
    (initialTyped : H.QueryCache) (initialPrivate : Raw.QueryCache),
    let E := encoding pkSeed
    let charge := metadataCost trackRaw pkSeed
    let actualSource := simulateQ resolvedProjection
      (SigningView.Events.fullExperiment (realView pkSeed) (rawMain adv))
    let actualHandler :=
      (eraseObsImpl (Ev := Ev) E.typedImpl).extendState (aux charge)
    let actualGuard := QueryImpl.guardQueryBudget caps
      (Sum.elim (fun _ : Native.Domain => (0, 0)) (policy reserve pkSeed))
      actualHandler (mixedFallback pkSeed)
    letI : MonadLiftT (OracleComp DCommon) (StateT PUnit (OracleComp DCommon)) :=
      ⟨fun action => StateT.lift action⟩
    let fixedForwarder : QueryImpl DCommon (StateT PUnit (OracleComp DCommon)) :=
      (QueryImpl.id' DCommon).liftTarget (StateT PUnit (OracleComp DCommon))
    let fixedGuarded : OracleComp DCommon (Guarded.Full × (PUnit × Paid)) :=
      (simulateQ (QueryImpl.guardQueryBudget caps
        (Sum.elim (fun _ : DNative.Domain => (0, 0)) (policy reserve pkSeed))
        fixedForwarder (deriveFallback pkSeed)) (fixedSource pkSeed adv)).run
          (PUnit.unit, ((0, 0), false))
    let actualRun : ProbComp (SecretFull × ((TypedPV × Meta) × Paid)) :=
      (simulateQ actualGuard actualSource).run
        (((initialTyped, initialPrivate), (0, .keygen)), ((0, 0), false))
    let factoredRun : ProbComp (SecretFull × ((TypedPV × Meta) × Paid)) := do
      let secret ← ($ᵗ Secret : ProbComp Secret)
      let unresolvedHandler :=
        (eraseObsImpl (Ev := Ev) (E.typedImpl ∘ₛ resolveNative pkSeed secret)).extendState
          (aux charge)
      let result ← (simulateQ unresolvedHandler fixedGuarded).run
        ((initialTyped, initialPrivate), (0, .keygen))
      let keys := result.1.1.1
      let rebuilt : SecretFull :=
        ((keys.1, fillSecretKey FIPS205.core secret keys.2), result.1.1.2)
      return (rebuilt, (result.2, result.1.2.2))
    actualRun = factoredRun ∧
      let clip : SecretFull × ((TypedPV × Meta) × Paid) →
          Option SecretFull × ((TypedPV × Meta) × Paid) := fun result =>
        (if result.2.2.2 then none else some result.1, result.2)
      clip <$> actualRun = clip <$> factoredRun := by
  intro pkSeed adv reserve trackRaw caps initialTyped initialPrivate E charge actualSource
    actualHandler actualGuard fixedForwarder fixedGuarded actualRun factoredRun
  let initial : (TypedPV × Meta) × Paid :=
    (((initialTyped, initialPrivate), (0, .keygen)), ((0, 0), false))
  let seedPrefix := simulateQ resolvedProjection
    (simulateQ (SigningView.Events.phaseImpl Native Message .keygen)
      (liftM ($ᵗ Secret) : OracleComp Native Secret))
  let rebuild (secret : Secret) (result : Guarded.Full) : SecretFull :=
    ((result.1.1, fillSecretKey FIPS205.core secret result.1.2), result.2)
  have reconstructed := (romScheme_partial_key_reconstruction FIPS205.core Raw
    (Equiv.refl _) (fun pk => pure pk.pkSeed) pkSeed
    (SLHDSA.Concrete.shakeWireCodec FIPS205.params.params)
    (fun request : Message =>
      (External.encodePureMessage request.context request.message).toOption)).2
      (rawMain adv)
  have sourceEq : actualSource = (do
      let secret ← seedPrefix
      rebuild secret <$> simulateQ resolvedProjection
        (SigningView.Events.fullExperiment (resolvedView pkSeed secret) (rawMain adv))) := by
    have source := congrArg (simulateQ resolvedProjection) reconstructed.1
    simpa only [actualSource, realView, SLHDSA.SigningView.fromInternalPure,
      resolvedView, seedPrefix, rebuild, simulateQ_bind, simulateQ_map] using source
  have prefixForwarding := uniform_prefix_forwarding pkSeed reserve trackRaw caps
    initialTyped initialPrivate
  have exactEquality : actualRun = factoredRun := by
    dsimp only [actualRun]
    rw [sourceEq, simulateQ_bind, StateT.run_bind]
    change ((simulateQ actualGuard seedPrefix).run initial >>= _) = _
    rw [prefixForwarding, bind_map_left]
    apply bind_congr
    intro secret
    have whole := guarded_resolved_full E.typedImpl pkSeed secret reserve trackRaw
      caps adv initial (fun _ _ => rfl)
    let unresolvedHandler :=
      (eraseObsImpl (Ev := Ev) (E.typedImpl ∘ₛ resolveNative pkSeed secret)).extendState
        (aux charge)
    have interpret := QueryImpl.map_run_simulateQ_guardQueryBudget_free_eq caps
      (Sum.elim (fun _ : DNative.Domain => (0, 0)) (policy reserve pkSeed))
      unresolvedHandler (deriveFallback pkSeed) (fixedSource pkSeed adv)
      ((initialTyped, initialPrivate), (0, .keygen)) (0, 0) false
    simp only [simulateQ_map, StateT.run_map]
    rw [whole]
    rw [← interpret]
    simp only [fixedGuarded, fixedForwarder, rebuild, map_eq_bind_pure_comp,
      Function.comp_def, bind_assoc, pure_bind]
    rfl
  refine ⟨exactEquality, ?_⟩
  exact congrArg (fun computation =>
    (fun result : SecretFull × ((TypedPV × Meta) × Paid) =>
      (if result.2.2.2 then none else some result.1, result.2)) <$> computation) exactEquality

end SLHDSA.SHAKE128s.Bridge.SharedExperiment.Native

end

open OracleComp OracleSpec SignatureAlg
open SLHDSA SLHDSA.Security SLHDSA.SHAKE128s
open SLHDSA.SHAKE128s.Bridge.SharedExperiment
open SLHDSA.SHAKE128s.Bridge.SharedExperiment.Guarded
open MeasureTheory
open scoped ENNReal

namespace SLHDSA.SHAKE128s.Bridge.SharedExperiment.Native

/-- Resolving the secret before or after routing a guarded run gives the same output, budget,
metadata and caches. -/
theorem resolved_guarded_router_observer_square :
  ∀ (s : FIPS205.core.PkSeed) (adv : Game.Adversary FIPS205.Answer PK)
    (reserve trackRaw : Bool) (caps : Nat × Nat) (secret : Secret),
    letI : MonadLiftT (OracleComp DCommon) (StateT PUnit (OracleComp DCommon)) :=
      ⟨fun action => StateT.lift action⟩
    let forwarder : QueryImpl DCommon (StateT PUnit (OracleComp DCommon)) :=
      (QueryImpl.id' DCommon).liftTarget (StateT PUnit (OracleComp DCommon))
    let fixedGuarded := (simulateQ (QueryImpl.guardQueryBudget caps
      (Sum.elim (fun _ : DNative.Domain => (0, 0)) (policy reserve s))
      forwarder (deriveFallback s))
      (SLHDSA.SHAKE128s.Bridge.SharedExperiment.Guarded.fixedSource s adv)).run
        (PUnit.unit, ((0, 0), false))
    let freeProgram :=
      (simulateQ (SLHDSA.SHAKE128s.Bridge.SharedExperiment.Guarded.observeD s trackRaw)
        ((simulateQ (SLHDSA.SHAKE128s.Bridge.SharedExperiment.Guarded.routeD s)
          fixedGuarded).run ∅)).run (0, .keygen)
    let resolved := (simulateQ
      ((eraseObsImpl (Ev := Ev) ((encoding s).typedImpl ∘ₛ resolveNative s secret)).extendState
        (aux (metadataCost trackRaw s))) fixedGuarded).run
          ((∅, ∅), (0, .keygen))
    let reshape := fun result : (Guarded.Full × (PUnit × Paid)) × (TypedPV × Meta) =>
      (((result.1, result.2.1.2), result.2.2), result.2.1.1)
    (reshape <$> resolved) =
      (simulateQ ((secretEncoding FIPS205.core (Equiv.refl _) s).realImpl secret)
        freeProgram).run ∅ := by
  intro s adv reserve trackRaw caps secret
  let _ : MonadLiftT (OracleComp.{0, 0, 0} DCommon)
      (StateT PUnit.{1} (OracleComp.{0, 0, 0} DCommon)) :=
    ⟨fun action => StateT.lift action⟩
  let forwarder : QueryImpl DCommon (StateT PUnit (OracleComp DCommon)) :=
    (QueryImpl.id' DCommon).liftTarget (StateT PUnit (OracleComp DCommon))
  let program : OracleComp DCommon (Guarded.Full × (PUnit × Paid)) :=
    (simulateQ (QueryImpl.guardQueryBudget caps
      (Sum.elim (fun _ : DNative.Domain => (0, 0)) (policy reserve s))
      forwarder (deriveFallback s))
      (SLHDSA.SHAKE128s.Bridge.SharedExperiment.Guarded.fixedSource s adv)).run
        (PUnit.unit, ((0, 0), false))
  let E := encoding s
  let privateEncoding := secretEncoding FIPS205.core (Equiv.refl _) s
  let real := privateEncoding.realImpl secret
  let observer :=
    SLHDSA.SHAKE128s.Bridge.SharedExperiment.Guarded.observeD s trackRaw
  let router := SLHDSA.SHAKE128s.Bridge.SharedExperiment.Guarded.routeD s
  let resolved : QueryImpl DCommon (StateT (TypedPV × Meta) ProbComp) :=
    (eraseObsImpl (Ev := Ev) (E.typedImpl ∘ₛ resolveNative s secret)).extendState
      (aux (metadataCost trackRaw s))
  let middle : QueryImpl (deriveSpec FIPS205.core + O)
      (StateT (Meta × H.QueryCache) ProbComp) :=
    (real.mapStateTBase observer).flattenStateT
  let whole : QueryImpl DCommon
      (StateT (Raw.QueryCache × (Meta × H.QueryCache)) ProbComp) :=
    (middle.mapStateTBase router).flattenStateT
  let permute : TypedPV × Meta → Raw.QueryCache × (Meta × H.QueryCache) :=
    fun state => (state.1.2, (state.2, state.1.1))
  let publicLift : QueryImpl (unifSpec + H) (OracleComp (deriveSpec FIPS205.core)) :=
    H.withDerivationsLift (DeriveQuery FIPS205.core) FIPS205.core.Y
  let inclusion : QueryImpl (unifSpec + H)
      (OracleComp (deriveSpec FIPS205.core + O)) :=
    QueryImpl.ofLift (unifSpec + H) (OracleComp (deriveSpec FIPS205.core + O))
  have observePublic {alpha : Type} (oa : OracleComp (unifSpec + H) alpha) :
      simulateQ observer (simulateQ inclusion oa) =
        liftM (simulateQ publicLift oa) := by
    rw [← simulateQ_liftTarget]
    apply QueryImpl.simulateQ_simulateQ_eq_of_apply
    intro input
    have inclusionEq : inclusion input =
        (liftM ((deriveSpec FIPS205.core + O).query (.inl (.inl input))) :
          OracleComp (deriveSpec FIPS205.core + O) ((unifSpec + H).Range input)) := by
      rcases input with sample | (typed | prf) <;> rfl
    rw [inclusionEq, simulateQ_spec_query]
    simp only [observer,
      SLHDSA.SHAKE128s.Bridge.SharedExperiment.Guarded.observeD, QueryImpl.add,
      QueryImpl.liftTarget_apply, QueryImpl.id'_apply]
    rfl
  have realPublic {alpha : Type} (oa : OracleComp (unifSpec + H) alpha) :
      simulateQ real (simulateQ publicLift oa) = simulateQ H.romImpl oa := by
    change simulateQ (H.romImpl ∘ₛ privateEncoding.deriveImpl secret)
      (simulateQ publicLift oa) = _
    rw [QueryImpl.simulateQ_compose,
      ← QueryImpl.simulateQ_compose (privateEncoding.deriveImpl secret) publicLift]
    change simulateQ H.romImpl
      (simulateQ (privateEncoding.deriveImpl secret ∘ₛ
        H.withDerivationsLift (DeriveQuery FIPS205.core) FIPS205.core.Y) oa) = _
    rw [privateEncoding.deriveImpl_comp_withDerivationsLift, simulateQ_id']
  have middlePublic {alpha : Type} (oa : OracleComp (unifSpec + H) alpha)
      (metadata : Meta) (cache : H.QueryCache) :
      (simulateQ middle (simulateQ inclusion oa)).run (metadata, cache) =
        (fun out => (out.1, (metadata, out.2))) <$>
          (simulateQ H.romImpl oa).run cache := by
    have nested :
        (simulateQ real ((simulateQ observer (simulateQ inclusion oa)).run metadata)).run
          cache = (fun out => ((out.1, metadata), out.2)) <$>
            (simulateQ H.romImpl oa).run cache := by
      rw [observePublic]
      simp only [StateT.run_liftM,
           bind_pure_comp]
      simp only [simulateQ_map, StateT.run_map, realPublic]
    rw [simulateQ_mapStateTBase_run_eq_map_flattenStateT] at nested
    have mapped := congrArg (fun action =>
      (fun out : (alpha × Meta) × H.QueryCache =>
        (out.1.1, (out.1.2, out.2))) <$> action) nested
    simp only [Functor.map_map, Prod.eta] at mapped
    change id <$> (simulateQ middle (simulateQ inclusion oa)).run (metadata, cache) = _ at mapped
    simpa only [id_map] using mapped
  have nativeResolved (input : (deriveSpec FIPS205.core).Domain)
      (cache : H.QueryCache) (privateValues : Raw.QueryCache) :
      (simulateQ E.typedImpl (resolveNative s secret (.inl input))).run
        (cache, privateValues) =
      (fun out => (out.1, (out.2, privateValues))) <$> (real input).run cache := by
    change (simulateQ E.typedImpl
      (simulateQ (liftTypedImpl (hs := H) (ext := Raw))
        (privateEncoding.deriveImpl secret input))).run (cache, privateValues) = _
    rw [E.typedImpl_eq_handlerRouterImpl]
    simpa only [real, SecretEncoding.realImpl, QueryImpl.apply_compose] using
      simulateQ_handlerRouterImpl_simulateQ_liftTypedImpl_run H.romImpl E.tableRouter
        (privateEncoding.deriveImpl secret input) cache privateValues
  have step (input : DCommon.Domain) (state : TypedPV × Meta) :
      Prod.map id permute <$> (resolved input).run state =
        (whole input).run (permute state) := by
    rcases state with ⟨⟨cache, privateValues⟩, metadata⟩
    rcases input with (native | bytes) | event
    · simp only [resolved, QueryImpl.extendState_apply, eraseObsImpl_inl,
        QueryImpl.apply_compose, aux, nativeResolved, whole, middle, router, observer,
        SLHDSA.SHAKE128s.Bridge.SharedExperiment.Guarded.routeD,
        SLHDSA.SHAKE128s.Bridge.SharedExperiment.Guarded.observeD,
        QueryImpl.flattenStateT_mapStateTBase_apply_run,
        QueryImpl.add,  QueryImpl.liftTarget_apply, QueryImpl.id'_apply,
         simulateQ_map, simulateQ_spec_query,
        StateT.run_mk,  StateT.run_map,
        StateT.run_monadLift, bind_pure_comp,
        Functor.map_map,  Prod.map, permute,  id_eq]
      simp only [monadLift_self, simulateQ_spec_query]
      rfl
    · simp only [resolved, QueryImpl.extendState_apply, eraseObsImpl_inl,
        QueryImpl.apply_compose, resolveNative, QueryImpl.add,
        simulateQ_spec_query, E.typedImpl_eq_handlerRouterImpl,
        handlerRouterImpl, StateT.run_mk, aux, whole, router,
        SLHDSA.SHAKE128s.Bridge.SharedExperiment.Guarded.routeD,
        QueryImpl.flattenStateT_mapStateTBase_apply_run,
        QueryImpl.add,
        bind_pure_comp, Functor.map_map,  Prod.map, permute, id_eq]
      change _ = (fun y => (y.1.1, y.1.2, y.2)) <$>
        (simulateQ middle (simulateQ inclusion ((E.tableRouter bytes).run privateValues))).run
          (metadata, cache)
      rw [middlePublic]
      simp only [Functor.map_map]
    · cases event <;>
        simp only [resolved, QueryImpl.extendState_apply, eraseObsImpl_inr,
          aux, whole, middle, router, observer,
          SLHDSA.SHAKE128s.Bridge.SharedExperiment.Guarded.routeD,
          SLHDSA.SHAKE128s.Bridge.SharedExperiment.Guarded.observeD,
          SLHDSA.SHAKE128s.Bridge.SharedExperiment.Guarded.aux,
          QueryImpl.flattenStateT_mapStateTBase_apply_run,
          QueryImpl.add,  simulateQ_bind,
          simulateQ_spec_query, simulateQ_pure, StateT.run_mk, StateT.run_bind,
           StateT.run_pure, pure_bind, map_pure,
            Prod.map, permute,
          SLHDSA.SHAKE128s.Bridge.SharedExperiment.Guarded.metadataCost,
          metadataCost, SLHDSA.SHAKE128s.Bridge.SharedExperiment.Guarded.selectedRaw,
          selectedRaw, SLHDSA.SHAKE128s.Bridge.SharedExperiment.Guarded.encoding, encoding,
          ite_self, Nat.add_zero, id_eq]
  let repack := fun out : (Guarded.Full × (PUnit × Paid)) ×
      (Raw.QueryCache × (Meta × H.QueryCache)) =>
    (((out.1, out.2.1), out.2.2.1), out.2.2.2)
  have transport := map_run_simulateQ_eq_of_query_map_eq resolved whole permute step
    program ((∅, ∅), (0, .keygen))
  have mapped := congrArg (fun action => repack <$> action) transport
  have regroup :
      (simulateQ real
        ((simulateQ observer ((simulateQ router program).run ∅)).run
          (0, .keygen))).run ∅ =
      repack <$> (simulateQ whole program).run (∅, ((0, .keygen), ∅)) := by
    rw [simulateQ_mapStateTBase_run_eq_map_flattenStateT real observer,
      simulateQ_mapStateTBase_run_eq_map_flattenStateT middle router]
    simp only [repack, whole, middle, Functor.map_map]
  change (fun result : (Guarded.Full × (PUnit × Paid)) × (TypedPV × Meta) =>
      (((result.1, result.2.1.2), result.2.2), result.2.1.1)) <$>
      (simulateQ resolved program).run ((∅, ∅), (0, .keygen)) =
    (simulateQ real
      ((simulateQ observer ((simulateQ router program).run ∅)).run (0, .keygen))).run ∅
  rw [regroup]
  simpa only [repack, permute, Functor.map_map, Function.comp_def, Prod.map,
    id_eq, Prod.eta] using mapped

end SLHDSA.SHAKE128s.Bridge.SharedExperiment.Native
