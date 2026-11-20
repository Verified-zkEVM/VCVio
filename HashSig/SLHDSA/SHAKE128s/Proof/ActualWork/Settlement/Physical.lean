/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module

import HashSig.SLHDSA.SHAKE128s.Bridge.Encodings
import HashSig.SLHDSA.Security.Transport
import VCVio.OracleComp.QueryTracking.LoggingOracle.Core
import VCVio.OracleComp.QueryTracking.RandomOracle.Defer
import VCVio.OracleComp.SimSemantics.StateT.PreservesInv
import VCVio.OracleComp.SimSemantics.StateT.StateProjection
import VCVio.OracleComp.SimSemantics.StateT.StateSeparating
import VCVio.OracleComp.SimSemantics.WriterT.Core
import all HashSig.SLHDSA.SHAKE128s.Bridge.SharedExperiment.Pure
import all HashSig.SLHDSA.Security.CoverageRun
import all HashSig.SLHDSA.Security.NativeCounts
import all HashSig.SLHDSA.Security.NativeRelative
import all HashSig.SLHDSA.Security.SeedCoupling
import all VCVio.CryptoFoundations.SignatureAlg.CountedExperiment
import all VCVio.OracleComp.QueryTracking.RandomOracle.ClassIndexedTape
public import HashSig.SLHDSA.SHAKE128s.Proof.ActualWork.Transcript.ReplyLog
public import HashSig.SLHDSA.SHAKE128s.Proof.ActualWork.Price.WinningEvent
public import HashSig.SLHDSA.SHAKE128s.Proof.ActualWork.Coupling.Tapes
import all HashSig.SLHDSA.SHAKE128s.Proof.ActualWork.Coupling.KeySampler
import all HashSig.SLHDSA.SHAKE128s.Proof.ActualWork.Work.Counters
import all HashSig.SLHDSA.SHAKE128s.Proof.ActualWork.Coupling.Guarded
import all HashSig.SLHDSA.SHAKE128s.Proof.ActualWork.Transcript.DeferredLaw
import all HashSig.SLHDSA.SHAKE128s.Proof.ActualWork.Transcript.CacheOrigins
import all HashSig.SLHDSA.SHAKE128s.Proof.ActualWork.Transcript.KeyMarginal
import all HashSig.SLHDSA.SHAKE128s.Proof.ActualWork.Settlement.Support

/-!
# Recovering a winning FIPS output from the oracle cache

The final random-oracle cache replays key generation, accepted signing replies and
the verification of a winning forgery using the same secret.
-/

public section

section

open OracleComp OracleSpec SignatureAlg
open SLHDSA SLHDSA.Security SLHDSA.SHAKE128s
open SLHDSA.SHAKE128s.Bridge.SharedExperiment
open SLHDSA.SHAKE128s.Bridge.SharedExperiment.Guarded
open MeasureTheory
open SLHDSA.Security.CanonicalGames SLHDSA.DigestTransport
open scoped ENNReal

namespace SLHDSA.SHAKE128s.Bridge.SharedExperiment.Native
private theorem source_of_free_guard
    {ι α Cache C : Type} {spec : OracleSpec.{0, 0} ι}
    [AddMonoid C] [Preorder C] [CanonicallyOrderedAdd C] [DecidableLE C]
    (caps : C) (cost : spec.Domain → C) (h : QueryImpl spec (StateT Cache ProbComp))
    (fb : (i : spec.Domain) → spec.Range i) (p : OracleComp spec α) (initial : Cache)
    (r : (α × (PUnit × (C × Bool))) × Cache)
    (mem : r ∈ support ((simulateQ h
      ((simulateQ (QueryImpl.guardQueryBudget caps cost
        ((QueryImpl.id' spec).liftTarget (StateT PUnit (OracleComp spec))) fb) p).run
          (PUnit.unit, (0, false)))).run initial)) (ok : r.1.2.2.2 = false) :
    (r.1.1, r.2) ∈ support ((simulateQ h p).run initial) := by
  apply mem_support_source_of_guard_not_aborted caps cost h fb p initial
    (r.1.1, (r.2, r.1.2.2)) _ ok
  rw [← QueryImpl.map_run_simulateQ_guardQueryBudget_free_eq, support_map]
  exact ⟨r, mem, rfl⟩

private theorem erased_fixed_run {σ : Type} (s : FIPS205.core.PkSeed)
    (adv : Game.Adversary FIPS205.Answer PK)
    (real : QueryImpl DNative (StateT σ ProbComp)) :
  let view := unresolvedView s
  let full := do
    let keys ← view.keygen
    let (candidate, replies) ← view.runWithSigningOracle keys.1 keys.2 (rawMainD adv keys.1)
    let verified ← view.verify keys.1 candidate.1 candidate.2
    pure (keys, (⟨candidate, replies, verified⟩ : RawOutcome))
  simulateQ (eraseObsImpl (Ev := Ev) real) (fixedSource s adv) = simulateQ real full := by
  intro view full
  have sourceEvents : (eraseObsImpl (Ev := Ev) real) ∘ₛ sparseProjection =
      SigningView.Events.handlerWithEvents (Request := Message) real := by
    funext input
    cases input with
    | inl native =>
      have forward : (liftM (DNative.query native) : OracleComp DCommon (DNative.Range native)) =
          (liftM (DCommon.query (.inl native)) : OracleComp DCommon (DNative.Range native)) := by
        rw [OracleComp.liftM_eq_liftM_liftM]
        rcases native with ((n | typed) | derivation) | bytes <;> rfl
      simp [sparseProjection, QueryImpl.apply_compose, QueryImpl.add,
        SigningView.Events.handlerWithEvents, QueryImpl.ofLift_apply, forward, eraseObsImpl]
    | inr event =>
      cases event with
      | signingAttempt request => simp [sparseProjection, QueryImpl.apply_compose, eraseObsImpl,
          QueryImpl.add, SigningView.Events.handlerWithEvents]
      | ambient phase input =>
        cases ho : nativeObservation input <;>
          simp [sparseProjection, QueryImpl.apply_compose, eraseObsImpl, ho, QueryImpl.add,
            SigningView.Events.handlerWithEvents]
  rw [fixedSource, ← QueryImpl.simulateQ_compose, sourceEvents]
  dsimp only [full]
  rw [← erase_full_signing_events view (rawMainD adv)]
  symm
  apply QueryImpl.simulateQ_simulateQ_eq_of_apply
  intro input
  cases input <;> simp [SigningView.Events.handlerWithEvents]

private theorem terminal_public_replay {α : Type} (p : OracleComp (publicHashSpec FIPS205.core) α)
    (start : H.QueryCache) (r : α × H.QueryCache) (final : H.QueryCache)
    (mem : r ∈ support ((simulateQ H.romImpl (simulateQ (HasQuery.toQueryImpl
      (spec := publicHashSpec FIPS205.core) (m := OracleComp (unifSpec + H))) p)).run start))
    (mono : r.2 ≤ final) : simulateQ final.fst.toPartialImpl p = some r.1 :=
  QueryCache.simulateQ_toPartialImpl_mono (QueryCache.fst_mono mono) _
    (simulateQ_toPartialImpl_snd_fst_of_mem_support_run_romImpl p mem)

private theorem resolved_sign_replay (s : FIPS205.core.PkSeed) (secret : Secret) (pk : PK)
    (msg : List Byte) (sig : GeneralScheme.SignatureCore FIPS205.params FIPS205.core)
    (before after final : H.QueryCache) (hle : after ≤ final) (key : pk.pkSeed = s)
    (mem : (sig, after) ∈ support ((simulateQ
      ((secretEncoding FIPS205.core (Equiv.refl _) s).realImpl secret)
        ((deriveScheme FIPS205.core (fun k => pure k.pkSeed) s).sign pk pk msg)).run before)) :
    simulateQ final.fst.toPartialImpl
      (GeneralScheme.signInternalWithSecretRandomizerM FIPS205.core
        (oracleSecret FIPS205.core (Equiv.refl _) s secret.1)
        msg pk.pkSeed pk.pkRoot sig.randomness) = some sig := by
  classical
  let E := secretEncoding FIPS205.core (Equiv.refl _) s
  let provider {m : Type → Type} [Monad m] [HasQuery (publicHashSpec FIPS205.core) m] :
      Adrs → m FIPS205.core.Y := oracleSecret FIPS205.core (Equiv.refl _) s secret.1
  have signNatural (message : List Byte) (root R : FIPS205.core.Y) :
      simulateQ (E.deriveImpl secret)
        (GeneralScheme.signInternalWithSecretRandomizerM FIPS205.core
          (deriveSecret FIPS205.core) message s root R) =
      (GeneralScheme.signInternalWithSecretRandomizerM FIPS205.core provider message s root R :
        OracleComp (unifSpec + H) (GeneralScheme.SignatureCore FIPS205.params FIPS205.core)) :=
    GeneralScheme.signInternalWithSecretRandomizerM_natural FIPS205.core
      (deriveHom FIPS205.core (Equiv.refl _) s secret) (deriveSecret FIPS205.core) provider
      (fun _ ha => simulateQ_deriveImpl_deriveSecret FIPS205.core (Equiv.refl _) s secret ha)
      message s root R
  change (sig, after) ∈ support ((simulateQ (E.realImpl secret) _).run before) at mem
  rw [SecretEncoding.realImpl, QueryImpl.simulateQ_compose] at mem
  simp only [deriveScheme, simulateQ_bind, SecretEncoding.simulateQ_deriveImpl_liftM,
    key, signNatural] at mem
  simp only [StateT.run_bind, mem_support_bind_iff] at mem
  obtain ⟨_, _, randomizer, _, tail⟩ := mem
  have lifted := signInternalWithSecretRandomizerM_oracleSecret_eq_ofSimulateQ
    (core := FIPS205.core) (m := OracleComp (unifSpec + H)) (Equiv.refl _) s secret.1
    msg pk.pkRoot randomizer.1
  have upper := (congrArg (fun p : OracleComp (unifSpec + H) _ =>
    (sig, after) ∈ support ((simulateQ H.romImpl p).run randomizer.2)) lifted).mp tail
  have read := terminal_public_replay _ _ (sig, after) final upper hle
  obtain ⟨same, _⟩ := components_of_simulateQ_toPartialImpl_signInternalWithSecretRandomizerM
    FIPS205.core _ _ _ _ _ _ read
  rw [← same] at read
  simpa only [key] using read

private theorem resolved_verify_replay (s : FIPS205.core.PkSeed) (secret : Secret) (pk : PK)
    (msg : List Byte) (sig : GeneralScheme.SignatureCore FIPS205.params FIPS205.core)
    (before final : H.QueryCache) (valid : Bool)
    (mem : (valid, final) ∈ support ((simulateQ
      ((secretEncoding FIPS205.core (Equiv.refl _) s).realImpl secret)
        ((deriveScheme FIPS205.core (fun k => pure k.pkSeed) s).verify pk msg sig)).run before)) :
    simulateQ final.fst.toPartialImpl
      (GeneralScheme.verifyInternalM FIPS205.params FIPS205.core msg sig pk) = some valid := by
  rw [SecretEncoding.realImpl, QueryImpl.simulateQ_compose] at mem
  let pub := HasQuery.QueryHom.ofSimulateQ
    (spec := publicHashSpec FIPS205.core) (m := OracleComp (unifSpec + H))
  have up := GeneralScheme.verifyInternalM_natural FIPS205.params FIPS205.core pub msg sig pk
  have resolve := GeneralScheme.verifyInternalM_natural FIPS205.params FIPS205.core
    (deriveHom FIPS205.core (Equiv.refl _) s secret) msg sig pk
  let p : OracleComp (publicHashSpec FIPS205.core) Bool :=
    GeneralScheme.verifyInternalM FIPS205.params FIPS205.core msg sig pk
  have lifted : simulateQ ((secretEncoding FIPS205.core (Equiv.refl _) s).deriveImpl secret)
      ((deriveScheme FIPS205.core (fun k => pure k.pkSeed) s).verify pk msg sig) =
      simulateQ (HasQuery.toQueryImpl (spec := publicHashSpec FIPS205.core)
        (m := OracleComp (unifSpec + H))) p := resolve.trans up.symm
  have direct := (congrArg (fun a : OracleComp (unifSpec + H) Bool =>
    (valid, final) ∈ support ((simulateQ H.romImpl a).run before)) lifted).mp mem
  exact terminal_public_replay p before (valid, final) final direct le_rfl

set_option maxHeartbeats 360000 in
-- Replay traverses the three consecutive phases of a supported fixed-key execution.
private theorem ordinary_cache_replays
    (s : FIPS205.core.PkSeed) (adv : Game.Adversary FIPS205.Answer PK) (secret : Secret)
    (retained : Guarded.Full) (values : H.QueryCache) (raw : Raw.QueryCache)
    (world : ProbComp (Guarded.Full × TypedPV))
    (world_eq : ((simulateQ
      (eraseObsImpl (Ev := Ev) ((encoding s).typedImpl ∘ₛ resolveNative s secret))
      (fixedSource s adv)).run (∅, ∅)) = world)
    (physical : (retained, (values, raw)) ∈ support world)
    (hwins : SigningView.Wins id retained.2) :
      let full := retained
      let cache := values.fst
      let typedLog := Settlement.typedLog full.2.rawLog
      let provider := oracleSecret FIPS205.core (Equiv.refl _) s secret.1
      ∃ (message : List Byte)
        (signature : GeneralScheme.SignatureCore FIPS205.params FIPS205.core),
        (External.encodePureMessage full.2.forgery.1.context
          full.2.forgery.1.message).toOption = some message ∧
        (SLHDSA.decodeSignature FIPS205.params
          (SLHDSA.Concrete.shakeWireCodec FIPS205.params.params)
          full.2.forgery.2).toOption = some signature ∧
        full.1.1.pkSeed = s ∧
        simulateQ cache.toPartialImpl
          (GeneralScheme.keygenInternalWithSecretM FIPS205.core provider full.1.1.pkSeed) =
            some full.1.1.pkRoot ∧
        (∀ entry ∈ typedLog, simulateQ cache.toPartialImpl
          (GeneralScheme.signInternalWithSecretRandomizerM FIPS205.core provider
            entry.1 full.1.1.pkSeed full.1.1.pkRoot entry.2.randomness) = some entry.2) ∧
        simulateQ cache.toPartialImpl
          (GeneralScheme.verifyInternalM FIPS205.params FIPS205.core
            message signature full.1.1) = some true := by
  classical
  dsimp only
  let E := secretEncoding FIPS205.core (Equiv.refl _) s
  let provider {m : Type → Type} [Monad m] [HasQuery (publicHashSpec FIPS205.core) m] :
      Adrs → m FIPS205.core.Y := oracleSecret FIPS205.core (Equiv.refl _) s secret.1
  let real := (encoding s).typedImpl ∘ₛ resolveNative s secret
  let view := unresolvedView s
  rw [← world_eq, erased_fixed_run] at physical
  let embedD := QueryImpl.ofLift (deriveSpec FIPS205.core) (OracleComp DNative)
  have componentRun {alpha : Type} (program : OracleComp (deriveSpec FIPS205.core) alpha)
      (cache : H.QueryCache) (privateCache : Raw.QueryCache) :
      (simulateQ real (simulateQ embedD program)).run (cache, privateCache) =
      (fun result => (result.1, (result.2, privateCache))) <$>
        (simulateQ (E.realImpl secret) program).run cache := by
    have resolve : simulateQ (resolveNative s secret) (simulateQ embedD program) =
        simulateQ (liftTypedImpl (hs := H) (ext := Raw))
          (simulateQ (E.deriveImpl secret) program) := by
      let combined := liftTypedImpl (hs := H) (ext := Raw) ∘ₛ E.deriveImpl secret
      have injected (input : (deriveSpec FIPS205.core).Domain) :
          embedD input = (liftM (DNative.query (.inl input)) :
            OracleComp DNative ((deriveSpec FIPS205.core).Range input)) := by
        rw [show embedD = QueryImpl.ofLift _ _ from rfl, QueryImpl.ofLift_apply]
        rcases input with (n | typed) | derivation <;> rfl
      have query (input : (deriveSpec FIPS205.core).Domain) :
          simulateQ (resolveNative s secret) (embedD input) = combined input := by
        rw [injected, simulateQ_spec_query]
        rfl
      exact (QueryImpl.simulateQ_simulateQ_eq_of_apply query program).trans
        (QueryImpl.simulateQ_compose _ _ program)
    dsimp only [real]
    rw [QueryImpl.simulateQ_compose, resolve, (encoding s).typedImpl_eq_handlerRouterImpl]
    simpa only [E, SecretEncoding.realImpl, QueryImpl.simulateQ_compose] using
      simulateQ_handlerRouterImpl_simulateQ_liftTypedImpl_run H.romImpl
        (encoding s).tableRouter (simulateQ (E.deriveImpl secret) program) cache privateCache
  have componentSupport {alpha : Type}
      (program : OracleComp (deriveSpec FIPS205.core) alpha)
      (before : TypedPV) (after : alpha × TypedPV)
      (hafter : after ∈ support ((simulateQ real (simulateQ embedD program)).run before)) :
      (after.1, after.2.1) ∈ support
        ((simulateQ (E.realImpl secret) program).run before.1) := by
    rw [componentRun, support_map] at hafter
    obtain ⟨result, hresult, hshape⟩ := hafter
    simpa only [← hshape] using hresult
  have cacheStep (input : DNative.Domain) (before : TypedPV)
      (after : DNative.Range input × TypedPV)
      (hafter : after ∈ support ((real input).run before)) : before.1 ≤ after.2.1 := by
    cases input with
    | inl input =>
      have injected : embedD input = (liftM (DNative.query (.inl input)) :
          OracleComp DNative ((deriveSpec FIPS205.core).Range input)) := by
        dsimp only [embedD]
        rw [QueryImpl.ofLift_apply]
        rcases input with (n | typed) | derivation <;> rfl
      have h := componentSupport (liftM ((deriveSpec FIPS205.core).query input)) before after
        (by simpa only [simulateQ_spec_query, injected] using hafter)
      rw [SecretEncoding.realImpl, QueryImpl.simulateQ_compose] at h
      exact le_snd_of_mem_support_run_unifFwdImpl_add_withCaching uniformSampleImpl _ h
    | inr bytes =>
      have normal : (real (.inr bytes)).run before =
          (fun result => (result.1.1, (result.2, result.1.2))) <$>
            (simulateQ H.romImpl (((encoding s).tableRouter bytes).run before.2)).run before.1 := by
        simp only [real, resolveNative, QueryImpl.apply_compose, QueryImpl.add,
          simulateQ_spec_query, (encoding s).typedImpl_eq_handlerRouterImpl,
          handlerRouterImpl, StateT.run_mk]
      rw [normal, support_map] at hafter
      obtain ⟨result, hresult, rfl⟩ := hafter
      exact le_snd_of_mem_support_run_unifFwdImpl_add_withCaching uniformSampleImpl _ hresult
  -- The order used by the generic log witness records only growth of the real hash cache.
  let cacheOrder : Preorder TypedPV := Preorder.lift (fun world : TypedPV => world.1)
  have cacheMono {alpha : Type} (program : OracleComp DNative alpha)
      (before : TypedPV) (after : alpha × TypedPV)
      (hafter : after ∈ support ((simulateQ real program).run before)) : before.1 ≤ after.2.1 := by
    exact simulateQ_run_preservesInv real (fun current => before.1 ≤ current.1)
      (fun input current hcurrent result hresult =>
        hcurrent.trans (cacheStep input current result hresult))
      program before le_rfl after hafter
  have keyNatural : simulateQ (E.deriveImpl secret)
      (GeneralScheme.keygenInternalWithSecretM FIPS205.core
        (deriveSecret FIPS205.core) s) =
      (GeneralScheme.keygenInternalWithSecretM FIPS205.core provider s :
        OracleComp (unifSpec + H) FIPS205.core.Y) :=
    GeneralScheme.keygenInternalWithSecretM_natural FIPS205.core
      (deriveHom FIPS205.core (Equiv.refl _) s secret) (deriveSecret FIPS205.core) provider
      (fun _ ha => simulateQ_deriveImpl_deriveSecret FIPS205.core (Equiv.refl _) s secret ha) s
  let decodeLog := Settlement.typedLog
  simp only [simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure,
    mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at physical
  obtain ⟨keys, hkeys, client, hclient, checked, hchecked, finalShape⟩ := physical
  have keyEq : keys.1 = retained.1 := (congrArg (fun result => result.1.1) finalShape).symm
  have rawLogEq : client.1.2 = retained.2.rawLog :=
    (congrArg (fun result => result.1.2.rawLog) finalShape).symm
  have cacheEq : checked.2.1 = values := (congrArg (fun result => result.2.1) finalShape).symm
  have checkedTrue : checked.1 = true := by
    have same := congrArg (fun result => result.1.2.verified) finalShape
    exact same.symm.trans hwins.1
  have keyToClient := cacheMono _ _ _ hclient
  have clientToFinal := cacheMono _ _ _ hchecked
  have publicReplay {alpha : Type} (program : OracleComp (publicHashSpec FIPS205.core) alpha)
      (cache : H.QueryCache) (result : alpha × H.QueryCache)
      (hresult : result ∈ support ((simulateQ H.romImpl
        (simulateQ (HasQuery.toQueryImpl (spec := publicHashSpec FIPS205.core)
          (m := OracleComp (unifSpec + H))) program)).run cache))
      (hle : result.2 ≤ checked.2.1) :
      simulateQ checked.2.1.fst.toPartialImpl program = some result.1 :=
    QueryCache.simulateQ_toPartialImpl_mono (QueryCache.fst_mono hle) _
      (simulateQ_toPartialImpl_snd_fst_of_mem_support_run_romImpl program hresult)
  have keyGraph := componentSupport
    (deriveScheme FIPS205.core (fun pk => pure pk.pkSeed) s).keygen (∅, ∅) keys
    (by simpa only [view, unresolvedView, SigningView.rejectingEncoding_keygen,
      SignatureAlg.map_keygen, embedD] using hkeys)
  rw [SecretEncoding.realImpl, QueryImpl.simulateQ_compose] at keyGraph
  simp only [deriveScheme, simulateQ_bind, simulateQ_pure, keyNatural] at keyGraph
  dsimp only [provider] at keyGraph
  rw [keygenInternalWithSecretM_oracleSecret_eq_ofSimulateQ
    (core := FIPS205.core) (m := OracleComp (unifSpec + H)) (Equiv.refl _) s secret.1] at keyGraph
  simp only [StateT.run_bind, StateT.run_pure, mem_support_bind_iff, support_pure,
    Set.mem_singleton_iff] at keyGraph
  obtain ⟨root, hroot, rootShape⟩ := keyGraph
  have firstKey : keys.1.1 = (⟨s, root.1⟩ : PK) := by
    exact congrArg (fun result => result.1.1) rootShape
  have secondKey : keys.1.2 = keys.1.1 := by
    exact (congrArg (fun result => result.1.2) rootShape).trans firstKey.symm
  have keyCache : root.2 = keys.2.1 := by
    exact (congrArg Prod.snd rootShape).symm
  have seed : keys.1.1.pkSeed = s := by rw [firstKey]
  have rootReplay : simulateQ checked.2.1.fst.toPartialImpl
      (GeneralScheme.keygenInternalWithSecretM FIPS205.core provider keys.1.1.pkSeed) =
        some keys.1.1.pkRoot := by
    have h := publicReplay _ _ root hroot
      (keyCache.le.trans (keyToClient.trans clientToFinal))
    simpa only [firstKey] using h
  have signReplay (entry) (hentry : entry ∈ decodeLog client.1.2) :
      simulateQ checked.2.1.fst.toPartialImpl
        (GeneralScheme.signInternalWithSecretRandomizerM FIPS205.core provider
          entry.1 keys.1.1.pkSeed keys.1.1.pkRoot entry.2.randomness) = some entry.2 := by
    obtain ⟨rawEntry, hrawEntry, wire, reply, decoded, framed⟩ :=
      Settlement.data_of_mem_typedLog client.1.2 entry hentry
    dsimp only [Settlement.framed] at framed
    dsimp only [Settlement.parsed] at decoded
    obtain ⟨before, after, _, afterLe, hsign⟩ :=
      @QueryImpl.exists_le_mem_support_run_of_mem_log_add_withLogging _ _ DNative Sign
        TypedPV cacheOrder real (fun {_} program st r hmem => cacheMono program st r hmem)
        (view.sign keys.1.1 keys.1.2) _ (rawMainD adv keys.1.1) _ client
        (by simpa only [SigningView.runWithSigningOracle, SigningView.signingOracle,
          QueryImpl.passthrough_add, HasQuery.toQueryImpl_eq_id'] using hclient) rawEntry hrawEntry
    have typedSign := componentSupport
      ((some ∘ SLHDSA.encodeSignature FIPS205.params
        (SLHDSA.Concrete.shakeWireCodec FIPS205.params.params)) <$>
        (deriveScheme FIPS205.core (fun pk => pure pk.pkSeed) s).sign keys.1.1 keys.1.1 entry.1)
      before (rawEntry.2, after)
      (by simpa only [view, unresolvedView, SigningView.rejectingEncoding_sign,
        framed, SignatureAlg.map_sign, secondKey, embedD, simulateQ_map] using hsign)
    rw [simulateQ_map, StateT.run_map, support_map] at typedSign
    obtain ⟨signed, hsigned, signShape⟩ := typedSign
    have rawReply := congrArg Prod.fst signShape
    change some (SLHDSA.encodeSignature FIPS205.params
      (SLHDSA.Concrete.shakeWireCodec FIPS205.params.params) signed.1) = rawEntry.2 at rawReply
    have wireEq := Option.some.inj (rawReply.trans reply)
    rw [← wireEq, SLHDSA.decodeSignature_encode] at decoded
    have sigEq : signed.1 = entry.2 := Option.some.inj decoded
    have cacheEq : signed.2 = after.1 := congrArg Prod.snd signShape
    have mono : after.1 ≤ client.2.1 := afterLe
    have replay := resolved_sign_replay s secret keys.1.1 entry.1 signed.1 before.1 signed.2
      checked.2.1 (cacheEq.le.trans (mono.trans clientToFinal)) seed hsigned
    simpa only [sigEq, provider] using replay
  have verifierFrame : ∃ message signature,
      (External.encodePureMessage client.1.1.1.context client.1.1.1.message).toOption =
        some message ∧
      (SLHDSA.decodeSignature FIPS205.params
        (SLHDSA.Concrete.shakeWireCodec FIPS205.params.params) client.1.1.2).toOption =
        some signature ∧
      simulateQ checked.2.1.fst.toPartialImpl
        (GeneralScheme.verifyInternalM FIPS205.params FIPS205.core
          message signature keys.1.1) = some true := by
    cases framed : (External.encodePureMessage client.1.1.1.context
        client.1.1.1.message).toOption with
    | none =>
      simp only [unresolvedView, SigningView.rejectingEncoding_verify, framed,
        simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hchecked
      have h := congrArg Prod.fst hchecked
      simp [checkedTrue] at h
    | some message =>
      cases decoded : (SLHDSA.decodeSignature FIPS205.params
          (SLHDSA.Concrete.shakeWireCodec FIPS205.params.params) client.1.1.2).toOption with
      | none =>
        simp only [unresolvedView, SigningView.rejectingEncoding_verify, framed, decoded,
          simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hchecked
        have h := congrArg Prod.fst hchecked
        simp [checkedTrue] at h
      | some signature =>
        have hverify := componentSupport
          ((deriveScheme FIPS205.core (fun pk => pure pk.pkSeed) s).verify
            keys.1.1 message signature) client.2 checked
          (by simpa only [view, unresolvedView, SigningView.rejectingEncoding_verify,
            framed, decoded, SignatureAlg.map_verify, embedD] using hchecked)
        have read := resolved_verify_replay s secret keys.1.1 message signature client.2.1
          checked.2.1 checked.1 hverify
        exact ⟨message, signature, rfl, rfl, by simpa only [checkedTrue] using read⟩
  obtain ⟨message, signature, framed, decoded, verified⟩ := verifierFrame
  have candidateEq : client.1.1 = retained.2.forgery :=
    (congrArg (fun result => result.1.2.forgery) finalShape).symm
  refine ⟨message, signature, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [candidateEq] using framed
  · simpa only [candidateEq] using decoded
  · simpa only [keyEq] using seed
  · simpa only [keyEq, cacheEq] using rootReplay
  · intro entry hentry
    have h := signReplay entry (by simpa only [decodeLog, rawLogEq] using hentry)
    simpa only [keyEq, cacheEq] using h
  · simpa only [keyEq, cacheEq] using verified

private theorem unmarked_of_free_reshape
    {ι α Cache RawTable Aux C : Type} {spec : OracleSpec.{0, 0} ι}
    [AddMonoid C] [Preorder C] [CanonicallyOrderedAdd C] [DecidableLE C]
    (caps : C) (cost : spec.Domain → C)
    (handler : QueryImpl spec (StateT (Cache × RawTable) ProbComp))
    (mark : (i : spec.Domain) → (Cache × RawTable) → spec.Range i → (Cache × RawTable) → Aux → Aux)
    (fb : (i : spec.Domain) → spec.Range i) (p : OracleComp spec α)
    (initial : Cache × RawTable) (aux0 : Aux)
    (world : ProbComp ((((α × (PUnit × (C × Bool))) × RawTable) × Aux) × Cache))
    (shape : ((fun r : (α × (PUnit × (C × Bool))) × ((Cache × RawTable) × Aux) =>
        (((r.1, r.2.1.2), r.2.2), r.2.1.1)) <$>
      (simulateQ (handler.extendState mark)
        ((simulateQ (QueryImpl.guardQueryBudget caps cost
          ((QueryImpl.id' spec).liftTarget (StateT PUnit (OracleComp spec))) fb) p).run
            (PUnit.unit, (0, false)))).run (initial, aux0)) = world)
    (out : (((α × (PUnit × (C × Bool))) × RawTable) × Aux) × Cache)
    (mem : out ∈ support world)
    (ok : out.1.1.1.2.2.2 = false) :
    (out.1.1.1.1, (out.2, out.1.1.2)) ∈ support ((simulateQ handler p).run initial) := by
  rw [← shape, support_map] at mem
  obtain ⟨r, mem, rfl⟩ := mem
  have ordinary := source_of_free_guard caps cost (handler.extendState mark) fb p
    (initial, aux0) r mem ok
  rw [← extendState_run_proj_eq handler mark p initial aux0, support_map]
  exact ⟨(r.1.1, r.2), ordinary, rfl⟩

/-- Removing the query guard on a surviving run keeps the physical terminal and both caches. -/
private theorem unguarded_physical_source_support
    (s : FIPS205.core.PkSeed) (adv : Game.Adversary FIPS205.Answer PK)
    (reserve : Bool) (caps : Nat × Nat) (secret : Secret) :
    ∀ (out : GuardedFill.Value.{0} × H.QueryCache),
      out ∈ support ((simulateQ ((secretEncoding FIPS205.core (Equiv.refl _) s).realImpl secret)
        (GuardedFill.freeProgram s adv reserve true caps)).run ∅) →
      out.1.1.1.2.2.2 = false →
      (out.1.1.1.1, (out.2, out.1.1.2)) ∈ support
        ((simulateQ (eraseObsImpl (Ev := Ev) ((encoding s).typedImpl ∘ₛ resolveNative s secret))
          (fixedSource s adv)).run (∅, ∅)) := by
  let real := (encoding s).typedImpl ∘ₛ resolveNative s secret
  let charge := Sum.elim (fun _ : DNative.Domain => (0, 0)) (policy reserve s)
  let world := (simulateQ ((secretEncoding FIPS205.core (Equiv.refl _) s).realImpl secret)
    (GuardedFill.freeProgram s adv reserve true caps)).run ∅
  with_reducible_and_instances
    exact @unmarked_of_free_reshape _ Guarded.Full H.QueryCache Raw.QueryCache Meta (Nat × Nat)
      DCommon _ _ _ _ caps charge (eraseObsImpl (Ev := Ev) real) (aux (metadataCost true s))
      (deriveFallback s) (fixedSource s adv) (∅, ∅) (0, .keygen) world
      (resolved_guarded_router_observer_square s adv reserve true caps secret)

private theorem recover_winning_output {α : Type} {p : ProbComp α} {N O W S : α → Prop}
    (erase : ∀ x ∈ support p, N x → O x) (replay : ∀ x, O x → W x → S x) :
    ∀ x ∈ support p, N x → W x → S x :=
  fun x hx ok => replay x (erase x hx ok)

/-- A nonaborted winning unresolved source settles its actual decoded transcript in the
returned real cache. Its private derivations are interpreted at the supplied secret; the
key pair, raw reply log, metadata and paid state belong to this same supported execution. -/
theorem real_cache_settles_unresolved_source
    (s : FIPS205.core.PkSeed) (adv : Game.Adversary FIPS205.Answer PK)
    (reserve : Bool) (caps : Nat × Nat) (secret : Secret) :
    letI : MonadLiftT (OracleComp DCommon) (StateT PUnit (OracleComp DCommon)) :=
      ⟨fun action => StateT.lift action⟩
    let E := secretEncoding FIPS205.core (Equiv.refl _) s
    let guarded := (simulateQ (QueryImpl.guardQueryBudget caps
      (Sum.elim (fun _ : DNative.Domain => (0, 0)) (policy reserve s))
      ((QueryImpl.id' DCommon).liftTarget (StateT PUnit (OracleComp DCommon)))
      (deriveFallback s)) (fixedSource s adv)).run
        (PUnit.unit, ((0, 0), false))
    let freeProgram := (simulateQ (observeD s true)
      ((simulateQ (routeD s) guarded).run ∅)).run (0, .keygen)
    ∀ out ∈ support ((simulateQ (E.realImpl secret) freeProgram).run ∅),
      let full := out.1.1.1.1
      let cache := out.2.fst
      let typedLog := Settlement.typedLog full.2.rawLog
      let provider := oracleSecret FIPS205.core (Equiv.refl _) s secret.1
      out.1.1.1.2.2.2 = false → SigningView.Wins id full.2 →
      ∃ (message : List Byte)
        (signature : GeneralScheme.SignatureCore FIPS205.params FIPS205.core),
        (External.encodePureMessage full.2.forgery.1.context
          full.2.forgery.1.message).toOption = some message ∧
        (SLHDSA.decodeSignature FIPS205.params
          (SLHDSA.Concrete.shakeWireCodec FIPS205.params.params)
          full.2.forgery.2).toOption = some signature ∧
        full.1.1.pkSeed = s ∧
        simulateQ cache.toPartialImpl
          (GeneralScheme.keygenInternalWithSecretM FIPS205.core provider full.1.1.pkSeed) =
            some full.1.1.pkRoot ∧
        (∀ entry ∈ typedLog, simulateQ cache.toPartialImpl
          (GeneralScheme.signInternalWithSecretRandomizerM FIPS205.core provider
            entry.1 full.1.1.pkSeed full.1.1.pkRoot entry.2.randomness) = some entry.2) ∧
        simulateQ cache.toPartialImpl
          (GeneralScheme.verifyInternalM FIPS205.params FIPS205.core
            message signature full.1.1) = some true := by
  with_reducible_and_instances
    exact recover_winning_output (unguarded_physical_source_support s adv reserve caps secret)
      (fun out => ordinary_cache_replays s adv secret out.1.1.1.1 out.2 out.1.1.2 _ rfl)

end SLHDSA.SHAKE128s.Bridge.SharedExperiment.Native
end
