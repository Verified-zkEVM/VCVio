/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module

public import HashSig.SLHDSA.SHAKE128s.Proof.ActualWork.Transcript.ReplyLog

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
import all HashSig.SLHDSA.SHAKE128s.Proof.ActualWork.Transcript.RoleInvariant
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
# Deferred signing log and verification on a nonaborting run

The signing log identifies private cells that remain hidden on a surviving run. If the graph
has no conflict and the public cache misses encoded secret points, the verifier can replay
against the cache before the remaining cells are filled.
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
set_option maxRecDepth 12000 in
set_option maxHeartbeats 1200000 in
-- The joint source records key generation, signing replies and the prefill verifier cache.
/-- The actual nonaborted deferred transcript retains its seed and hidden cells, and its
public verifier replays already on the prefill graph cache. Secret merging is permitted only
off a graph conflict and an encoded public-cache point, as required by cache monotonicity. -/
theorem deferred_nonabort_hidden_log_and_verify
    (s : FIPS205.core.PkSeed) (adv : Game.Adversary FIPS205.Answer PK)
    (reserve : Bool) (caps : Nat × Nat)
    (fallback : (input : LabCommon.Domain) → LabCommon.Range input)
    (out : (((Guarded.Full × (PUnit × Paid)) × Raw.QueryCache) × Meta) ×
      (LabState FIPS205.core × List (DeriveQuery FIPS205.core ⊕ NodeKey FIPS205.core)))
    (hout : out ∈ support ((simulateQ (slhGraph FIPS205.core s).deferredImpl
      (deferredProgram s adv reserve caps fallback)).run ((∅, ∅), [])))
    (hnotAborted : out.1.1.1.2.2.2 = false) :
    let full := out.1.1.1.1
    let G := slhGraph FIPS205.core s
    let E := secretEncoding FIPS205.core (Equiv.refl _) s
    let typedLog := Settlement.typedLog full.2.rawLog
    full.1.1.pkSeed = s ∧ HiddenUndrawn FIPS205.core full.1.1 typedLog out.2.1 ∧
      ∀ secret : Secret, ¬G.Conflict out.2.1 →
        (¬∃ cell, (out.2.1.1 (E.enc secret cell)).isSome) →
        ∀ (message : List Byte)
          (signature : GeneralScheme.SignatureCore FIPS205.params FIPS205.core),
          (External.encodePureMessage full.2.forgery.1.context
            full.2.forgery.1.message).toOption = some message →
          (SLHDSA.decodeSignature FIPS205.params
            (SLHDSA.Concrete.shakeWireCodec FIPS205.params.params)
            full.2.forgery.2).toOption = some signature →
          simulateQ ((E.merge secret (G.toSplitCache out.2.1)).fst).toPartialImpl
            (GeneralScheme.verifyInternalM FIPS205.params FIPS205.core
              message signature full.1.1) = some full.2.verified := by
  classical
  dsimp only
  let _ : MonadLiftT (OracleComp.{0, 0, 0} LabCommon)
      (StateT PUnit.{1} (OracleComp.{0, 0, 0} LabCommon)) :=
    ⟨fun action => StateT.lift action⟩
  let G := slhGraph FIPS205.core s
  let hd : FIPS205.core.KeyDiscipline FIPS205.params :=
    Concrete.keyDiscipline_approvedPrimitives .SLHDSA_SHAKE_128s
  let D := CoverageDeferred.D FIPS205.core
  let graph := G.deferredImpl
  let native := eraseObsImpl (Ev := Ev) graph
  let observed := native.extendState (aux (spec := Lab) (metadataCost true s))
  let routed := QueryImpl.Stateful.link (routeLab s) observed
  let plain := QueryImpl.Stateful.link (routeLab s) native
  let plainA : QueryImpl A (StateT (Raw.QueryCache × D) ProbComp) :=
    fun input => plain (.inl input)
  let charge := Sum.elim (fun _ : A.Domain => (0, 0)) (policy reserve s)
  let reshape := fun result :
      (((Guarded.Full × (PUnit × Paid)) × Raw.QueryCache) × Meta) × D =>
    (result.1.1.1.1, ((result.1.1.2, (result.2, result.1.2)), result.1.1.1.2.2))
  have guarded : reshape out ∈ support
      ((simulateQ (QueryImpl.guardQueryBudget caps charge routed fallback)
        (commonSource true s adv)).run ((∅, (((∅, ∅), []), (0, .keygen))),
          ((0, 0), false))) := by
    rw [← deferred_guarded_front_run_eq s adv reserve caps fallback, support_map]
    exact ⟨out, hout, rfl⟩
  have unguarded : ((reshape out).1, (reshape out).2.1) ∈ support
      ((simulateQ routed (commonSource true s adv)).run
        (∅, (((∅, ∅), []), (0, .keygen)))) :=
    mem_support_source_of_guard_not_aborted caps charge routed fallback
      (commonSource true s adv) (∅, (((∅, ∅), []), (0, .keygen)))
      (reshape out) guarded hnotAborted
  have physical : (out.1.1.1.1, (out.1.1.2, out.2)) ∈ support
      ((simulateQ plain (commonSource true s adv)).run (∅, ((∅, ∅), []))) := by
    rw [← deferred_forget_metadata_run_eq s (commonSource true s adv)
      (∅, (((∅, ∅), []), (0, .keygen))), support_map]
    exact ⟨((reshape out).1, (reshape out).2.1), unguarded, rfl⟩
  let view := commonView true s
  let full := do
    let keys ← view.keygen
    let (candidate, replies) ← view.runWithSigningOracle keys.1 keys.2
      (commonMain adv keys.1)
    let verified ← view.verify keys.1 candidate.1 candidate.2
    pure (keys, (⟨candidate, replies, verified⟩ : RawOutcome))
  have sourceEvents : plain ∘ₛ commonProjection =
      SigningView.Events.handlerWithEvents (Request := Message) plainA := by
    funext input
    cases input with
    | inl input => simp [plainA, commonProjection, QueryImpl.apply_compose, QueryImpl.add,
        SigningView.Events.handlerWithEvents]
    | inr event =>
      cases hevent : commonEvent event <;>
        simp [plain, native, commonProjection, hevent, QueryImpl.add,
          SigningView.Events.handlerWithEvents, StateT.ext_iff, QueryImpl.apply_compose,
          routeLab, QueryImpl.Stateful.link_impl_apply_run, eraseObsImpl,
          QueryImpl.Stateful.Frame.linkReshape, QueryImpl.Stateful.Frame.prod,
          PFunctor.Lens.State.fst_put, PFunctor.Lens.State.snd_put]
  have eventErasure : simulateQ plain (commonSource true s adv) = simulateQ plainA full := by
    as_aux_lemma =>
      rw [commonSource, ← QueryImpl.simulateQ_compose, sourceEvents]
      dsimp only [full]
      rw [← erase_full_signing_events view (commonMain adv)]
      symm
      apply QueryImpl.simulateQ_simulateQ_eq_of_apply
      intro input
      cases input <;>
        simp [SigningView.Events.handlerWithEvents, plainA]
  rw [eventErasure] at physical
  let liftLab : QueryImpl Lab (OracleComp A) :=
    fun input => liftM (A.query (.inl input))
  have labProjection {alpha : Type} (program : OracleComp Lab alpha)
      (before : Raw.QueryCache × D) :
      Prod.map id Prod.snd <$>
        (simulateQ plainA (simulateQ liftLab program)).run before =
      (simulateQ graph program).run before.2 := by
    as_aux_lemma =>
      rw [← QueryImpl.simulateQ_compose]
      apply map_run_simulateQ_eq_of_query_map_eq
      rintro input ⟨raw, st⟩
      simp [plainA, plain, native, liftLab, routeLab, eraseObsImpl, QueryImpl.add,
        simulateQ_map, StateT.run_map, StateT.run_mk,
        QueryImpl.apply_compose, QueryImpl.Stateful.link_impl_apply_run,
        QueryImpl.Stateful.Frame.linkReshape, QueryImpl.Stateful.Frame.prod,
        PFunctor.Lens.State.fst_put, PFunctor.Lens.State.snd_put, Functor.map_map]
  have labSupport {alpha : Type} (program : OracleComp Lab alpha)
      (before : Raw.QueryCache × D) (after : alpha × (Raw.QueryCache × D))
      (hafter : after ∈ support
        ((simulateQ plainA (simulateQ liftLab program)).run before)) :
      (after.1, after.2.2) ∈ support ((simulateQ graph program).run before.2) := by
    as_aux_lemma =>
      rw [← labProjection program before, support_map]
      exact ⟨after, hafter, rfl⟩
  let decodeLog := Settlement.typedLog
  let Allowed : A.Domain → Prop
    | .inl (.inl (.inl (.inl _))) => True
    | .inr _ => True
    | _ => False
  have clientAllowed (key : PK) : AllQueriesSatisfy (commonMain adv key)
      (Sum.elim Allowed (fun _ => True)) := by
    as_aux_lemma =>
      unfold commonMain
      refine (allQueriesSatisfy_of_forall (fun _ => True.intro)
        (Game.Counted.externalMain adv key)).simulateQ ?_
      rintro ((sample | bytes) | request) _ <;>
        exact (allQueriesSatisfy_query_iff (spec := A + Sign) _ _).2 trivial
  have ambient (key : PK) (entries : QueryLog Sign) (before : Raw.QueryCache × D)
      (hbefore : HiddenUndrawn FIPS205.core key (decodeLog entries) before.2.1)
      (input : A.Domain) (hi : Allowed input) (after : A.Range input × (Raw.QueryCache × D))
      (hafter : after ∈ support ((plainA input).run before)) :
      HiddenUndrawn FIPS205.core key (decodeLog entries) after.2.2.1 := by
    as_aux_lemma =>
      rcases input with labInput | bytes
      · rcases labInput with (((sample | point) | (secret | nonce)) | (touch | read))
        · have hgraph := labSupport (liftM (Lab.query (.inl (.inl (.inl sample)))))
            before after (by simpa only [simulateQ_spec_query, liftLab] using hafter)
          rw [simulateQ_spec_query] at hgraph
          exact hiddenUndrawn_of_mem_support_deferredImpl hd s hbefore hgraph
        all_goals simp only [Allowed] at hi
      · let publicHandler : QueryImpl (unifSpec + H) (StateT D ProbComp) :=
          fun input => graph (.inl (.inl input))
        let rawProgram := ((encoding s).tableRouter bytes).run before.1
        have normal : (plainA (.inr bytes)).run before =
            (fun result => (result.1.1, (result.1.2, result.2))) <$>
              (simulateQ publicHandler rawProgram).run before.2 := by
          rcases before with ⟨raw, state⟩
          change (fun r => (r.1.1, (r.1.2, r.2))) <$>
            (simulateQ (eraseObsImpl (Ev := Ev) graph)
              (simulateQ (QueryImpl.ofLift (unifSpec + H) (OracleComp (Lab + O)))
                (((encoding s).tableRouter bytes).run raw))).run state = _
          rw [← QueryImpl.simulateQ_compose]
          have same : eraseObsImpl (Ev := Ev) graph ∘ₛ
                QueryImpl.ofLift (unifSpec + H) (OracleComp (Lab + O)) =
              (fun input => graph (.inl (.inl input))) := by
            funext input
            have qi : QueryImpl.ofLift (unifSpec + H) (OracleComp (Lab + O)) input =
                (liftM ((Lab + O).query (.inl (.inl (.inl input)))) :
                  OracleComp (Lab + O) ((unifSpec + H).Range input)) := by
              rcases input with n | (⟨seed, key, values⟩ | ⟨r, seed, root, msg⟩) | non
              all_goals rfl
            rw [QueryImpl.apply_compose, qi, simulateQ_spec_query]
            rfl
          rw [same]
        rw [normal, support_map] at hafter
        obtain ⟨result, hresult, rfl⟩ := hafter
        have allowed := allQueriesSatisfy_of_forall (fun _ => True.intro) rawProgram
        exact allowed.holds_of_mem_support_run_simulateQ
            (fun current : D => HiddenUndrawn FIPS205.core key (decodeLog entries) current.1)
            (fun _ _ _ hcurrent _ hstep =>
              hiddenUndrawn_of_mem_support_deferredImpl hd s hcurrent hstep) hbefore hresult
  have signing (key : PK) (hseed : key.pkSeed = s) (request : Message)
      (entries : QueryLog Sign) (before : Raw.QueryCache × D)
      (hbefore : HiddenUndrawn FIPS205.core key (decodeLog entries) before.2.1)
      (after : Option (List Byte) × (Raw.QueryCache × D))
      (hafter : after ∈ support ((simulateQ plainA (view.sign key key request)).run before)) :
      HiddenUndrawn FIPS205.core key (decodeLog (entries ++ [⟨request, after.1⟩]))
        after.2.2.1 := by
    as_aux_lemma =>
      cases framed : (External.encodePureMessage request.context request.message).toOption with
      | none =>
        simp only [view, commonView_eq_rejectingEncoding,
          ite_true, SigningView.rejectingEncoding_sign, framed, simulateQ_pure, StateT.run_pure,
          support_pure, Set.mem_singleton_iff] at hafter
        subst after
        simpa only [decodeLog, Settlement.typedLog_append_rejected] using hbefore
      | some message =>
        let program := (labScheme FIPS205.core (fun pk => pure pk.pkSeed) s).sign key key message
        simp only [view, commonView_eq_rejectingEncoding, ite_true,
          SigningView.rejectingEncoding_sign, framed, SignatureAlg.map_sign, simulateQ_map,
          StateT.run_map, support_map] at hafter
        obtain ⟨signed, hsigned, hshape⟩ := hafter
        have hg := labSupport program before signed hsigned
        have kept := hiddenUndrawn_of_mem_support_labScheme_sign s hd
          (fun pk => pure pk.pkSeed) hseed message hbefore hg
        have reply := (congrArg Prod.fst hshape).symm
        have stateEq := (congrArg (fun z => z.2.2) hshape).symm
        change after.1 = some (SLHDSA.encodeSignature FIPS205.params
          (SLHDSA.Concrete.shakeWireCodec FIPS205.params.params) signed.1) at reply
        change after.2.2 = signed.2.2 at stateEq
        have d : decodeLog (entries ++ [⟨request, after.1⟩]) =
            decodeLog entries ++ [⟨message, signed.1⟩] := by
          rw [reply]
          exact Settlement.typedLog_append_accepted entries request message _ signed.1 framed
            (Settlement.parsed_encoded signed.1)
        rw [d, stateEq]
        exact kept
  have verification (key : PK) (entries : QueryLog Sign) (request : Message)
      (wire : List Byte) (before : Raw.QueryCache × D)
      (hbefore : HiddenUndrawn FIPS205.core key (decodeLog entries) before.2.1)
      (after : Bool × (Raw.QueryCache × D))
      (hafter : after ∈ support ((simulateQ plainA (view.verify key request wire)).run before)) :
      HiddenUndrawn FIPS205.core key (decodeLog entries) after.2.2.1 := by
    as_aux_lemma =>
      cases framed : (External.encodePureMessage request.context request.message).toOption with
      | none =>
        simp only [view, commonView_eq_rejectingEncoding,
          ite_true, SigningView.rejectingEncoding_verify, framed, simulateQ_pure, StateT.run_pure,
          support_pure, Set.mem_singleton_iff] at hafter
        subst after
        exact hbefore
      | some message =>
        cases decoded : (SLHDSA.decodeSignature FIPS205.params
            (SLHDSA.Concrete.shakeWireCodec FIPS205.params.params) wire).toOption with
        | none =>
          simp only [view, commonView_eq_rejectingEncoding,
            ite_true, SigningView.rejectingEncoding_verify, framed, decoded, simulateQ_pure,
            StateT.run_pure, support_pure, Set.mem_singleton_iff] at hafter
          subst after
          exact hbefore
        | some signature =>
          have hgraph := labSupport
            ((labScheme FIPS205.core (fun pk => pure pk.pkSeed) s).verify key message signature)
            before after (by simpa only [view, commonView_eq_rejectingEncoding,
              SLHDSA.SHAKE128s.Bridge.SharedExperiment.Guarded.partialView, ite_true,
              SigningView.map, SignatureAlg.map_sign, SignatureAlg.map_verify,
              SignatureAlg.map_keygen, SigningView.rejectingEncoding_keygen,
              SigningView.rejectingEncoding_verify, framed, decoded, liftLab] using hafter)
          exact (allQueriesSatisfy_labScheme_verify (pkSeed := s) (fun pk => pure pk.pkSeed)
            key message signature).holds_of_mem_support_run_simulateQ
            (fun current : D => HiddenUndrawn FIPS205.core key (decodeLog entries) current.1)
            (by
              rintro ((input | _) | _) allowed current hcurrent result hresult
              · exact hiddenUndrawn_of_mem_support_deferredImpl hd s hcurrent hresult
              all_goals exact allowed.elim) hbefore hgraph
  simp only [full, simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure,
    mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at physical
  obtain ⟨keys, hkeys, client, hclient, checked, hchecked, hshape⟩ := physical
  have keyGraph := labSupport
    (labScheme FIPS205.core (fun pk => pure pk.pkSeed) s).keygen
    (∅, ((∅, ∅), [])) keys (by
      simpa only [view, commonView_eq_rejectingEncoding,
        SLHDSA.SHAKE128s.Bridge.SharedExperiment.Guarded.partialView, ite_true, SigningView.map,
        SignatureAlg.map_sign, SignatureAlg.map_verify, SignatureAlg.map_keygen,
        SigningView.rejectingEncoding_keygen,
        liftLab] using hkeys)
  simp only [labScheme, simulateQ_bind, StateT.run_bind, mem_support_bind_iff,
    simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at keyGraph
  obtain ⟨root, hroot, keyShape⟩ := keyGraph
  have firstKey : keys.1.1 = (⟨s, root.1⟩ : PK) := by
    have h := congrArg (fun result => result.1.1) keyShape
    exact h
  have secondKey : keys.1.2 = keys.1.1 := by
    exact (congrArg (fun result => result.1.2) keyShape).trans firstKey.symm
  have keyState : keys.2.2 = root.2 := by
    exact congrArg Prod.snd keyShape
  have keySeed : keys.1.1.pkSeed = s := by rw [firstKey]
  have initial : HiddenUndrawn FIPS205.core keys.1.1 (decodeLog []) keys.2.2.1 := by
    rw [firstKey, keyState]
    intro cell hidden
    exact (hiddenKept_of_readsUnhidden s hroot
      (readsUnhidden_labXmssNode s hd _ _ _) cell hidden).trans rfl
  have afterClient : HiddenUndrawn FIPS205.core keys.1.1
      (decodeLog client.1.2) client.2.2.1 := by
    have h := QueryImpl.holds_of_mem_support_run_add_withLogging plainA
      (view.sign keys.1.1 keys.1.1) (allowed := Allowed)
      (fun entries world => HiddenUndrawn FIPS205.core keys.1.1
        (decodeLog entries) world.2.1)
      (fun input hi entries current hcurrent result hresult =>
        ambient keys.1.1 entries current hcurrent input hi result hresult)
      (fun request entries current hcurrent result hresult =>
        signing keys.1.1 keySeed request entries current hcurrent result hresult)
      (clientAllowed keys.1.1) initial
      (by simpa only [SigningView.runWithSigningOracle, SigningView.signingOracle,
        QueryImpl.passthrough_add, HasQuery.toQueryImpl_eq_id', secondKey] using hclient)
    simpa only [List.nil_append] using h
  have finalHidden := verification keys.1.1 client.1.2 client.1.1.1 client.1.1.2
    client.2 afterClient checked hchecked
  have keyEq : out.1.1.1.1.1.1 = keys.1.1 := congrArg (fun result => result.1.1.1) hshape
  have logEq : out.1.1.1.1.2.rawLog = client.1.2 :=
    congrArg (fun result => result.1.2.rawLog) hshape
  have cacheEq : out.2 = checked.2.2 := congrArg (fun result => result.2.2) hshape
  refine ⟨by simpa only [keyEq] using keySeed,
    by simpa only [keyEq, logEq, cacheEq, decodeLog] using finalHidden, ?_⟩
  intro secret hconflict hnoEncoded message signature framed decoded
  have candidateEq : client.1.1 = out.1.1.1.1.2.forgery :=
    (congrArg (fun result => result.1.2.forgery) hshape).symm
  have framedClient : (External.encodePureMessage client.1.1.1.context
      client.1.1.1.message).toOption = some message := by
    simpa only [candidateEq] using framed
  have decodedClient : (SLHDSA.decodeSignature FIPS205.params
      (SLHDSA.Concrete.shakeWireCodec FIPS205.params.params) client.1.1.2).toOption =
        some signature := by
    simpa only [candidateEq] using decoded
  have graphVerify := labSupport
    ((labScheme FIPS205.core (fun pk => pure pk.pkSeed) s).verify
      keys.1.1 message signature) client.2 checked (by
        simpa only [view, commonView_eq_rejectingEncoding,
          SLHDSA.SHAKE128s.Bridge.SharedExperiment.Guarded.partialView, ite_true, SigningView.map,
        SignatureAlg.map_sign, SignatureAlg.map_verify, SignatureAlg.map_keygen,
        SigningView.rejectingEncoding_keygen,
          SigningView.rejectingEncoding_verify, framedClient, decodedClient,
          liftLab] using hchecked)
  let publicProgram := (GeneralScheme.verifyInternalM FIPS205.params FIPS205.core
    message signature keys.1.1 : OracleComp (publicHashSpec FIPS205.core) Bool)
  let publicHom := HasQuery.QueryHom.ofSimulateQ
    (spec := publicHashSpec FIPS205.core) (m := OracleComp Lab)
  have publicSource : (labScheme FIPS205.core (fun pk => pure pk.pkSeed) s).verify
      keys.1.1 message signature =
      simulateQ (HasQuery.toQueryImpl (spec := publicHashSpec FIPS205.core)
        (m := OracleComp Lab)) publicProgram := by
    simpa only [labScheme, publicProgram, publicHom, HasQuery.QueryHom.ofSimulateQ_apply] using
      (GeneralScheme.verifyInternalM_natural FIPS205.params FIPS205.core
        publicHom message signature keys.1.1).symm
  rw [publicSource] at graphVerify
  have read := G.simulateQ_toPartialImpl_merge_fst_of_mem_support_deferredImpl
    publicProgram graphVerify le_rfl (by simpa only [cacheEq] using hconflict)
  rw [← cacheEq] at read
  have mergeLe := merge_le_merge_toSplitCache (e := Equiv.refl _) (s := secret)
    (st := out.2.1) hd.keySeparated hnoEncoded
  have replay := QueryCache.simulateQ_toPartialImpl_mono
    (QueryCache.fst_mono mergeLe) publicProgram read
  have verifiedEq : checked.1 = out.1.1.1.1.2.verified :=
    (congrArg (fun result => result.1.2.verified) hshape).symm
  simpa only [keyEq, verifiedEq, publicProgram] using replay

/-- A nonaborted deferred interpretation leaves the hidden cells of its actual decoded log
undrawn. The key and chronological raw replies are those returned by the same marked source;
metadata and the private raw table are retained in the supported output. -/
theorem deferred_nonabort_hidden_log
    (s : FIPS205.core.PkSeed) (adv : Game.Adversary FIPS205.Answer PK)
    (reserve : Bool) (caps : Nat × Nat)
    (fallback : (input : LabCommon.Domain) → LabCommon.Range input)
    (out : (((Guarded.Full × (PUnit × Paid)) × Raw.QueryCache) × Meta) ×
      (LabState FIPS205.core × List (DeriveQuery FIPS205.core ⊕ NodeKey FIPS205.core)))
    (hout : out ∈ support ((simulateQ (slhGraph FIPS205.core s).deferredImpl
      (deferredProgram s adv reserve caps fallback)).run ((∅, ∅), [])))
    (hnotAborted : out.1.1.1.2.2.2 = false) :
    let full := out.1.1.1.1
    let typedLog := Settlement.typedLog full.2.rawLog
    full.1.1.pkSeed = s ∧ HiddenUndrawn FIPS205.core full.1.1 typedLog out.2.1 := by
  have core := deferred_nonabort_hidden_log_and_verify s adv reserve caps fallback out
    hout hnotAborted
  exact ⟨core.1, core.2.1⟩


end SLHDSA.SHAKE128s.Bridge.SharedExperiment.Native
end
