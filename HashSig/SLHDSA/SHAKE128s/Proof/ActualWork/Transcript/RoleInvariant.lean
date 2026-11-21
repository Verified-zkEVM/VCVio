/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module

public import VCVio.CryptoFoundations.SignatureAlg.CountedExperiment
public import VCVio.OracleComp.QueryTracking.LoggingOracle.Core
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
public import HashSig.SLHDSA.SHAKE128s.Proof.ActualWork.Settlement.Support
import all HashSig.SLHDSA.SHAKE128s.Proof.ActualWork.Settlement.Support
import all HashSig.SLHDSA.SHAKE128s.Proof.ActualWork.Transcript.CacheOrigins
import all HashSig.SLHDSA.SHAKE128s.Proof.ActualWork.Transcript.KeyMarginal
import all HashSig.SLHDSA.SHAKE128s.Proof.ActualWork.Transcript.Program

import all HashSig.SLHDSA.SHAKE128s.Proof.ActualWork.Transcript.KeygenOrigins

/-!
# Signing and verification role invariants on a marked execution

Every accepted signing reply is covered at the retained public key. The proof follows
the two digest tapes, the role counters and the set of cells already read.
-/

public section

section

open OracleComp OracleSpec SignatureAlg
open SLHDSA SLHDSA.Security SLHDSA.SHAKE128s
open SLHDSA.SHAKE128s.Bridge.SharedExperiment.Guarded
open MeasureTheory
open SLHDSA.Security.CanonicalGames SLHDSA.DigestTransport
open scoped ENNReal

namespace SLHDSA.SHAKE128s.Bridge.SharedExperiment.Native
/-- A non-Hmsg public call is the existing deferred graph step with private uniform base. -/
private theorem relative_public_other_run
    (s : FIPS205.core.PkSeed) (point : H.Domain) (notHmsg : ¬IsHmsgPoint point)
    (state : CoverageDeferred.S FIPS205.core) (role : Coverage.RoleState FIPS205.core) :
    (simulateQ (Coverage.roleRunImpl FIPS205.core)
      ((CoverageDeferred.relative FIPS205.core s (metadataCost true s)
        (.inl (.inl (.inl (.inr point))))).run state)).run role =
      (fun out => ((out.1, (out.2, state.2)), role)) <$>
        (((slhGraph FIPS205.core s).deferredImpl (.inl (.inl (.inr point)))).run state.1) := by
  have other : ¬CoverageDeferred.IsSelectedNative FIPS205.core
      (.inl (.inl (.inr point))) := by
    rcases point with (⟨seed, key, values⟩ | ⟨R, seed, root, message⟩) | nonce
    · simp only [CoverageDeferred.IsSelectedNative, not_false_eq_true]
    · exact (notHmsg trivial).elim
    · simp only [CoverageDeferred.IsSelectedNative, not_false_eq_true]
  rw [CoverageDeferred.relative_other FIPS205.core s (metadataCost true s)
    (.inl (.inl (.inr point))) other]
  simp only [ simulateQ_map,  StateT.run_map,
      Coverage.roleRunImpl_liftComp_run, bind_pure_comp,
     Functor.map_map]

/-- An Hmsg call goes once through the actual forger copy and mirrors its returned digest. -/
private theorem relative_public_hmsg_run
    (s : FIPS205.core.PkSeed) (phase : SigningView.Phase)
    (hphase : phase = .adversary ∨ phase = .verification)
    (randomness : FIPS205.core.Y) (seed : FIPS205.core.PkSeed)
    (root : FIPS205.core.Y) (message : List Byte)
    (state : CoverageDeferred.S FIPS205.core) (role : Coverage.RoleState FIPS205.core)
    (currentPhase : state.2.2 = phase) :
    (simulateQ (Coverage.roleRunImpl FIPS205.core)
      ((CoverageDeferred.relative FIPS205.core s (metadataCost true s)
        (.inl (.inl (.inl (.inr (.inl (.hmsg randomness seed root message))))))).run
        state)).run role =
      (fun out =>
        ((out.1, (((state.1.1.1.cacheQuery (.inl (.hmsg randomness seed root message)) out.1,
          state.1.1.2), state.1.2), state.2)), out.2)) <$>
        ((Coverage.roleRunImpl FIPS205.core
          (.inr (.inl (.inl (.inl (.hmsg randomness seed root message)))))).run role) := by
  rw [CoverageDeferred.relative_hmsg]
  rcases hphase with rfl | rfl <;>
    simp [currentPhase, CoverageDeferred.phaseRole, Coverage.roleImpl]

open scoped Classical in
private theorem linked_native_eq (s : FIPS205.core.PkSeed) :
    QueryImpl.Stateful.link
      (CoverageDeferred.relative FIPS205.core s (metadataCost true s))
      (Coverage.roleRunImpl FIPS205.core) =
        NativeCounts.nativeImpl FIPS205.core s (metadataCost true s) := by
  funext input world
  rcases world with ⟨state, role⟩
  change ((QueryImpl.Stateful.link
    (CoverageDeferred.relative FIPS205.core s (metadataCost true s))
    (Coverage.roleRunImpl FIPS205.core)) input).run (state, role) =
      (NativeCounts.nativeImpl FIPS205.core s (metadataCost true s) input).run (state, role)
  rw [QueryImpl.Stateful.link_impl_apply_run, NativeCounts.nativeImpl,
    QueryImpl.flattenStateT_mapStateTBase_apply_run]
  rfl

private theorem native_uniform_run (s : FIPS205.core.PkSeed) (n : unifSpec.Domain)
    (world : CoverageDeferred.S FIPS205.core × Coverage.RoleState FIPS205.core) :
    (NativeCounts.nativeImpl FIPS205.core s (metadataCost true s)
      (.inl (.inl (.inl (.inl n))))).run world =
        (fun answer => (answer, world)) <$>
          (liftM (unifSpec.query n) : ProbComp (unifSpec.Range n)) := by
  rcases world with ⟨state, role⟩
  rw [NativeCounts.nativeImpl, QueryImpl.flattenStateT_mapStateTBase_apply_run]
  simp only [CoverageDeferred.relative, StateT.run_mk, simulateQ_map, StateT.run_map,
    Coverage.roleRunImpl_liftComp_run,
      CanonicalGraph.deferredImpl_run_inl,
    CanonicalGraph.relabelImpl_run_unif, Functor.map_map, Prod.eta, bind_pure_comp]

private theorem native_public_preserves
    (s : FIPS205.core.PkSeed) (phase : SigningView.Phase)
    (hphase : phase = .adversary ∨ phase = .verification)
    (pk : PK)
    (log : QueryLog (List Byte →ₒ GeneralScheme.SignatureCore FIPS205.params FIPS205.core))
    (point : H.Domain) (state : CoverageDeferred.S FIPS205.core)
    (role : Coverage.RoleState FIPS205.core)
    (hmetadata : state.2.2 = phase) (hinv : Coverage.RunInv FIPS205.core pk log role) :
    ∀ result ∈ support
      ((NativeCounts.nativeImpl FIPS205.core s (metadataCost true s)
        (.inl (.inl (.inl (.inr point))))).run (state, role)),
      Coverage.RunInv FIPS205.core pk log result.2.2 ∧ result.2.1.2 = state.2 := by
  intro result hresult
  rw [NativeCounts.nativeImpl, QueryImpl.flattenStateT_mapStateTBase_apply_run,
    support_map] at hresult
  obtain ⟨nested, hnested, rfl⟩ := hresult
  rcases point with (⟨seed, key, values⟩ | ⟨randomness, seed, root, message⟩) | nonce
  · rw [SLHDSA.SHAKE128s.Bridge.SharedExperiment.Native.relative_public_other_run s _ (by simp
    [IsHmsgPoint]),
      support_map] at hnested
    obtain ⟨answer, _, rfl⟩ := hnested
    exact ⟨hinv, rfl⟩
  · rw [SLHDSA.SHAKE128s.Bridge.SharedExperiment.Native.relative_public_hmsg_run s phase hphase
    randomness seed root
      message state role hmetadata, support_map] at hnested
    obtain ⟨answer, hanswer, rfl⟩ := hnested
    refine ⟨hinv.step ?_ hanswer, rfl⟩
    simp [Coverage.IsFrameQuery, Coverage.IsRoleRandQuery, Coverage.IsRandPoint,
      AnswerTape.classOf, Coverage.tapeClass]
  · rw [SLHDSA.SHAKE128s.Bridge.SharedExperiment.Native.relative_public_other_run s _ (by simp
    [IsHmsgPoint]),
      support_map] at hnested
    obtain ⟨answer, _, rfl⟩ := hnested
    exact ⟨hinv, rfl⟩

private theorem projected_ambient_source
    (phase : SigningView.Phase) (input : A.Domain) (event : Ev)
    (selected : commonEvent (.ambient phase input) = some event) :
    simulateQ commonProjection (SigningView.Events.phaseImpl A Message phase input) = (do
      let _ ← (liftM (LabCommon.query (.inr event)) : OracleComp LabCommon PUnit)
      (liftM (LabCommon.query (.inl input)) : OracleComp LabCommon (A.Range input))) := by
  simp [SigningView.Events.phaseImpl, SigningView.Events.emit, commonProjection,
    selected, QueryImpl.add, OracleQuery.input_query, OracleQuery.cont_query,
    seqRight_eq_bind]

private theorem routed_marker_run (s : FIPS205.core.PkSeed) (event : Ev)
    (before : Raw.QueryCache ×
      (CoverageDeferred.S FIPS205.core × Coverage.RoleState FIPS205.core)) :
    (QueryImpl.Stateful.link (routeLab s)
      (NativeCounts.nativeImpl FIPS205.core s (metadataCost true s)) (.inr event)).run before =
      pure (PUnit.unit, (before.1, ((before.2.1.1,
        CoverageDeferred.phaseCostAux FIPS205.core (metadataCost true s) (.inr event)
          before.2.1.1 PUnit.unit before.2.1.1 before.2.1.2), before.2.2))) := by
  rcases before with ⟨raw, state, role⟩
  rw [QueryImpl.Stateful.link_impl_apply_run]
  simp only [routeLab, QueryImpl.add, StateT.run_mk, simulateQ_bind,
    simulateQ_spec_query, simulateQ_pure, StateT.run_bind, StateT.run_pure]
  rfl

private theorem routed_uniform_run (s : FIPS205.core.PkSeed) (n : unifSpec.Domain)
    (before : Raw.QueryCache ×
      (CoverageDeferred.S FIPS205.core × Coverage.RoleState FIPS205.core)) :
    (QueryImpl.Stateful.link (routeLab s)
      (NativeCounts.nativeImpl FIPS205.core s (metadataCost true s))
        (.inl (.inl (.inl (.inl (.inl n)))))).run before =
      (fun answer => (answer, before)) <$>
        (liftM (unifSpec.query n) : ProbComp (unifSpec.Range n)) := by
  rcases before with ⟨raw, state, role⟩
  rw [QueryImpl.Stateful.link_impl_apply_run]
  simp only [routeLab, QueryImpl.add, StateT.run_mk, bind_pure_comp,
    simulateQ_map, StateT.run_map, simulateQ_spec_query, Functor.map_map]
  change (fun result : unifSpec.Range n ×
      (CoverageDeferred.S FIPS205.core × Coverage.RoleState FIPS205.core) =>
        (result.1, (raw, result.2))) <$>
      (NativeCounts.nativeImpl FIPS205.core s (metadataCost true s)
        (.inl (.inl (.inl (.inl n))))).run (state, role) = _
  simpa only [Functor.map_map] using congrArg
    (fun body => (fun result : unifSpec.Range n ×
      (CoverageDeferred.S FIPS205.core × Coverage.RoleState FIPS205.core) =>
        (result.1, (raw, result.2))) <$> body)
    (native_uniform_run s n (state, role))

private theorem routed_raw_run (s : FIPS205.core.PkSeed) (raw : Raw.Domain)
    (before : Raw.QueryCache ×
      (CoverageDeferred.S FIPS205.core × Coverage.RoleState FIPS205.core)) :
    (QueryImpl.Stateful.link (routeLab s)
      (NativeCounts.nativeImpl FIPS205.core s (metadataCost true s)) (.inl (.inr raw))).run
        before =
      (fun result : (Raw.Range raw × Raw.QueryCache) ×
          (CoverageDeferred.S FIPS205.core × Coverage.RoleState FIPS205.core) =>
        (result.1.1, (result.1.2, result.2))) <$>
        (simulateQ (NativeCounts.nativeImpl FIPS205.core s (metadataCost true s) ∘ₛ
          QueryImpl.ofLift (unifSpec + H) (OracleComp (Lab + O)))
          (((encoding s).tableRouter raw).run before.1)).run before.2 := by
  rcases before with ⟨privateCache, state, role⟩
  rw [QueryImpl.Stateful.link_impl_apply_run]
  simp only [routeLab, QueryImpl.add, StateT.run_mk]
  rw [← QueryImpl.simulateQ_compose]
  rfl

private theorem client_ambient_preserves_runInv
    (s : FIPS205.core.PkSeed) (root : FIPS205.core.Y) :
  let key : PK := ⟨s, root⟩
  let decodeLog := Settlement.typedLog
  let World := Raw.QueryCache ×
    (CoverageDeferred.S FIPS205.core × Coverage.RoleState FIPS205.core)
  let native := QueryImpl.Stateful.link
    (CoverageDeferred.relative FIPS205.core s (metadataCost true s))
    (Coverage.roleRunImpl FIPS205.core)
  let routed := QueryImpl.Stateful.link (routeLab s) native
  let outer := routed ∘ₛ commonProjection
  let ambient := outer ∘ₛ SigningView.Events.phaseImpl A Message .adversary
  let Allowed : A.Domain → Prop
    | .inl (.inl (.inl (.inl _))) => True
    | .inr _ => True
    | _ => False
  ∀ (input : A.Domain), Allowed input →
    ∀ (entries : QueryLog Sign) (before : World),
      Coverage.RunInv FIPS205.core key (decodeLog entries) before.2.2 →
      ∀ (after : A.Range input × World),
        after ∈ support ((ambient input).run before) →
          Coverage.RunInv FIPS205.core key (decodeLog entries) after.2.2.2 := by
  classical
  intro key decodeLog World native routed outer ambient Allowed input hi entries before hbefore
    after hafter
  have routed_eq : routed = QueryImpl.Stateful.link (routeLab s)
      (NativeCounts.nativeImpl FIPS205.core s (metadataCost true s)) := by
    dsimp only [routed, native]
    rw [linked_native_eq s]
  have forward (event : Ev) (selected : commonEvent (.ambient .adversary input) = some event) :
      (ambient input).run before = (do
        let entered ← (routed (.inr event)).run before
        (routed (.inl input)).run entered.2) := by
    change (simulateQ (routed ∘ₛ commonProjection)
      (SigningView.Events.phaseImpl A Message .adversary input)).run before = _
    rw [QueryImpl.simulateQ_compose, projected_ambient_source .adversary input event selected]
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
    rfl
  rcases input with lab | raw
  · rcases lab with (((n | point) | (secret | nonce)) | (touch | read))
    · let event : Ev := .ambient .adversary (.inl n)
      let marked : World := (before.1, ((before.2.1.1,
        (before.2.1.2.1 + metadataCost true s event, .adversary)), before.2.2))
      have marker : (routed (.inr event)).run before = pure (PUnit.unit, marked) := by
        rw [routed_eq, routed_marker_run]
        rfl
      rw [forward event rfl, marker, pure_bind, routed_eq, routed_uniform_run,
        support_map] at hafter
      obtain ⟨answer, _, rfl⟩ := hafter
      exact hbefore
    all_goals simp only [Allowed] at hi
  · let event : Ev := .ambient .adversary (.inr raw)
    let marked : World := (before.1, ((before.2.1.1,
      (before.2.1.2.1 + metadataCost true s event, .adversary)), before.2.2))
    have marker : (routed (.inr event)).run before = pure (PUnit.unit, marked) := by
      rw [routed_eq, routed_marker_run]
      rfl
    rw [forward event rfl, marker, pure_bind, routed_eq, routed_raw_run,
      support_map] at hafter
    obtain ⟨result, hresult, rfl⟩ := hafter
    let transport := QueryImpl.ofLift (unifSpec + H) (OracleComp (Lab + O))
    let handler := NativeCounts.nativeImpl FIPS205.core s (metadataCost true s) ∘ₛ transport
    let J : CoverageDeferred.S FIPS205.core × Coverage.RoleState FIPS205.core → Prop :=
      fun current => Coverage.RunInv FIPS205.core key (decodeLog entries) current.2 ∧
        current.1.2.2 = .adversary
    have uniformQuery (n : unifSpec.Domain)
        (current : CoverageDeferred.S FIPS205.core × Coverage.RoleState FIPS205.core) :
        (handler (.inl n)).run current =
          (fun answer => (answer, current)) <$>
            (liftM (unifSpec.query n) : ProbComp (unifSpec.Range n)) := by
      have included : transport (.inl n) =
          (liftM ((Lab + O).query (.inl (.inl (.inl (.inl n))))) :
            OracleComp (Lab + O) (unifSpec.Range n)) := by rfl
      change (simulateQ (NativeCounts.nativeImpl FIPS205.core s (metadataCost true s))
        (transport (.inl n))).run current = _
      rw [included, simulateQ_spec_query]
      exact native_uniform_run s n current
    have publicQuery (point : H.Domain)
        (current : CoverageDeferred.S FIPS205.core × Coverage.RoleState FIPS205.core) :
        (handler (.inr point)).run current =
          (NativeCounts.nativeImpl FIPS205.core s (metadataCost true s)
            (.inl (.inl (.inl (.inr point))))).run current := by
      have included : transport (.inr point) =
          (liftM ((Lab + O).query (.inl (.inl (.inl (.inr point))))) :
            OracleComp (Lab + O) (H.Range point)) := by
        rcases point with (⟨seed, key, values⟩ | ⟨R, seed, root, message⟩) | nonce <;> rfl
      change (simulateQ (NativeCounts.nativeImpl FIPS205.core s (metadataCost true s))
        (transport (.inr point))).run current = _
      rw [included, simulateQ_spec_query]
    have preserves : QueryImpl.PreservesInv handler J := by
      intro query current hcurrent next hnext
      rcases query with n | point
      · rw [uniformQuery, support_map] at hnext
        obtain ⟨answer, _, rfl⟩ := hnext
        exact hcurrent
      · rw [publicQuery] at hnext
        have kept := native_public_preserves s .adversary (Or.inl rfl) key
          (decodeLog entries) point current.1 current.2 hcurrent.2 hcurrent.1 next hnext
        exact ⟨kept.1, (congrArg Prod.snd kept.2).trans hcurrent.2⟩
    exact (simulateQ_run_preservesInv handler J preserves
      (((encoding s).tableRouter raw).run before.1)
      marked.2 (⟨hbefore, rfl⟩ : J marked.2) result hresult).1

private theorem routed_lab_run (s : FIPS205.core.PkSeed) (input : Lab.Domain)
    (before : Raw.QueryCache ×
      (CoverageDeferred.S FIPS205.core × Coverage.RoleState FIPS205.core)) :
    (QueryImpl.Stateful.link (routeLab s)
      (NativeCounts.nativeImpl FIPS205.core s (metadataCost true s))
        (.inl (.inl input))).run before =
      (fun result : Lab.Range input ×
          (CoverageDeferred.S FIPS205.core × Coverage.RoleState FIPS205.core) =>
        (result.1, (before.1, result.2))) <$>
        (NativeCounts.nativeImpl FIPS205.core s (metadataCost true s)
          (.inl input)).run before.2 := by
  rcases before with ⟨raw, state, role⟩
  rw [QueryImpl.Stateful.link_impl_apply_run]
  simp only [routeLab, QueryImpl.add, StateT.run_mk, bind_pure_comp,
    simulateQ_map, StateT.run_map, simulateQ_spec_query, Functor.map_map]
  rfl

private theorem projected_signer_private (input : Lab.Domain)
    (hi : SLHDSA.Security.NativeProvenance.StructuralInput FIPS205.core input ∧
      Keygen.NoPublicInput input) :
    simulateQ commonProjection
      (simulateQ (SigningView.Events.phaseImpl A Message .signer)
        (liftM (A.query (.inl input)) : OracleComp A (Lab.Range input))) =
      (liftM (LabCommon.query (.inl (.inl input))) :
        OracleComp LabCommon (Lab.Range input)) := by
  rcases input with ((pubInput | (secret | nonce)) | (touch | node))
  · exact hi.2.elim
  · simp [SigningView.Events.phaseImpl, SigningView.Events.emit, commonProjection,
      commonEvent, QueryImpl.add]
  · exact hi.1.elim
  all_goals
    simp [SigningView.Events.phaseImpl, SigningView.Events.emit, commonProjection,
      commonEvent, QueryImpl.add]

private theorem native_private_run (s : FIPS205.core.PkSeed) (input : Lab.Domain)
    (hi : SLHDSA.Security.NativeProvenance.StructuralInput FIPS205.core input ∧
      Keygen.NoPublicInput input)
    (state : CoverageDeferred.S FIPS205.core) (role : Coverage.RoleState FIPS205.core) :
    (NativeCounts.nativeImpl FIPS205.core s (metadataCost true s)
      (.inl input)).run (state, role) =
      (fun out => (out.1, ((out.2, state.2), role))) <$>
        ((slhGraph FIPS205.core s).deferredImpl input).run state.1 := by
  rw [← linked_native_eq, QueryImpl.Stateful.link_impl_apply_run,
    Keygen.relative_private_run s input hi]
  simp only [simulateQ_map, StateT.run_map,
    Coverage.roleRunImpl_liftComp_run,
    Functor.map_map]
  rfl

private theorem projected_phase_none (phase : SigningView.Phase) (input : A.Domain)
    (noEvent : commonEvent (.ambient phase input) = none) :
    simulateQ commonProjection (SigningView.Events.phaseImpl A Message phase input) =
      (liftM (LabCommon.query (.inl input)) : OracleComp LabCommon (A.Range input)) := by
  simp [SigningView.Events.phaseImpl, SigningView.Events.emit, commonProjection,
    noEvent, QueryImpl.add, OracleQuery.input_query, OracleQuery.cont_query,
    seqRight_eq_bind]

private theorem native_nonce_marginal (s : FIPS205.core.PkSeed) (salt : FIPS205.core.Y)
    (message : List Byte)
    (state : CoverageDeferred.S FIPS205.core) (role : Coverage.RoleState FIPS205.core)
    (hphase : state.2.2 = .signer) :
    (fun result : FIPS205.core.Y ×
        (CoverageDeferred.S FIPS205.core × Coverage.RoleState FIPS205.core) =>
      (result.1, result.2.2)) <$>
        (NativeCounts.nativeImpl FIPS205.core s (metadataCost true s)
          (.inl (.inl (.inr (.inr (salt, message)))))).run (state, role) =
      (Coverage.roleRunImpl FIPS205.core
        (.inr (.inr (.inr (.inr (salt, message)))))).run role := by
  have query : simulateQ (Coverage.roleRunImpl FIPS205.core)
      (Coverage.roleImpl FIPS205.core (CoverageDeferred.phaseRole state.2.2)
        (.inr (.inr (salt, message)))) =
      Coverage.roleRunImpl FIPS205.core (.inr (.inr (.inr (.inr (salt, message))))) := by
    simp only [hphase, CoverageDeferred.phaseRole, Coverage.roleImpl, simulateQ_spec_query]
  rw [← linked_native_eq, QueryImpl.Stateful.link_impl_apply_run,
    CoverageDeferred.relative_rand]
  simp only [simulateQ_map, StateT.run_map, query,
    QueryImpl.Stateful.Frame.linkReshape, QueryImpl.Stateful.Frame.prod,
    PFunctor.Lens.State.fst_put, PFunctor.Lens.State.snd_put,
    Functor.map_map, Prod.eta, id_map']

private theorem native_hmsg_marginal (s : FIPS205.core.PkSeed)
    (root randomizer : FIPS205.core.Y) (message : List Byte)
    (state : CoverageDeferred.S FIPS205.core) (role : Coverage.RoleState FIPS205.core)
    (hphase : state.2.2 = .signer) :
    (fun result : FIPS205.Answer ×
        (CoverageDeferred.S FIPS205.core × Coverage.RoleState FIPS205.core) =>
      (result.1, result.2.2)) <$>
        (NativeCounts.nativeImpl FIPS205.core s (metadataCost true s)
          (.inl (.inl (.inl (.inr (.inl (.hmsg randomizer s root message))))))).run
            (state, role) =
      (Coverage.roleRunImpl FIPS205.core
        (.inr (.inr (.inl (.inl (.hmsg randomizer s root message)))))).run role := by
  have query : simulateQ (Coverage.roleRunImpl FIPS205.core)
      (Coverage.roleImpl FIPS205.core (CoverageDeferred.phaseRole state.2.2)
        (.inl (.inr (.inl (.hmsg randomizer s root message))))) =
      Coverage.roleRunImpl FIPS205.core
        (.inr (.inr (.inl (.inl (.hmsg randomizer s root message))))) := by
    simp only [hphase, CoverageDeferred.phaseRole, Coverage.roleImpl,
      simulateQ_spec_query]
  rw [← linked_native_eq, QueryImpl.Stateful.link_impl_apply_run,
    CoverageDeferred.relative_hmsg]
  simp only [bind_pure_comp]
  rw [simulateQ_map, StateT.run_map, query]
  simp only [QueryImpl.Stateful.Frame.prod, PFunctor.Lens.State.fst_put,
    PFunctor.Lens.State.snd_put, Functor.map_map, Prod.eta, id_map']

private theorem signer_private_query_preserves_role
    (s : FIPS205.core.PkSeed) :
  let World := Raw.QueryCache ×
    (CoverageDeferred.S FIPS205.core × Coverage.RoleState FIPS205.core)
  let native := QueryImpl.Stateful.link
    (CoverageDeferred.relative FIPS205.core s (metadataCost true s))
    (Coverage.roleRunImpl FIPS205.core)
  let routed := QueryImpl.Stateful.link (routeLab s) native
  let outer := routed ∘ₛ commonProjection
  let liftLab : QueryImpl Lab (OracleComp A) := fun input =>
    (liftM (A.query (.inl input)) : OracleComp A (Lab.Range input))
  let phase := SigningView.Events.phaseImpl A Message .signer
  let signerImpl := outer ∘ₛ (phase ∘ₛ liftLab)
  ∀ (input : Lab.Domain),
    SLHDSA.Security.NativeProvenance.StructuralInput FIPS205.core input ∧
      Keygen.NoPublicInput input →
      ∀ (current : World) (result : Lab.Range input × World),
    result ∈ support ((signerImpl input).run current) →
      result.2.2.2 = current.2.2 := by
  intro World native routed outer liftLab phase signerImpl input hi current result hresult
  have shaped : result ∈ support
      ((simulateQ routed (simulateQ commonProjection
        (simulateQ phase (liftLab input)))).run current) := by
    simpa only [signerImpl, outer, QueryImpl.apply_compose,
      QueryImpl.simulateQ_compose] using hresult
  rw [projected_signer_private input hi, simulateQ_spec_query] at shaped
  change result ∈ support
    ((QueryImpl.Stateful.link (routeLab s)
      (QueryImpl.Stateful.link
        (CoverageDeferred.relative FIPS205.core s (metadataCost true s))
        (Coverage.roleRunImpl FIPS205.core))
          (.inl (.inl input))).run current) at shaped
  rw [linked_native_eq, routed_lab_run, native_private_run s input hi, Functor.map_map,
    support_map] at shaped
  obtain ⟨out, hout, rfl⟩ := shaped
  rfl

private theorem signer_private_run_preserves_role
    (s : FIPS205.core.PkSeed) :
  let World := Raw.QueryCache ×
    (CoverageDeferred.S FIPS205.core × Coverage.RoleState FIPS205.core)
  let native := QueryImpl.Stateful.link
    (CoverageDeferred.relative FIPS205.core s (metadataCost true s))
    (Coverage.roleRunImpl FIPS205.core)
  let routed := QueryImpl.Stateful.link (routeLab s) native
  let outer := routed ∘ₛ commonProjection
  let liftLab : QueryImpl Lab (OracleComp A) := fun input =>
    (liftM (A.query (.inl input)) : OracleComp A (Lab.Range input))
  let phase := SigningView.Events.phaseImpl A Message .signer
  let signerImpl := outer ∘ₛ (phase ∘ₛ liftLab)
  ∀ {alpha : Type} (program : OracleComp Lab alpha),
    AllQueriesSatisfy program (fun input =>
      SLHDSA.Security.NativeProvenance.StructuralInput FIPS205.core input ∧
        Keygen.NoPublicInput input) →
      ∀ (current : World) (result : alpha × World),
        result ∈ support ((simulateQ signerImpl program).run current) →
          result.2.2.2 = current.2.2 := by
  intro World native routed outer liftLab phase signerImpl alpha program hprogram current result
    hresult
  exact hprogram.holds_of_mem_support_run_simulateQ
    (fun world : World => world.2.2 = current.2.2)
    (fun input hi before' hbefore' after' hafter' =>
      (signer_private_query_preserves_role s input hi before' after' hafter').trans
        hbefore') rfl hresult

private theorem signer_nonce_role_marginal
    (s : FIPS205.core.PkSeed) (message : List Byte) :
  let World := Raw.QueryCache ×
    (CoverageDeferred.S FIPS205.core × Coverage.RoleState FIPS205.core)
  let native := QueryImpl.Stateful.link
    (CoverageDeferred.relative FIPS205.core s (metadataCost true s))
    (Coverage.roleRunImpl FIPS205.core)
  let routed := QueryImpl.Stateful.link (routeLab s) native
  let outer := routed ∘ₛ commonProjection
  let liftLab : QueryImpl Lab (OracleComp A) := fun input =>
    (liftM (A.query (.inl input)) : OracleComp A (Lab.Range input))
  let phase := SigningView.Events.phaseImpl A Message .signer
  let signerImpl := outer ∘ₛ (phase ∘ₛ liftLab)
  ∀ (salt : FIPS205.core.Y) (current : World),
    current.2.1.2.2 = .signer →
      (fun result : FIPS205.core.Y × World => (result.1, result.2.2.2)) <$>
        (signerImpl (.inl (.inr (.inr (salt, message))))).run current =
      (Coverage.roleRunImpl FIPS205.core
        (.inr (.inr (.inr (.inr (salt, message)))))).run current.2.2 := by
  intro World native routed outer liftLab phase signerImpl salt current hphase
  simp only [signerImpl, outer, QueryImpl.apply_compose, QueryImpl.simulateQ_compose]
  dsimp only [liftLab, phase]
  rw [simulateQ_spec_query]
  rw [projected_phase_none .signer (.inl (.inl (.inr (.inr (salt, message))))) rfl,
    simulateQ_spec_query]
  change _ <$> (QueryImpl.Stateful.link (routeLab s)
    (QueryImpl.Stateful.link
      (CoverageDeferred.relative FIPS205.core s (metadataCost true s))
      (Coverage.roleRunImpl FIPS205.core))
        (.inl (.inl (.inl (.inr (.inr (salt, message))))))).run current = _
  rw [linked_native_eq, routed_lab_run]
  simp only [Functor.map_map]
  change (fun result : FIPS205.core.Y ×
        (CoverageDeferred.S FIPS205.core × Coverage.RoleState FIPS205.core) =>
      (result.1, result.2.2)) <$>
        (NativeCounts.nativeImpl FIPS205.core s (metadataCost true s)
          (.inl (.inl (.inr (.inr (salt, message)))))).run (current.2.1, current.2.2) =
      (Coverage.roleRunImpl FIPS205.core
        (.inr (.inr (.inr (.inr (salt, message)))))).run current.2.2
  exact native_nonce_marginal s salt message current.2.1 current.2.2 hphase

private theorem signer_hmsg_role_marginal
    (s : FIPS205.core.PkSeed) (root : FIPS205.core.Y) (message : List Byte) :
  let World := Raw.QueryCache ×
    (CoverageDeferred.S FIPS205.core × Coverage.RoleState FIPS205.core)
  let native := QueryImpl.Stateful.link
    (CoverageDeferred.relative FIPS205.core s (metadataCost true s))
    (Coverage.roleRunImpl FIPS205.core)
  let routed := QueryImpl.Stateful.link (routeLab s) native
  let outer := routed ∘ₛ commonProjection
  let liftLab : QueryImpl Lab (OracleComp A) := fun input =>
    (liftM (A.query (.inl input)) : OracleComp A (Lab.Range input))
  let phase := SigningView.Events.phaseImpl A Message .signer
  let signerImpl := outer ∘ₛ (phase ∘ₛ liftLab)
  ∀ (R : FIPS205.core.Y) (current : World),
    (fun result : FIPS205.Answer × World => (result.1, result.2.2.2)) <$>
      (signerImpl (.inl (.inl (.inr (.inl (.hmsg R s root message)))))).run current =
    (Coverage.roleRunImpl FIPS205.core
      (.inr (.inr (.inl (.inl (.hmsg R s root message)))))).run current.2.2 := by
  intro World native routed outer liftLab phase signerImpl R current
  let event : Ev := .ambient .signer (sourceInput (.inr (.inl (.hmsg R s root message))))
  let afterMarker : World := (current.1,
    ((current.2.1.1,
      (current.2.1.2.1 + metadataCost true s event, .signer)), current.2.2))
  have marker : (routed (.inr event)).run current = pure (PUnit.unit, afterMarker) := by
    change (QueryImpl.Stateful.link (routeLab s)
      (QueryImpl.Stateful.link
        (CoverageDeferred.relative FIPS205.core s (metadataCost true s))
        (Coverage.roleRunImpl FIPS205.core)) (.inr event)).run current = _
    rw [linked_native_eq]
    simpa only [afterMarker, event, CoverageDeferred.phaseCostAux] using
      routed_marker_run s event current
  have source := projected_ambient_source .signer
    (.inl (.inl (.inl (.inr (.inl (.hmsg R s root message)))))) event rfl
  simp only [signerImpl, outer, QueryImpl.apply_compose, QueryImpl.simulateQ_compose]
  dsimp only [liftLab, phase]
  rw [simulateQ_spec_query]
  simp only [source, simulateQ_bind, simulateQ_spec_query, StateT.run_bind,
    marker, pure_bind]
  change _ <$> (QueryImpl.Stateful.link (routeLab s)
    (QueryImpl.Stateful.link
      (CoverageDeferred.relative FIPS205.core s (metadataCost true s))
      (Coverage.roleRunImpl FIPS205.core))
        (.inl (.inl (.inl (.inl (.inr (.inl (.hmsg R s root message)))))))).run
          afterMarker = _
  rw [linked_native_eq, routed_lab_run]
  simp only [Functor.map_map]
  change (fun result : FIPS205.Answer ×
        (CoverageDeferred.S FIPS205.core × Coverage.RoleState FIPS205.core) =>
      (result.1, result.2.2)) <$>
        (NativeCounts.nativeImpl FIPS205.core s (metadataCost true s)
          (.inl (.inl (.inl (.inr (.inl (.hmsg R s root message))))))).run
            (afterMarker.2.1, afterMarker.2.2) =
      (Coverage.roleRunImpl FIPS205.core
        (.inr (.inr (.inl (.inl (.hmsg R s root message)))))).run afterMarker.2.2
  exact native_hmsg_marginal s root R message afterMarker.2.1 afterMarker.2.2 rfl

private theorem signer_internal_role_support
    (s : FIPS205.core.PkSeed) (root : FIPS205.core.Y) (message : List Byte) :
  let key : PK := ⟨s, root⟩
  let World := Raw.QueryCache ×
    (CoverageDeferred.S FIPS205.core × Coverage.RoleState FIPS205.core)
  let native := QueryImpl.Stateful.link
    (CoverageDeferred.relative FIPS205.core s (metadataCost true s))
    (Coverage.roleRunImpl FIPS205.core)
  let routed := QueryImpl.Stateful.link (routeLab s) native
  let outer := routed ∘ₛ commonProjection
  let liftLab : QueryImpl Lab (OracleComp A) := fun input =>
    (liftM (A.query (.inl input)) : OracleComp A (Lab.Range input))
  let phase := SigningView.Events.phaseImpl A Message .signer
  let signerImpl := outer ∘ₛ (phase ∘ₛ liftLab)
  ∀ (R : FIPS205.core.Y) (current : World)
    (result : GeneralScheme.SignatureCore FIPS205.params FIPS205.core × World),
    result ∈ support ((simulateQ signerImpl
      (labSignInternal FIPS205.core s message root R)).run current) →
      ∃ digest afterHmsg,
        (digest, afterHmsg) ∈ support ((Coverage.roleRunImpl FIPS205.core
          (.inr (.inr (Coverage.hmsgPoint FIPS205.core key R message)))).run current.2.2) ∧
        result.2.2.2 = afterHmsg := by
  intro key World native routed outer liftLab phase signerImpl R current result hresult
  let P := fun program : OracleComp Lab
      (GeneralScheme.SignatureCore FIPS205.params FIPS205.core) =>
    AllQueriesSatisfy program (SLHDSA.Security.NativeProvenance.StructuralInput FIPS205.core) →
      ∀ (start : World) (output : GeneralScheme.SignatureCore
          FIPS205.params FIPS205.core × World),
        output ∈ support ((simulateQ signerImpl program).run start) →
          ∃ digest afterHmsg,
            (digest, afterHmsg) ∈ support ((Coverage.roleRunImpl FIPS205.core
              (.inr (.inr (Coverage.hmsgPoint FIPS205.core key R message)))).run
                start.2.2) ∧ output.2.2.2 = afterHmsg
  have body : P (labSignInternal FIPS205.core s message root R) := by
    refine labSignInternal_pred_of_hmsg_bind FIPS205.core
      (Q := fun program => AllQueriesSatisfy program Keygen.NoPublicInput)
      (P := P) (fun _ => allQueriesSatisfy_pure _ _)
      (fun _ _ => allQueriesSatisfy_bind) ?_ ?_ s message root R ?_
    · intro cell
      exact (allQueriesSatisfy_query_iff _ _).2 trivial
    · rintro (derive | node)
      all_goals exact (allQueriesSatisfy_query_iff _ _).2 trivial
    · intro rest hrest structural start output houtput
      change AllQueriesSatisfy
        ((liftM (Lab.query (.inl (.inl (.inr (.inl (.hmsg R s root message)))))) :
            OracleComp Lab (SLHDSA.Bytes FIPS205.params.params.m)) >>= rest)
            (SLHDSA.Security.NativeProvenance.StructuralInput FIPS205.core) at structural
      rw [allQueriesSatisfy_query_bind_iff] at structural
      change output ∈ support ((simulateQ signerImpl
        ((liftM (Lab.query (.inl (.inl (.inr (.inl (.hmsg R s root message)))))) :
          OracleComp Lab (SLHDSA.Bytes FIPS205.params.params.m)) >>= rest)).run start)
            at houtput
      rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind,
        mem_support_bind_iff] at houtput
      obtain ⟨middle, hmiddle, htail⟩ := houtput
      refine ⟨middle.1, middle.2.2.2, ?_, ?_⟩
      · have mapped : (middle.1, middle.2.2.2) ∈ support
            ((fun out : FIPS205.Answer × World => (out.1, out.2.2.2)) <$>
              (signerImpl (.inl (.inl (.inr (.inl (.hmsg R s root message)))))).run start) := by
          exact (support_map
            (fun out : FIPS205.Answer × World => (out.1, out.2.2.2))
            ((signerImpl (.inl (.inl (.inr (.inl (.hmsg R s root message)))))).run
              start)).symm ▸ ⟨middle, hmiddle, rfl⟩
        exact (congrArg
          (fun program : ProbComp (FIPS205.Answer × Coverage.RoleState FIPS205.core) =>
            (middle.1, middle.2.2.2) ∈ support program)
          (signer_hmsg_role_marginal s root message R start)).mp mapped
      · exact signer_private_run_preserves_role s (rest middle.1)
          ((structural.2 middle.1).and (hrest middle.1)) middle.2 output htail
  exact body (SLHDSA.Security.NativeProvenance.lab_internal_sign_structural
    FIPS205.core s message root R)
    current result hresult

private theorem client_signing_preserves_runInv
    (s : FIPS205.core.PkSeed) (root : FIPS205.core.Y) :
  let key : PK := ⟨s, root⟩
  let decodeLog := Settlement.typedLog
  let World := Raw.QueryCache ×
    (CoverageDeferred.S FIPS205.core × Coverage.RoleState FIPS205.core)
  let native := QueryImpl.Stateful.link
    (CoverageDeferred.relative FIPS205.core s (metadataCost true s))
    (Coverage.roleRunImpl FIPS205.core)
  let routed := QueryImpl.Stateful.link (routeLab s) native
  let outer := routed ∘ₛ commonProjection
  let marked := SigningView.Events.viewWithEvents (commonView true s)
  let service : QueryImpl Sign (StateT World ProbComp) := fun request =>
    simulateQ outer (marked.sign key key request)
  ∀ (request : Message) (entries : QueryLog Sign) (before : World),
    Coverage.RunInv FIPS205.core key (decodeLog entries) before.2.2 →
    ∀ (after : Sign.Range request × World),
      after ∈ support ((service request).run before) →
        Coverage.RunInv FIPS205.core key
          (decodeLog (entries ++ [⟨request, after.1⟩])) after.2.2.2 := by
  classical
  intro key decodeLog World native routed outer marked service request entries before hbefore
    after hafter
  let entered : World := (before.1,
    ((before.2.1.1,
      (before.2.1.2.1 + metadataCost true s (.signingAttempt request), .signer)),
        before.2.2))
  have entryRun : (routed (.inr (.signingAttempt request))).run before =
      pure (PUnit.unit, entered) := by
    change (QueryImpl.Stateful.link (routeLab s)
      (QueryImpl.Stateful.link
        (CoverageDeferred.relative FIPS205.core s (metadataCost true s))
        (Coverage.roleRunImpl FIPS205.core)) (.inr (.signingAttempt request))).run before = _
    rw [linked_native_eq]
    simpa only [entered, CoverageDeferred.phaseCostAux] using
      routed_marker_run s (.signingAttempt request) before
  change after ∈ support ((simulateQ outer (marked.sign key key request)).run before)
    at hafter
  rw [QueryImpl.simulateQ_compose,
    Guarded.projected_callback_eq, simulateQ_bind, StateT.run_bind,
    simulateQ_spec_query, entryRun, pure_bind] at hafter
  cases framed : (External.encodePureMessage request.context request.message).toOption with
  | none =>
    simp only [commonView_eq_rejectingEncoding, ite_true, SigningView.rejectingEncoding_sign,
      framed,
      simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hafter
    subst after
    have rejectedLog : decodeLog (entries ++ [⟨request, none⟩]) = decodeLog entries := by
      exact Settlement.typedLog_append_rejected entries request
    simpa only [rejectedLog, entered] using hbefore
  | some message =>
    let liftLab : QueryImpl Lab (OracleComp A) := fun input =>
      (liftM (A.query (.inl input)) : OracleComp A (Lab.Range input))
    let phase := SigningView.Events.phaseImpl A Message .signer
    let signerImpl := outer ∘ₛ (phase ∘ₛ liftLab)
    simp only [commonView_eq_rejectingEncoding, ite_true, SigningView.rejectingEncoding_sign,
      framed,
      SignatureAlg.map_sign, simulateQ_map, StateT.run_map, support_map] at hafter
    obtain ⟨signed, hsigned, rfl⟩ := hafter
    have signed_support : signed ∈ support ((simulateQ signerImpl
        ((labScheme FIPS205.core (fun pk => pure pk.pkSeed) s).sign key key message)).run
          entered) := by
      simpa only [signerImpl, outer, liftLab, phase, QueryImpl.simulateQ_compose] using hsigned
    change signed ∈ support ((simulateQ signerImpl
      (((liftM (Lab.query (.inl (.inr (.inr (s, message)))))) :
          OracleComp Lab FIPS205.core.Y) >>= fun R =>
        labSignInternal FIPS205.core s message root R)).run entered) at signed_support
    rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind,
      mem_support_bind_iff] at signed_support
    obtain ⟨nonceOut, hnonce, hinternal⟩ := signed_support
    have nonceRole : (nonceOut.1, nonceOut.2.2.2) ∈ support
        ((Coverage.roleRunImpl FIPS205.core
          (.inr (.inr (.inr (.inr (s, message)))))).run before.2.2) := by
      rw [← signer_nonce_role_marginal s message (s : FIPS205.core.Y) entered rfl,
        support_map]
      exact ⟨nonceOut, hnonce, rfl⟩
    obtain ⟨digest, afterHmsg, hHmsg, roleEq⟩ :=
      signer_internal_role_support s root message nonceOut.1 nonceOut.2 signed hinternal
    have sourceSignature : signed.1 ∈ support
        (labSignInternal FIPS205.core s message root nonceOut.1) :=
      support_simulateQ_run'_subset signerImpl _ nonceOut.2 (by
        rw [StateT.run'_eq, support_map]
        exact ⟨signed, hinternal, rfl⟩)
    have randomness : signed.1.randomness = nonceOut.1 := by
      simp only [labSignInternal, mem_support_bind_iff, support_pure,
        Set.mem_singleton_iff] at sourceSignature
      obtain ⟨_, _, _, _, _, _, _, _, signatureEq⟩ := sourceSignature
      exact congrArg (fun signature : GeneralScheme.SignatureCore FIPS205.params
        FIPS205.core => signature.randomness) signatureEq
    have appended := Coverage.runInv_after_signer_nonce_hmsg FIPS205.core key
      (decodeLog entries) before.2.2 nonceOut.2.2.2 afterHmsg s nonceOut.1 message digest
      signed.1 hbefore nonceRole hHmsg randomness
    change Coverage.RunInv FIPS205.core key
      (decodeLog (entries ++ [⟨request, some (SLHDSA.encodeSignature FIPS205.params
        (SLHDSA.Concrete.shakeWireCodec FIPS205.params.params) signed.1)⟩])) signed.2.2.2
    rw [roleEq]
    have decoded := Settlement.typedLog_append_accepted entries request message _ signed.1 framed
      (Settlement.parsed_encoded signed.1)
    change decodeLog (entries ++ [⟨request, some (SLHDSA.encodeSignature FIPS205.params
      (SLHDSA.Concrete.shakeWireCodec FIPS205.params.params) signed.1)⟩]) =
        decodeLog entries ++ [⟨message, signed.1⟩] at decoded
    rw [decoded]
    exact appended

private theorem native_client_preserves_runInv
    (s : FIPS205.core.PkSeed) (root : FIPS205.core.Y)
    (adv : Game.Adversary FIPS205.Answer PK)
    (raw : Raw.QueryCache) (state : CoverageDeferred.S FIPS205.core)
    (role : Coverage.RoleState FIPS205.core) (log : QueryLog Sign) :
    let key : PK := ⟨s, root⟩
    let decodeLog := Settlement.typedLog
    let marked := SigningView.Events.viewWithEvents (commonView true s)
    let client := simulateQ commonProjection
      (marked.runWithSigningOracle key key
        (SigningView.Events.mainWithEvents (commonMain adv) key))
    let handler := QueryImpl.Stateful.link (routeLab s)
      (QueryImpl.Stateful.link
        (CoverageDeferred.relative FIPS205.core s (metadataCost true s))
        (Coverage.roleRunImpl FIPS205.core))
    Coverage.RunInv FIPS205.core key (decodeLog log) role →
      ∀ out ∈ support ((simulateQ handler client).run (raw, (state, role))),
        Coverage.RunInv FIPS205.core key (decodeLog (log ++ out.1.2)) out.2.2.2 := by
  classical
  dsimp only
  intro hinitial out hout
  let key : PK := ⟨s, root⟩
  let decodeLog := Settlement.typedLog
  let World := Raw.QueryCache ×
    (CoverageDeferred.S FIPS205.core × Coverage.RoleState FIPS205.core)
  let marked := SigningView.Events.viewWithEvents (commonView true s)
  let native := QueryImpl.Stateful.link
    (CoverageDeferred.relative FIPS205.core s (metadataCost true s))
    (Coverage.roleRunImpl FIPS205.core)
  let routed := QueryImpl.Stateful.link (routeLab s) native
  let outer := routed ∘ₛ commonProjection
  let ambient := outer ∘ₛ SigningView.Events.phaseImpl A Message .adversary
  let service : QueryImpl Sign (StateT World ProbComp) := fun request =>
    simulateQ outer (marked.sign key key request)
  let mixed : QueryImpl (A + Sign) (WriterT (QueryLog Sign) (StateT World ProbComp)) :=
    QueryImpl.add (ambient.liftTarget _) service.withLogging
  let I : QueryLog Sign → World → Prop := fun entries world =>
    Coverage.RunInv FIPS205.core key (decodeLog entries) world.2.2
  let Allowed : A.Domain → Prop
    | .inl (.inl (.inl (.inl _))) => True
    | .inr _ => True
    | _ => False
  have allowed : AllQueriesSatisfy (commonMain adv key)
      (Sum.elim Allowed (fun _ => True)) := by
    unfold commonMain
    refine (allQueriesSatisfy_of_forall (fun _ => True.intro)
      (Game.Counted.externalMain adv key)).simulateQ ?_
    rintro ((sample | bytes) | request) _
    · exact (allQueriesSatisfy_query_iff (spec := A + Sign) _ _).2 trivial
    · exact (allQueriesSatisfy_query_iff (spec := A + Sign) _ _).2 trivial
    · exact (allQueriesSatisfy_query_iff (spec := A + Sign) _ _).2 trivial
  have ambient_step (input : A.Domain) (hi : Allowed input)
      (entries : QueryLog Sign) (before : World) (hbefore : I entries before)
      (after : A.Range input × World)
      (hafter : after ∈ support ((ambient input).run before)) : I entries after.2 := by
    exact client_ambient_preserves_runInv s root input hi entries before hbefore after hafter
  have signing_step (request : Message) (entries : QueryLog Sign)
      (before : World) (hbefore : I entries before) (after : Sign.Range request × World)
      (hafter : after ∈ support ((service request).run before)) :
      I (entries ++ [⟨request, after.1⟩]) after.2 := by
    exact client_signing_preserves_runInv s root request entries before hbefore after hafter
  have service_square : out ∈ support
      ((simulateQ mixed (commonMain adv key)).run.run (raw, (state, role))) := by
    have square := SigningView.simulateQ_runWithSigningOracle_mapClient
      (SigningView.Events.phaseImpl A Message .adversary) outer marked key key (commonMain adv key)
    rw [← QueryImpl.simulateQ_compose] at hout
    exact (congrArg (fun action => action.run (raw, (state, role))) square) ▸ hout
  exact QueryImpl.holds_of_mem_support_run_add_stateful_withLogging
    ambient service Allowed I ambient_step signing_step (commonMain adv key) allowed
    log (raw, (state, role)) hinitial out service_square

/-- Every nonaborted cold native transcript covers its decoded signing log at its retained key.
The complete role state is the one returned by the actual run, including its unread tapes,
class counters and hit set. The assertion imposes no freshness or winning condition. -/
theorem native_nonabort_terminal_runInv
    (s : FIPS205.core.PkSeed) (adv : Game.Adversary FIPS205.Answer PK)
    (reserve : Bool) (caps : Nat × Nat)
    (fallback : (input : LabCommon.Domain) → LabCommon.Range input)
    (leftTape rightTape : List HashOutput)
    (terminal : NativeTerminal)
    (hterminal : terminal ∈ support
      (nativeRun s adv reserve caps fallback leftTape rightTape))
    (hnotAborted : terminal.2.2.2 = false) :
    let typedLog := Settlement.typedLog terminal.1.2.rawLog
    Coverage.RunInv FIPS205.core terminal.1.1.1 typedLog terminal.2.1.2 := by
  classical
  dsimp only
  let World := Raw.QueryCache ×
    (CoverageDeferred.S FIPS205.core × Coverage.RoleState FIPS205.core)
  let native := QueryImpl.Stateful.link
    (CoverageDeferred.relative FIPS205.core s (metadataCost true s))
    (Coverage.roleRunImpl FIPS205.core)
  let routed := QueryImpl.Stateful.link (routeLab s) native
  let outer := routed ∘ₛ commonProjection
  let marked := SigningView.Events.viewWithEvents (commonView true s)
  have verification_frame (key : PK)
      (log : QueryLog (List Byte →ₒ GeneralScheme.SignatureCore FIPS205.params FIPS205.core))
      (request : Message) (wire : List Byte) (before : World)
      (hinv : Coverage.RunInv FIPS205.core key log before.2.2)
      (after : Bool × World)
      (hafter : after ∈ support
        ((simulateQ outer (marked.verify key request wire)).run before)) :
      Coverage.RunInv FIPS205.core key log after.2.2.2 := by
    let liftPublic : QueryImpl (publicHashSpec FIPS205.core) (OracleComp A) := fun point =>
      (liftM (A.query (.inl (.inl (.inl (.inr (.inl point)))))) :
        OracleComp A ((publicHashSpec FIPS205.core).Range point))
    let phase := SigningView.Events.phaseImpl A Message .verification
    let impl := outer ∘ₛ (phase ∘ₛ liftPublic)
    have step (point : (publicHashSpec FIPS205.core).Domain)
        (current : World) (hcurrent : Coverage.RunInv FIPS205.core key log current.2.2)
        (result : (publicHashSpec FIPS205.core).Range point × World)
        (hresult : result ∈ support ((impl point).run current)) :
        Coverage.RunInv FIPS205.core key log result.2.2.2 := by
      let event : Ev := .ambient .verification (sourceInput (.inr (.inl point)))
      let marker : CoverageDeferred.S FIPS205.core :=
        (current.2.1.1, (current.2.1.2.1 + metadataCost true s event, .verification))
      have normal : (impl point).run current =
          (fun output : (publicHashSpec FIPS205.core).Range point ×
              (CoverageDeferred.S FIPS205.core × Coverage.RoleState FIPS205.core) =>
            (output.1, (current.1, output.2))) <$>
            (native (.inl (.inl (.inl (.inr (.inl point)))))).run
              (marker, current.2.2) := by
        let labPoint : Lab.Domain := .inl (.inl (.inr (.inl point)))
        have source := projected_ambient_source .verification (.inl labPoint) event
          (by cases point <;> rfl)
        have mark : (routed (.inr event)).run current =
            pure (PUnit.unit, (current.1, (marker, current.2.2))) := by
          dsimp only [routed, native]
          rw [linked_native_eq]
          simpa only [marker, event, CoverageDeferred.phaseCostAux] using
            routed_marker_run s event current
        simp only [impl, outer, QueryImpl.apply_compose, QueryImpl.simulateQ_compose]
        dsimp only [phase, liftPublic]
        rw [simulateQ_spec_query]
        change (simulateQ routed (simulateQ commonProjection
          (SigningView.Events.phaseImpl A Message .verification (.inl labPoint)))).run current = _
        rw [source]
        simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mark, pure_bind]
        change (QueryImpl.Stateful.link (routeLab s) _ (.inl (.inl labPoint))).run
          (current.1, (marker, current.2.2)) = _
        dsimp only [native, routed]
        rw [linked_native_eq, routed_lab_run]
        rfl
      rw [normal, support_map] at hresult
      obtain ⟨output, houtput, rfl⟩ := hresult
      have sameNative : native =
          NativeCounts.nativeImpl FIPS205.core s (metadataCost true s) := linked_native_eq s
      rw [sameNative] at houtput
      exact (native_public_preserves s .verification (Or.inr rfl)
        key log (.inl point) marker current.2.2 rfl hcurrent output houtput).1
    cases framed : (External.encodePureMessage request.context request.message).toOption with
    | none =>
      simp only [marked, SigningView.Events.viewWithEvents, commonView_eq_rejectingEncoding,
        ite_true,
        SigningView.rejectingEncoding_verify, framed, simulateQ_pure,
        StateT.run_pure, support_pure, Set.mem_singleton_iff] at hafter
      subst after
      exact hinv
    | some message =>
      cases decoded : (SLHDSA.decodeSignature FIPS205.params
          (SLHDSA.Concrete.shakeWireCodec FIPS205.params.params) wire).toOption with
      | none =>
        simp only [marked, SigningView.Events.viewWithEvents, commonView_eq_rejectingEncoding,
          ite_true,
          SigningView.rejectingEncoding_verify, framed, decoded, simulateQ_pure,
          StateT.run_pure, support_pure, Set.mem_singleton_iff] at hafter
        subst after
        exact hinv
      | some signature =>
        let publicHom := HasQuery.QueryHom.ofSimulateQ
          (spec := publicHashSpec FIPS205.core) (m := OracleComp Lab)
        let labLift : QueryImpl Lab (OracleComp A) := fun input =>
          (liftM (A.query (.inl input)) : OracleComp A (Lab.Range input))
        have factor (body : OracleComp (publicHashSpec FIPS205.core) Bool) :
            simulateQ labLift (publicHom.toFun Bool body) = simulateQ liftPublic body := by
          change simulateQ labLift (simulateQ (HasQuery.toQueryImpl
            (spec := publicHashSpec FIPS205.core) (m := OracleComp Lab)) body) = _
          rw [← QueryImpl.simulateQ_compose]
          congr 1
        have actual : after ∈ support ((simulateQ impl
            (GeneralScheme.verifyInternalM FIPS205.params FIPS205.core message signature key :
              OracleComp (publicHashSpec FIPS205.core) Bool)).run before) := by
          simp only [marked, SigningView.Events.viewWithEvents, commonView_eq_rejectingEncoding,
            ite_true,
            SigningView.rejectingEncoding_verify, framed, decoded, SignatureAlg.map_verify,
            labScheme, ← GeneralScheme.verifyInternalM_natural FIPS205.params
              FIPS205.core publicHom] at hafter
          change after ∈ support ((simulateQ outer (simulateQ phase (simulateQ labLift
            (publicHom.toFun Bool (GeneralScheme.verifyInternalM FIPS205.params FIPS205.core
              message signature key))))).run before) at hafter
          rw [factor] at hafter
          simpa only [impl, QueryImpl.simulateQ_compose] using hafter
        have body := allQueriesSatisfy_of_forall (fun _ => True.intro)
          (GeneralScheme.verifyInternalM FIPS205.params FIPS205.core
            message signature key : OracleComp (publicHashSpec FIPS205.core) Bool)
        exact body.holds_of_mem_support_run_simulateQ
            (fun current : World => Coverage.RunInv FIPS205.core key log current.2.2)
            (fun point _ current hcurrent result hresult => step point current hcurrent
              result hresult) hinv actual
  let _ : MonadLiftT (OracleComp.{0, 0, 0} LabCommon)
      (StateT PUnit.{1} (OracleComp.{0, 0, 0} LabCommon)) :=
    ⟨fun action => StateT.lift action⟩
  let decodeLog := Settlement.typedLog
  let tapes : (j : Coverage.TapeClass) → List (Coverage.tapeClassRange FIPS205.core j)
    | .signer => leftTape.map Bridge.answerEquiv
    | .forger => rightTape.map Bridge.answerEquiv
    | .other => []
  let initialRole : Coverage.RoleState FIPS205.core :=
    ((∅, tapes), (AnswerTape.ClassPos.init, ∅))
  let initialState : CoverageDeferred.S FIPS205.core :=
    (((∅, ∅), []), (0, .keygen))
  let charge := Sum.elim (fun _ : A.Domain => (0, 0)) (policy reserve s)
  let guard := QueryImpl.guardQueryBudget caps charge routed fallback
  let reshape {alpha : Type} := fun z :
      (((alpha × (PUnit × Paid)) × Raw.QueryCache) ×
        CoverageDeferred.S FIPS205.core) × Coverage.RoleState FIPS205.core =>
    (z.1.1.1.1, ((z.1.1.2, (z.1.2, z.2)), z.1.1.1.2.2))
  have front {alpha : Type} (program : OracleComp LabCommon alpha)
      (before : World × Paid) :
      reshape <$> (simulateQ (Coverage.roleRunImpl FIPS205.core)
        ((simulateQ (CoverageDeferred.relative FIPS205.core s (metadataCost true s))
          ((simulateQ (routeLab s)
            ((simulateQ (QueryImpl.guardQueryBudget caps charge
              ((QueryImpl.id' LabCommon).liftTarget (StateT PUnit (OracleComp LabCommon)))
              fallback) program).run (PUnit.unit, before.2))).run before.1.1)).run
                before.1.2.1)).run before.1.2.2 =
        (simulateQ guard program).run before := by
    simpa only [reshape, guard, routed, native, charge] using
      Provenance.native_guarded_frontend s reserve caps fallback program
        before.1.1 before.1.2.1 before.1.2.2 before.2
  simp only [nativeRun, bind_pure_comp, support_map] at hterminal
  obtain ⟨nested, hnested, rfl⟩ := hterminal
  let flat := reshape nested
  have hflat : flat ∈ support ((simulateQ guard (commonSource true s adv)).run
      ((∅, (initialState, initialRole)), ((0, 0), false))) := by
    rw [← front (commonSource true s adv) _, support_map]
    exact ⟨nested, hnested, rfl⟩
  have flatNotAborted : flat.2.2.2 = false := hnotAborted
  have finalInv : Coverage.RunInv FIPS205.core flat.1.1.1
      (decodeLog flat.1.2.rawLog) flat.2.1.2.2 := by
    let keygenSource := simulateQ commonProjection marked.keygen
    let continuation := fun keys : PK × PK => simulateQ commonProjection (do
      let (forgery, rawLog) ← marked.runWithSigningOracle keys.1 keys.2
        (SigningView.Events.mainWithEvents (commonMain adv) keys.1)
      let verified ← marked.verify keys.1 forgery.1 forgery.2
      pure (keys, (⟨forgery, rawLog, verified⟩ : RawOutcome)))
    have source : commonSource true s adv = keygenSource >>= continuation := by
      simp only [commonSource, SigningView.Events.fullExperiment,
        simulateQ_bind, keygenSource, continuation, marked]
    rw [source, simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hflat
    obtain ⟨keys, hkeys, hcontinuation⟩ := hflat
    rw [← front keygenSource _, support_map] at hkeys
    obtain ⟨cold, hcold, keyShape⟩ := hkeys
    have prefixLaw := native_cold_keygen_role_factorization s reserve caps fallback initialRole
    dsimp only at prefixLaw
    rw [prefixLaw, support_map] at hcold
    obtain ⟨privateKeygen, hprivate, coldShape⟩ := hcold
    simp only [labScheme, simulateQ_bind, StateT.run_bind, mem_support_bind_iff,
      simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hprivate
    obtain ⟨rootState, hroot, privateShape⟩ := hprivate
    rw [← keyShape, ← coldShape, privateShape] at hcontinuation
    dsimp only [reshape] at hcontinuation
    let key : PK := ⟨s, rootState.1⟩
    let afterKeygen : World := (∅, ((rootState.2, (0, .keygen)), initialRole))
    have sourceContinuation : (flat.1, flat.2.1) ∈ support
        ((simulateQ routed (continuation (key, key))).run afterKeygen) := by
      exact mem_support_source_of_guard_not_aborted caps charge routed fallback
        (continuation (key, key)) afterKeygen flat hcontinuation flatNotAborted
    simp only [continuation, simulateQ_bind, simulateQ_pure, StateT.run_bind,
      StateT.run_pure, mem_support_bind_iff, support_pure, Set.mem_singleton_iff]
      at sourceContinuation
    obtain ⟨client, hclient, verified, hverified, finalShape⟩ := sourceContinuation
    have initialInv : Coverage.RunInv FIPS205.core key (decodeLog []) initialRole := by
      exact Coverage.RunInv.init FIPS205.core key tapes
    have afterClient := native_client_preserves_runInv s rootState.1 adv
      afterKeygen.1 afterKeygen.2.1 afterKeygen.2.2 [] initialInv client hclient
    have afterVerifier := verification_frame key (decodeLog client.1.2)
      client.1.1.1 client.1.1.2 client.2 (by simpa only [List.nil_append] using afterClient)
      verified (by simpa only [← QueryImpl.simulateQ_compose] using hverified)
    have keyEq : flat.1.1.1 = key := congrArg (fun result => result.1.1.1) finalShape
    have logEq : flat.1.2.rawLog = client.1.2 :=
      congrArg (fun result => result.1.2.rawLog) finalShape
    have roleEq : flat.2.1.2.2 = verified.2.2.2 :=
      congrArg (fun result => result.2.2.2) finalShape
    simpa only [keyEq, logEq, roleEq] using afterVerifier
  exact finalInv

/-! ## Deferred execution and completed graph support -/

end SLHDSA.SHAKE128s.Bridge.SharedExperiment.Native

end
