/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module

public import HashSig.SLHDSA.Security.CoveragePotential
public import HashSig.SLHDSA.Security.CoverageCountCausality
public import HashSig.SLHDSA.SHAKE128s.Proof.ActualWork.Coverage.Keygen
public import HashSig.SLHDSA.Security.CoverageRun
public import HashSig.SLHDSA.Security.RomSchemeUnion
public import HashSig.SLHDSA.SHAKE128s.Bridge.Encodings
public import HashSig.SLHDSA.SHAKE128s.Proof.UsedPrefixCoverage
public import VCVio.OracleComp.QueryTracking.ExpectedQueryCount
public import VCVio.OracleComp.EvalDist.Measure
public import VCVio.OracleComp.QueryTracking.LoggingOracle.Core
public import HashSig.SLHDSA.Security.NativeRelative
public import HashSig.SLHDSA.SHAKE128s.Bridge.SharedExperiment.Pure
import all HashSig.SLHDSA.SHAKE128s.Proof.ActualWork.Work.Signing
import HashSig.SLHDSA.SHAKE128s.Proof.ActualWork.Transcript.Program
import VCVio.OracleComp.SimSemantics.StateT.StateProjection
import VCVio.OracleComp.EvalDist.Sum
import VCVio.OracleComp.QueryTracking.SubSpec
import all HashSig.SLHDSA.Security.CoverageRun
import all VCVio.OracleComp.QueryTracking.RandomOracle.ClassIndexedTape
import all VCVio.OracleComp.QueryTracking.RandomOracle.ClassIndexedTape.Position
import VCVio.OracleComp.QueryTracking.QueryBound.Simulation
import VCVio.OracleComp.SimSemantics.StateT.PreservesInv

/-! # Single- and paired-query credits for the actual public key

Single-slot credit, shared-nonce pair credit and future-cell causality specialize to the
complete existing role experiment. All complete counts, consumed counts and output fields
remain in that computation. The final credit statement has no additional resource premise.
-/

public section
open OracleComp OracleSpec SignatureAlg MeasureTheory
open scoped ENNReal
open SLHDSA.Security SLHDSA.SHAKE128s
open SLHDSA.SHAKE128s.DigestTape SLHDSA.SHAKE128s.NoticingTape

namespace SLHDSA.SHAKE128s.ConsumedPrefix

/-- The typed forgery outcome and final state of the role-indexed hash tapes. -/
abbrev Outcome := DeriveOutcome FIPS205.core × Coverage.RoleState FIPS205.core

/-- A typed forgery adversary for a fixed public seed and deterministic signing randomizer. -/
abbrev Adversary (seed : FIPS205.core.PkSeed) :=
  UnforgeableAdversary (romScheme FIPS205.core (Equiv.refl _)
    (fun pk => pure pk.pkSeed) (pure seed))

/-- The two digest blocks retain their respective signer and forger classes. -/
@[expose] def tapes (left right : List HashOutput) :
    (which : Coverage.TapeClass) → List (Coverage.tapeClassRange FIPS205.core which)
  | .signer => left.map Bridge.answerEquiv
  | .forger => right.map Bridge.answerEquiv
  | .other => []

/-- The complete typed experiment against two fixed digest blocks. -/
noncomputable abbrev run (seed : FIPS205.core.PkSeed) (adv : Adversary seed)
    (left right : List HashOutput) : ProbComp Outcome :=
  Coverage.roleRun FIPS205.core adv seed (tapes left right)

/-- A message-hash point for the returned public key fired at this position of the forger tape. -/
abbrev fired (outcome : Outcome) (index : Nat) : Prop :=
  Coverage.ActualKeyPotential.Fired FIPS205.core outcome.1.pk outcome.2 index
end SLHDSA.SHAKE128s.ConsumedPrefix

/-! ## Query discipline of the original rejecting continuation -/

namespace SLHDSA.SHAKE128s.MarkedClient
open OracleComp OracleSpec SignatureAlg
open SLHDSA SLHDSA.Security SLHDSA.SHAKE128s
open SLHDSA.SHAKE128s.Bridge.SharedExperiment
open Guarded (PK Raw H R Ev O Native Common Paid Meta Lab A LabCommon Full Sign RawOutcome
  encoding policy selectedRaw metadataCost aux partialView commonView commonMain commonEvent
  commonProjection routeLab commonView_eq_rejectingEncoding projected_lab_phase_queries
  projected_callback_eq)
open Coverage.ActualKeyPotential

private def Salted (salt : FIPS205.core.PkSeed) : Lab.Domain → Prop
  | .inl (.inr (.inr (value, _))) => value = salt
  | _ => True

private def SaltedCommon (salt : FIPS205.core.PkSeed) : LabCommon.Domain → Prop :=
  Sum.elim (Sum.elim (Salted salt) (fun _ => True)) (fun _ => True)

private theorem internal_sign_salted
    (seed salt : FIPS205.core.PkSeed) (root R : FIPS205.core.Y) (message : List Byte) :
    AllQueriesSatisfy (labSignInternal FIPS205.core seed message root R) (Salted salt) := by
  refine (SLHDSA.Security.NativeProvenance.lab_internal_sign_structural
    FIPS205.core seed message root R).mono ?_
  rintro (((sample | point) | (secret | nonce)) | (touch | node)) hi
  · trivial
  · trivial
  · trivial
  · exact hi.elim
  · trivial
  · trivial

private theorem lab_sign_salted
    (seed : FIPS205.core.PkSeed) (pk sk : PK) (message : List Byte) :
    AllQueriesSatisfy
      ((labScheme FIPS205.core (fun key => pure key.pkSeed) seed).sign pk sk message)
      (Salted pk.pkSeed) := by
  change AllQueriesSatisfy
    ((query (spec := Lab) (.inl (.inr (.inr (pk.pkSeed, message))))) >>= fun R =>
      labSignInternal FIPS205.core seed message sk.pkRoot R) (Salted pk.pkSeed)
  exact allQueriesSatisfy_bind ((allQueriesSatisfy_query_iff _ _).2 rfl)
    fun R => internal_sign_salted seed pk.pkSeed sk.pkRoot R message

private theorem lab_verify_salted
    (seed : FIPS205.core.PkSeed) (pk : PK) (message : List Byte)
    (signature : GeneralScheme.SignatureCore FIPS205.params FIPS205.core) :
    AllQueriesSatisfy
      ((labScheme FIPS205.core (fun key => pure key.pkSeed) seed).verify pk message signature)
      (Salted pk.pkSeed) := by
  change AllQueriesSatisfy
    (GeneralScheme.verifyInternalM FIPS205.params FIPS205.core message signature pk :
      OracleComp Lab Bool) (Salted pk.pkSeed)
  refine GeneralScheme.verifyInternalM_pred (m := OracleComp Lab)
    (Q := fun p => AllQueriesSatisfy p (Salted pk.pkSeed))
    (fun _ => allQueriesSatisfy_pure _ _) (fun _ _ => allQueriesSatisfy_bind)
    FIPS205.core message signature pk ?_ ?_
  · intro _ _ _
    exact (allQueriesSatisfy_query_iff _ _).2 trivial
  · exact (allQueriesSatisfy_query_iff _ _).2 trivial

private theorem projected_sign_salted
    (seed : FIPS205.core.PkSeed) (pk sk : PK) (request : Message) :
    AllQueriesSatisfy
      (simulateQ commonProjection
        (simulateQ (SigningView.Events.phaseImpl A Message .signer)
          ((commonView true seed).sign pk sk request))) (SaltedCommon pk.pkSeed) := by
  cases hframe : (External.encodePureMessage request.context request.message).toOption with
  | none =>
    simpa only [commonView_eq_rejectingEncoding, ite_true, SigningView.rejectingEncoding_sign,
      hframe, simulateQ_pure] using
        (allQueriesSatisfy_pure (spec := LabCommon) none (SaltedCommon pk.pkSeed))
  | some message =>
    let encodeReply := some ∘ SLHDSA.encodeSignature FIPS205.params
      (SLHDSA.Concrete.shakeWireCodec FIPS205.params.params)
    have hencoded : AllQueriesSatisfy
        (encodeReply <$> ((labScheme FIPS205.core (fun key => pure key.pkSeed) seed).sign
          pk sk message)) (Salted pk.pkSeed) := by
      simpa only [map_eq_bind_pure_comp, Function.comp_def] using
        (allQueriesSatisfy_bind (lab_sign_salted seed pk sk message)
          (fun _ => allQueriesSatisfy_pure _ _))
    have h := projected_lab_phase_queries .signer (Salted pk.pkSeed)
      (encodeReply <$> ((labScheme FIPS205.core (fun key => pure key.pkSeed) seed).sign
        pk sk message)) hencoded
    simpa only [commonView_eq_rejectingEncoding, ite_true, SigningView.rejectingEncoding_sign,
      hframe, SignatureAlg.map_sign, simulateQ'_apply, simulateQ_map, encodeReply,
      SaltedCommon] using h

private theorem projected_verify_salted
    (seed : FIPS205.core.PkSeed) (pk : PK) (request : Message) (wire : List Byte) :
    AllQueriesSatisfy
      (simulateQ commonProjection
        ((SigningView.Events.viewWithEvents (commonView true seed)).verify pk request wire))
      (SaltedCommon pk.pkSeed) := by
  cases hframe : (External.encodePureMessage request.context request.message).toOption with
  | none =>
    simpa only [SigningView.Events.viewWithEvents, commonView_eq_rejectingEncoding, ite_true,
      SigningView.rejectingEncoding_verify, hframe, simulateQ_pure] using
      (allQueriesSatisfy_pure (spec := LabCommon) false (SaltedCommon pk.pkSeed))
  | some message =>
    cases hdecode : (SLHDSA.decodeSignature FIPS205.params
        (SLHDSA.Concrete.shakeWireCodec FIPS205.params.params) wire).toOption with
    | none =>
      simpa only [SigningView.Events.viewWithEvents, commonView_eq_rejectingEncoding, ite_true,
        SigningView.rejectingEncoding_verify, hframe, hdecode, simulateQ_pure] using
        (allQueriesSatisfy_pure (spec := LabCommon) false (SaltedCommon pk.pkSeed))
    | some signature =>
      have h := projected_lab_phase_queries .verification (Salted pk.pkSeed)
        ((labScheme FIPS205.core (fun key => pure key.pkSeed) seed).verify pk message signature)
        (lab_verify_salted seed pk message signature)
      simpa only [SigningView.Events.viewWithEvents, commonView_eq_rejectingEncoding, ite_true,
        SigningView.rejectingEncoding_verify, hframe, hdecode,
        SignatureAlg.map_verify, simulateQ'_apply, SaltedCommon] using h

private theorem projected_callback_salted
    (seed : FIPS205.core.PkSeed) (pk sk : PK) (request : Message) :
    AllQueriesSatisfy
      (simulateQ commonProjection
        ((SigningView.Events.viewWithEvents (commonView true seed)).sign pk sk request))
      (SaltedCommon pk.pkSeed) := by
  rw [projected_callback_eq]
  exact allQueriesSatisfy_bind
    ((allQueriesSatisfy_query_iff (spec := LabCommon) _ _).2 trivial)
    (fun _ => projected_sign_salted seed pk sk request)

private theorem projected_client_salted
    (seed : FIPS205.core.PkSeed) (pk sk : PK)
    (adv : Game.Adversary FIPS205.Answer PK) :
    let marked := SigningView.Events.viewWithEvents (commonView true seed)
    AllQueriesSatisfy
      (simulateQ commonProjection
        (marked.runWithSigningOracle pk sk
          (SigningView.Events.mainWithEvents (commonMain adv) pk))) (SaltedCommon pk.pkSeed) := by
  dsimp only
  rw [SigningCounts.actual_client_eq]
  refine SigningCounts.clientHandler_preserves
    (fun p => AllQueriesSatisfy p (SaltedCommon pk.pkSeed))
    (fun _ => allQueriesSatisfy_pure _ _) (fun hp hf => allQueriesSatisfy_bind hp hf)
    ?_ (projected_callback_salted seed pk sk) _
  rintro (n | raw) <;>
    simp only [SigningCounts.clientAmbient, SigningView.Events.phaseImpl,
      QueryImpl.preInsert_apply, SigningView.Events.emit, simulateQ_bind,
      simulateQ_spec_query, commonProjection, commonEvent, Guarded.sourceInput, QueryImpl.add] <;>
    exact allQueriesSatisfy_bind ((allQueriesSatisfy_query_iff _ _).2 trivial)
      (fun _ => (allQueriesSatisfy_query_iff _ _).2 trivial)

private theorem marked_rejecting_postkeygen_good_queries
    (seed : FIPS205.core.PkSeed) (pk sk : PK)
    (adv : Game.Adversary FIPS205.Answer PK)
    (reserve : Bool) (caps : Nat × Nat)
    (fallback : (input : LabCommon.Domain) → LabCommon.Range input)
    (raw : Raw.QueryCache) (state : CoverageDeferred.S FIPS205.core) (paid : Paid) :
    let marked := SigningView.Events.viewWithEvents (commonView true seed)
    let suffix := simulateQ commonProjection (do
      let (forgery, rawLog) ← marked.runWithSigningOracle pk sk
        (SigningView.Events.mainWithEvents (commonMain adv) pk)
      let verified ← marked.verify pk forgery.1 forgery.2
      return ((pk, sk), (⟨forgery, rawLog, verified⟩ : RawOutcome)))
    letI : MonadLiftT (OracleComp LabCommon) (StateT PUnit (OracleComp LabCommon)) :=
      ⟨fun action => StateT.lift action⟩
    let forwarder := (QueryImpl.id' LabCommon).liftTarget
      (StateT PUnit (OracleComp LabCommon))
    let guarded := (simulateQ (QueryImpl.guardQueryBudget caps
      (Sum.elim (fun _ : A.Domain => (0, 0)) (policy reserve seed)) forwarder fallback)
      suffix).run (PUnit.unit, paid)
    AllQueriesSatisfy
      ((simulateQ (CoverageDeferred.relative FIPS205.core seed (metadataCost true seed))
        ((simulateQ (routeLab seed) guarded).run raw)).run state)
      (Coverage.ActualKeyPotential.GoodQuery FIPS205.core pk (fun pk => pk.pkSeed)) := by
  let _ : MonadLiftT (OracleComp.{0, 0, 0} LabCommon)
      (StateT PUnit.{1} (OracleComp.{0, 0, 0} LabCommon)) :=
    ⟨fun action => StateT.lift action⟩
  classical
  dsimp only
  let marked := SigningView.Events.viewWithEvents (commonView true seed)
  let suffix := simulateQ commonProjection (do
    let (forgery, rawLog) ← marked.runWithSigningOracle pk sk
      (SigningView.Events.mainWithEvents (commonMain adv) pk)
    let verified ← marked.verify pk forgery.1 forgery.2
    return ((pk, sk), (⟨forgery, rawLog, verified⟩ : RawOutcome)))
  let forwarder := (QueryImpl.id' LabCommon).liftTarget
    (StateT PUnit (OracleComp LabCommon))
  let charge := Sum.elim (fun _ : A.Domain => (0, 0)) (policy reserve seed)
  let guard := QueryImpl.guardQueryBudget caps charge forwarder fallback
  let Allowed := SaltedCommon pk.pkSeed
  let RoutedAllowed : (Lab + O).Domain → Prop :=
    Sum.elim (Salted pk.pkSeed) (fun _ => True)
  let Good := Coverage.ActualKeyPotential.GoodQuery FIPS205.core pk (fun pk => pk.pkSeed)
  have hsource : AllQueriesSatisfy suffix Allowed := by
    simp only [suffix, simulateQ_bind, simulateQ_pure]
    refine allQueriesSatisfy_bind (projected_client_salted seed pk sk adv) ?_
    rintro ⟨forgery, rawLog⟩
    exact allQueriesSatisfy_bind
      (projected_verify_salted seed pk forgery.1 forgery.2)
      (fun _ => allQueriesSatisfy_pure _ _)
  have hguard : AllQueriesSatisfy
      ((simulateQ guard suffix).run (PUnit.unit, paid)) Allowed := by
    refine hsource.simulateQ_run ?_ (PUnit.unit, paid)
    intro input hi current
    by_cases haborted : current.2.2 = true
    · simp [guard, QueryImpl.guardQueryBudget, haborted]
    · by_cases hfit : current.2.1 + charge input ≤ caps
      · have hquery := (allQueriesSatisfy_query_iff (spec := LabCommon) input Allowed).2 hi
        simpa [guard, QueryImpl.guardQueryBudget, haborted, hfit, forwarder,
          QueryImpl.liftTarget_apply, QueryImpl.id', map_eq_bind_pure_comp,
          allQueriesSatisfy_def, isQueryBound_map_iff] using hquery
      · simp [guard, QueryImpl.guardQueryBudget, haborted, hfit]
  have hroute : AllQueriesSatisfy
      ((simulateQ (routeLab seed) ((simulateQ guard suffix).run (PUnit.unit, paid))).run raw)
      RoutedAllowed := by
    refine hguard.simulateQ_run ?_ raw
    rintro ((native | bytes) | event) hi cache
    · change AllQueriesSatisfy
        ((fun answer => (answer, cache)) <$>
          (liftM ((Lab + O).query (.inl native)) : OracleComp (Lab + O) _)) RoutedAllowed
      simpa only [allQueriesSatisfy_def, isQueryBound_map_iff] using
        (allQueriesSatisfy_query_iff (spec := Lab + O) (.inl native) RoutedAllowed).2 hi
    · change AllQueriesSatisfy
        (simulateQ (QueryImpl.ofLift (unifSpec + H) (OracleComp (Lab + O)))
          (((encoding seed).tableRouter bytes).run cache)) RoutedAllowed
      refine (allQueriesSatisfy_of_forall (fun _ => True.intro)
        (((encoding seed).tableRouter bytes).run cache)).simulateQ ?_
      rintro (sample | point) _
      · change AllQueriesSatisfy
          (liftM ((Lab + O).query (.inl (.inl (.inl (.inl sample))))) :
            OracleComp (Lab + O) _) RoutedAllowed
        exact (allQueriesSatisfy_query_iff (spec := Lab + O) _ _).2 trivial
      · have inputEq :
            QueryImpl.ofLift (unifSpec + H) (OracleComp (Lab + O)) (.inr point) =
            (liftM ((Lab + O).query (.inl (.inl (.inl (.inr point))))) :
              OracleComp (Lab + O) (H.Range point)) := by
          rcases point with
            (⟨publicSeed, nodeKey, inputs⟩ |
              ⟨randomness, publicSeed, publicRoot, message⟩) | nonce <;>
            rfl
        rw [inputEq]
        exact (allQueriesSatisfy_query_iff (spec := Lab + O) _ _).2 trivial
    · change AllQueriesSatisfy
        ((fun answer => (answer, cache)) <$>
          (liftM ((Lab + O).query (.inr event)) : OracleComp (Lab + O) PUnit)) RoutedAllowed
      simpa only [allQueriesSatisfy_def, isQueryBound_map_iff] using
        (allQueriesSatisfy_query_iff (spec := Lab + O) (.inr event) RoutedAllowed).2 trivial
  have huniform {alpha : Type} (program : ProbComp alpha) :
      AllQueriesSatisfy (liftComp program (Coverage.roleSpec FIPS205.core)) Good := by
    unfold liftComp
    refine (allQueriesSatisfy_of_forall (fun _ => True.intro) program).simulateQ ?_
    intro sample _
    change AllQueriesSatisfy
      (liftM ((Coverage.roleSpec FIPS205.core).query (.inl sample)) :
        OracleComp (Coverage.roleSpec FIPS205.core) _) Good
    exact (allQueriesSatisfy_query_iff _ _).2 trivial
  have hrole (role : Coverage.Role) (input : (deriveSpec FIPS205.core).Domain)
      (good : Coverage.ActualKeyPotential.GoodQuery FIPS205.core pk (fun pk => pk.pkSeed)
        (Coverage.roleQuery FIPS205.core role input)) :
      AllQueriesSatisfy (Coverage.roleImpl FIPS205.core role input) Good := by
    apply (isQueryBoundP_zero_iff _ Good).1
    exact (Coverage.isQueryBoundP_roleImpl_iff FIPS205.core role input).2
      (fun bad => (bad good).elim)
  have hprivate (input : Lab.Domain) (before : CoverageDeferred.S FIPS205.core) :
      AllQueriesSatisfy
        (do
          let result ← liftComp
            (((slhGraph FIPS205.core seed).deferredImpl input).run before.1)
            (Coverage.roleSpec FIPS205.core)
          pure (result.1, (result.2, before.2))) Good :=
    allQueriesSatisfy_bind (huniform _) (fun _ => allQueriesSatisfy_pure _ _)
  have hrelative : ∀ input, RoutedAllowed input → ∀ before,
      AllQueriesSatisfy
        ((CoverageDeferred.relative FIPS205.core seed (metadataCost true seed) input).run before)
        Good := by
    rintro ((((sample | (hash | publicNonce)) | (secret | nonce)) |
      (touch | node)) | event) hi before
    · simpa only [CoverageDeferred.relative, StateT.run_mk] using
        hprivate (.inl (.inl (.inl sample))) before
    · cases hash with
      | thash seed address values =>
        simpa only [CoverageDeferred.relative, StateT.run_mk] using
          hprivate (.inl (.inl (.inr (.inl (.thash seed address values))))) before
      | hmsg R seed pkRoot message =>
        apply allQueriesSatisfy_bind
          (hrole (CoverageDeferred.phaseRole before.2.2)
            (.inl (.inr (.inl (.hmsg R seed pkRoot message)))) (by
              cases CoverageDeferred.phaseRole before.2.2 <;> trivial))
        intro _
        exact allQueriesSatisfy_pure _ _
    · simpa only [CoverageDeferred.relative, StateT.run_mk] using
        hprivate (.inl (.inl (.inr (.inr publicNonce)))) before
    · simpa only [CoverageDeferred.relative, StateT.run_mk] using
        hprivate (.inl (.inr (.inl secret))) before
    · rcases nonce with ⟨salt, message⟩
      have hsalt : salt = pk.pkSeed := hi
      apply allQueriesSatisfy_bind
        (hrole (CoverageDeferred.phaseRole before.2.2) (.inr (.inr (salt, message))) (by
          cases CoverageDeferred.phaseRole before.2.2 <;> exact hsalt))
      intro _
      exact allQueriesSatisfy_pure _ _
    · simpa only [CoverageDeferred.relative, StateT.run_mk] using
        hprivate (.inr (.inl touch)) before
    · simpa only [CoverageDeferred.relative, StateT.run_mk] using
        hprivate (.inr (.inr node)) before
    · exact allQueriesSatisfy_pure _ _
  exact hroute.simulateQ_run hrelative state

private theorem source_output_of_run
    {ι κ σ α : Type} {spec : OracleSpec.{0, 0} ι} {target : OracleSpec.{0, 0} κ}
    (implementation : QueryImpl spec (StateT σ (OracleComp target)))
    (program : OracleComp spec α) (initial : σ) (result : α × σ)
    (member : result ∈ support ((simulateQ implementation program).run initial)) :
    result.1 ∈ support program := by
  apply support_simulateQ_run'_subset implementation program initial
  rw [StateT.run'_eq, support_map]
  exact ⟨result, member, rfl⟩

/-- The existing rejecting continuation keeps nonce discipline and its supplied public key. -/
theorem marked_rejecting_postkeygen_allowed_and_retained_key
    (seed : FIPS205.core.PkSeed) (adv : Game.Adversary FIPS205.Answer PK)
    (pk sk : PK) (caps : Nat × Nat)
    (fallback : (input : LabCommon.Domain) → LabCommon.Range input)
    (initialPaid : Paid) (initialRaw : Raw.QueryCache)
    (initialRelative : CoverageDeferred.S FIPS205.core)
    (initialRole : Coverage.RoleState FIPS205.core) :
    let marked := SigningView.Events.viewWithEvents (commonView true seed)
    let continuation : OracleComp (SigningView.Events.Spec A Message) Full := do
      let (forgery, rawLog) ← marked.runWithSigningOracle pk sk
        (SigningView.Events.mainWithEvents (commonMain adv) pk)
      let verified ← marked.verify pk forgery.1 forgery.2
      return ((pk, sk), ⟨forgery, rawLog, verified⟩)
    let source : OracleComp LabCommon Full := simulateQ commonProjection continuation
    letI : MonadLiftT (OracleComp LabCommon) (StateT PUnit (OracleComp LabCommon)) :=
      ⟨fun action => StateT.lift action⟩
    let forwarder := (QueryImpl.id' LabCommon).liftTarget
      (StateT PUnit (OracleComp LabCommon))
    let guarded := (simulateQ (QueryImpl.guardQueryBudget caps
      (Sum.elim (fun _ : A.Domain => (0, 0)) (policy true seed)) forwarder fallback)
        source).run (PUnit.unit, initialPaid)
    let routed := (simulateQ (routeLab seed) guarded).run initialRaw
    let roleProgram := (simulateQ (CoverageDeferred.relative FIPS205.core seed
      (metadataCost true seed)) routed).run initialRelative
    roleProgram.AllQueriesSatisfy
      (Coverage.ActualKeyPotential.GoodQuery FIPS205.core pk (fun key => key.pkSeed)) ∧
      (∀ outcome ∈ support ((simulateQ (Coverage.roleRunImpl FIPS205.core) roleProgram).run
          initialRole), outcome.1.1.1.1.1.1 = pk) := by
  intro marked continuation source forwarder guarded routed roleProgram
  refine ⟨?_, ?_⟩
  · simpa only [roleProgram, routed, guarded, source, continuation, marked, forwarder] using
      marked_rejecting_postkeygen_good_queries seed pk sk adv true caps fallback
        initialRaw initialRelative initialPaid
  · intro outcome member
    have roleMember := source_output_of_run (Coverage.roleRunImpl FIPS205.core)
      roleProgram initialRole outcome member
    have relativeMember := source_output_of_run
      (CoverageDeferred.relative FIPS205.core seed (metadataCost true seed))
      routed initialRelative outcome.1 roleMember
    have routedMember := source_output_of_run (routeLab seed) guarded
      initialRaw outcome.1.1 relativeMember
    have guardedMember := source_output_of_run
      (QueryImpl.guardQueryBudget caps
        (Sum.elim (fun _ : A.Domain => (0, 0)) (policy true seed)) forwarder fallback)
      source (PUnit.unit, initialPaid) outcome.1.1.1 routedMember
    have continuationMember := support_simulateQ_subset commonProjection continuation guardedMember
    simp only [continuation, mem_support_bind_iff, support_pure,
      Set.mem_singleton_iff] at continuationMember
    obtain ⟨⟨forgery, rawLog⟩, _, verified, _, fullEq⟩ := continuationMember
    exact congrArg (fun full : Full => full.1.1) fullEq

end SLHDSA.SHAKE128s.MarkedClient

namespace SLHDSA.SHAKE128s.RoleProgramCredit
open OracleComp OracleSpec MeasureTheory
open scoped ENNReal
open SLHDSA.Security SLHDSA.SHAKE128s
open SLHDSA.SHAKE128s.DigestTape SLHDSA.SHAKE128s.NoticingTape
open Coverage.ActualKeyPotential Coverage.ActualKeyPotential.Pair

/-- The result of a role-indexed program and its terminal tape and query state. -/
abbrev Outcome (alpha : Type) := alpha × Coverage.RoleState FIPS205.core

/-- The signer and forger digest blocks as a family of role-indexed tapes. -/
abbrev tapes := SLHDSA.SHAKE128s.ConsumedPrefix.tapes

/-- Run a role-indexed program with the two supplied digest blocks, an empty cache and zero
counters. -/
noncomputable abbrev run {alpha : Type}
    (program : OracleComp (Coverage.roleSpec FIPS205.core) alpha)
    (left right : List HashOutput) : ProbComp (Outcome alpha) :=
  (simulateQ (Coverage.roleRunImpl FIPS205.core) program).run
    ((∅, tapes left right), (AnswerTape.ClassPos.init, ∅))

/-- The number of queries made in the forger class. -/
abbrev forgerCount {alpha : Type} (outcome : Outcome alpha) : Nat :=
  outcome.2.2.1.cnt .forger
/-- The number of queries made in the signer class. -/
abbrev signerCount {alpha : Type} (outcome : Outcome alpha) : Nat :=
  outcome.2.2.1.cnt .signer
/-- The number of entries consumed from the signer tape. -/
abbrev signerPrefix {alpha : Type} (outcome : Outcome alpha) : Nat :=
  outcome.2.2.1.next .signer
/-- A message-hash point for the key selected from the output fired at this forger-tape position. -/
abbrev fired {alpha : Type} (key : alpha → PublicKeyCore FIPS205.core)
    (outcome : Outcome alpha) (index : Nat) : Prop :=
  Fired FIPS205.core (key outcome.1) outcome.2 index

/-! ## Shared role-position and future-cell invariants -/

private theorem prefix_bounds {alpha : Type}
    (program : OracleComp (Coverage.roleSpec FIPS205.core) alpha)
    (leftLength rightLength : Nat) (outcome : (List HashOutput × List HashOutput) × Outcome alpha)
    (hout : outcome ∈ support (blockRunOf (run program) leftLength rightLength)) :
    signerPrefix outcome.2 ≤ leftLength ∧
      signerPrefix outcome.2 ≤ signerCount outcome.2 := by
  have hs := mem_support_blockRunOf (run program) leftLength rightLength outcome hout
  have hpos : AnswerTape.ClassPosInv (Coverage.tapeClass FIPS205.core)
      (tapes outcome.1.1 outcome.1.2) outcome.2.2.1.1 outcome.2.2.1.2
      outcome.2.2.2.1.cls outcome.2.2.2.1.pos outcome.2.2.2.1.next outcome.2.2.2.1.cnt :=
    simulateQ_run_preserves_inv_of_query (Coverage.roleRunImpl FIPS205.core)
      (fun state : Coverage.RoleState FIPS205.core =>
        AnswerTape.ClassPosInv (Coverage.tapeClass FIPS205.core)
          (tapes outcome.1.1 outcome.1.2) state.1.1 state.1.2
          state.2.1.cls state.2.1.pos state.2.1.next state.2.1.cnt)
      (AnswerTape.classPosInvAuxFwd_step (Coverage.tapeClass FIPS205.core)
        (Coverage.range_eq_tapeClassRange FIPS205.core)
        (AnswerTape.freshHitAux (Coverage.IsRandPoint FIPS205.core)
          (Coverage.randRel FIPS205.core)) (tapes outcome.1.1 outcome.1.2))
      program _
      (AnswerTape.ClassPosInv.empty (Coverage.tapeClass FIPS205.core)
        (tapes outcome.1.1 outcome.1.2)) outcome.2 hs.2.2
  have lengths := hpos.length_add .signer
  have leftLengthEq := padding_length leftLength outcome.1.1 hs.1
  simp only [SLHDSA.SHAKE128s.ConsumedPrefix.tapes, List.length_map, leftLengthEq] at lengths
  exact ⟨by dsimp only [signerPrefix]; omega, hpos.next_le_cnt .signer⟩

private theorem count_overwrite {alpha : Type}
    (program : OracleComp (Coverage.roleSpec FIPS205.core) alpha)
    (which : Coverage.TapeClass) (index cell : Nat) (left right : List HashOutput)
    (value : HashOutput) (horder : index ≤ cell) :
    Pr{let z ← (run program
      (if which = .signer then left.set cell value else left)
      (if which = .forger then right.set cell value else right))}[
        index < z.2.2.1.cnt which] =
    Pr{let z ← run program left right}[index < z.2.2.1.cnt which] := by
  classical
  let initial : Coverage.RoleState FIPS205.core :=
    ((∅, tapes left right), (AnswerTape.ClassPos.init, ∅))
  let observation (family : (j : Coverage.TapeClass) →
      List (Coverage.tapeClassRange FIPS205.core j)) : ℝ≥0∞ :=
    Pr{let z ← ((simulateQ (Coverage.roleRunImpl FIPS205.core)
      program).run
        ((∅, family), (AnswerTape.ClassPos.init, ∅)))}[index < z.2.2.1.cnt which]
  cases which with
  | signer =>
    have h := Coverage.ClassCountCausality.prEvent_cnt_overwrite FIPS205.core .signer
      program initial index cell
      (Bridge.answerEquiv value) horder
    simp only [initial, Coverage.ClassCountCausality.overwrite,
      AnswerTape.ClassPos.init, Nat.zero_add] at h
    convert h using 1 <;> apply congrArg observation <;> funext j <;>
      cases j <;> simp [SLHDSA.SHAKE128s.ConsumedPrefix.tapes,
        Coverage.ClassCountCausality.overwriteTapes, List.map_set]
  | forger =>
    have h := Coverage.ClassCountCausality.prEvent_cnt_overwrite FIPS205.core .forger
      program initial index cell
      (Bridge.answerEquiv value) horder
    simp only [initial, Coverage.ClassCountCausality.overwrite,
      AnswerTape.ClassPos.init, Nat.zero_add] at h
    convert h using 1 <;> apply congrArg observation <;> funext j <;>
      cases j <;> simp [SLHDSA.SHAKE128s.ConsumedPrefix.tapes,
        Coverage.ClassCountCausality.overwriteTapes, List.map_set]
  | other => simp

/-! ## Terminal credits and compensated coverage -/

private theorem digest_card : Nat.card FIPS205.core.Y = 2 ^ 128 := by
  change Nat.card (SLHDSA.Concrete.shakePrimitives FIPS205.params.params).core.Y = 2 ^ 128
  rw [SLHDSA.Concrete.natCard_shakePrimitives_y]
  change 256 ^ 16 = 2 ^ 128
  norm_num

private theorem single_rate_finite : (Nat.card FIPS205.core.Y : ℝ≥0∞)⁻¹ ≠ ⊤ := by
  rw [digest_card]
  norm_num

private theorem thin_one {alpha : Type}
    (program : OracleComp (Coverage.roleSpec FIPS205.core) alpha)
    (key : alpha → PublicKeyCore FIPS205.core)
    (singleCredit : ∀ (left right : List HashOutput) (index : Nat),
      ∫⁻ value, value ∂𝒟[(fun outcome =>
        terminalValue FIPS205.core (key outcome.1) index outcome.2) <$>
          run program left right] ≤ (Nat.card FIPS205.core.Y : ℝ≥0∞)⁻¹)
    (left right : List HashOutput) (index : Nat) :
    Pr{let z ← run program left right}[index < forgerCount z ∧ fired key z index] ≤
      1 / ((2 ^ 128 : Nat) : ℝ≥0∞) *
        Pr{let z ← run program left right}[index < forgerCount z] := by
  classical
  let mx := run program left right
  let reach : Outcome alpha → Prop := fun z => index < forgerCount z
  let fire : Outcome alpha → Prop := fun z => fired key z index
  let epsilon : ℝ≥0∞ := (Nat.card FIPS205.core.Y : ℝ≥0∞)⁻¹
  have thin := OracleComp.prEvent_le_mul_prEvent_of_unreached_credit
    mx reach fire epsilon single_rate_finite (by
      simpa only [mx, terminalValue, fire, reach, forgerCount, fired, epsilon]
        using singleCredit left right index)
  have answer := (prEvent_mono mx (fun z => reach z ∧ fire z) fire
    (fun _ h => h.2)).trans thin
  have rate : epsilon = 1 / ((2 ^ 128 : Nat) : ℝ≥0∞) := by
    simp only [epsilon, digest_card, one_div]
  simpa only [mx, reach, fire, rate] using answer

private theorem thin_two {alpha : Type}
    (program : OracleComp (Coverage.roleSpec FIPS205.core) alpha)
    (key : alpha → PublicKeyCore FIPS205.core)
    (pairCredit : ∀ (left right : List HashOutput) (first second : Nat),
      first < second →
      ∫⁻ value, value ∂𝒟[(fun outcome =>
        pairTerminalValue FIPS205.core (key outcome.1) first second outcome.2) <$>
          run program left right] ≤ ((Nat.card FIPS205.core.Y : ℝ≥0∞)⁻¹) ^ 2)
    (left right : List HashOutput) (first second : Nat) (horder : first < second) :
    Pr{let z ← run program left right}[
      second < forgerCount z ∧ fired key z first ∧ fired key z second] ≤
      1 / ((2 ^ 256 : Nat) : ℝ≥0∞) *
        Pr{let z ← run program left right}[first < forgerCount z] := by
  classical
  let mx := run program left right
  let reach : Outcome alpha → Prop := fun z => first < forgerCount z
  let fire : Outcome alpha → Prop := fun z => fired key z first ∧ fired key z second
  let epsilon : ℝ≥0∞ := ((Nat.card FIPS205.core.Y : ℝ≥0∞)⁻¹)^2
  have epsilonFinite : epsilon ≠ ⊤ := by
    simpa only [epsilon, pow_two] using ENNReal.mul_ne_top single_rate_finite single_rate_finite
  let creditMean (credit : Outcome alpha → ℝ≥0∞) : ℝ≥0∞ :=
    ∫⁻ value, value ∂𝒟[credit <$> mx]
  have thin := OracleComp.prEvent_le_mul_prEvent_of_unreached_credit
    mx reach fire epsilon epsilonFinite (by
      refine le_of_eq_of_le ?_ (pairCredit left right first second horder)
      apply congrArg creditMean
      funext z
      by_cases hfire : fired key z first ∧ fired key z second <;>
        by_cases hreach : first < forgerCount z <;>
          simp [pairTerminalValue, fire, reach, epsilon, fired, forgerCount, hfire, hreach])
  have answer := (prEvent_mono mx (fun z => second < forgerCount z ∧ fire z) fire
    (fun _ h => h.2)).trans thin
  have rate : epsilon = 1 / ((2 ^ 256 : Nat) : ℝ≥0∞) := by
    simp only [epsilon, ← ENNReal.inv_pow]
    norm_num [digest_card, one_div]
  simpa only [mx, reach, fire, rate] using answer

/-- Any fixed role program with internally proved terminal credits has compensated coverage.
The returned-key selector is allowed to depend on every retained output field. -/
theorem role_program_consumed_credit
    {alpha : Type}
    (program : OracleComp (Coverage.roleSpec FIPS205.core) alpha)
    (key : alpha → PublicKeyCore FIPS205.core)
    (singleCredit : ∀ (left right : List HashOutput) (index : Nat),
      ∫⁻ value, value ∂𝒟[(fun outcome =>
        terminalValue FIPS205.core (key outcome.1) index outcome.2) <$>
          run program left right] ≤ (Nat.card FIPS205.core.Y : ℝ≥0∞)⁻¹)
    (pairCredit : ∀ (left right : List HashOutput) (first second : Nat),
      first < second →
      ∫⁻ value, value ∂𝒟[(fun outcome =>
        pairTerminalValue FIPS205.core (key outcome.1) first second outcome.2) <$>
          run program left right] ≤ ((Nat.card FIPS205.core.Y : ℝ≥0∞)⁻¹) ^ 2)
    (leftLength rightLength : Nat)
    (leftMin : 2 ≤ leftLength) (leftCap : leftLength ≤ 5 * 2 ^ 62) :
    Pr{let outcome ← blockRunOf (run program) leftLength rightLength}[
      FiredCoverage.FiredCovered forgerCount (fired key)
        (signerPrefix outcome.2) rightLength outcome] ≤
      ((1 : ℝ≥0∞) / ((8 * 2 ^ 128 : Nat) : ℝ≥0∞)) *
        Pr{let outcome ← blockRunOf (run program) leftLength rightLength}[
          2 ≤ signerCount outcome.2] +
      (∑' outcome,
        Pr{let x ← blockRunOf (run program) leftLength rightLength}[x = outcome] *
          (forgerCount outcome.2 : ℝ≥0∞)) *
        ((((9 * 2 ^ 99 : Nat) : ℝ≥0∞) / ((2 ^ 231 : Nat) : ℝ≥0∞)) +
          (rightLength : ℝ≥0∞) / ((2 ^ 303 : Nat) : ℝ≥0∞)) := by
  apply FiredCoverage.prob_usedPrefix_firedCovered_le
    (run program) forgerCount (fired key) signerCount signerPrefix
    leftLength rightLength leftMin leftCap
  · exact prefix_bounds program leftLength rightLength
  · intro index cell left right value horder
    simpa [forgerCount] using
      count_overwrite program .forger index cell left right value horder
  · intro index left right
    exact thin_one program key singleCredit left right index
  · intro first second left right horder
    exact thin_two program key pairCredit left right first second horder
  · intro cell left right value horder
    simpa [signerCount, Nat.succ_le_iff] using
      count_overwrite program .signer 1 cell left right value horder

end SLHDSA.SHAKE128s.RoleProgramCredit

namespace SLHDSA.SHAKE128s.MarkedPrefix
open OracleComp OracleSpec SignatureAlg MeasureTheory
open scoped ENNReal
open SLHDSA SLHDSA.Security SLHDSA.SHAKE128s
open SLHDSA.SHAKE128s.Bridge.SharedExperiment
open Guarded (PK Raw H A O Lab LabCommon Full Paid Meta RawOutcome
  commonView commonMain commonSource commonProjection routeLab policy metadataCost
  guardedRoutedSource)
open Coverage.ActualKeyPotential
open SLHDSA.SHAKE128s.DigestTape SLHDSA.SHAKE128s.NoticingTape

/-- The public key returned by the marked key-generation phase. -/
abbrev returnedPK (outcome : Outcome) : PK := outcome.1.1.1.1.1.1
/-- The final number of forger-class queries in the marked experiment. -/
abbrev forgerCount (outcome : Outcome) : Nat := outcome.2.2.1.cnt .forger
/-- The final number of signer-class queries in the marked experiment. -/
abbrev signerCount (outcome : Outcome) : Nat := outcome.2.2.1.cnt .signer
/-- The number of signer-tape entries consumed by the marked experiment. -/
abbrev signerPrefix (outcome : Outcome) : Nat := outcome.2.2.1.next .signer
/-- A message-hash point for the generated public key fired at this forger-tape position. -/
abbrev fired (outcome : Outcome) (index : Nat) : Prop :=
  Fired FIPS205.core (returnedPK outcome) outcome.2 index

/-- Conditioning on the complete key-generation output transfers a credit bound
from allowed continuations with their retained public key to the complete marked run. -/
private theorem whole_credit_of_allowed
    (seed : FIPS205.core.PkSeed) (adv : Game.Adversary FIPS205.Answer PK)
    (caps : Nat × Nat)
    (fallback : (input : LabCommon.Domain) → LabCommon.Range input)
    (relative : CoverageDeferred.S FIPS205.core)
    (family : (j : Coverage.TapeClass) → List (Coverage.tapeClassRange FIPS205.core j))
    (credit : PK → Coverage.RoleState FIPS205.core → ℝ≥0∞) (limit : ℝ≥0∞)
    (funded : ∀ (pk : PK) (program : OracleComp (Coverage.roleSpec FIPS205.core) (Stage Full)),
      program.AllQueriesSatisfy (GoodQuery FIPS205.core pk (fun key => key.pkSeed)) →
      ∫⁻ value, value ∂𝒟[(fun outcome => credit pk outcome.2) <$>
        (simulateQ (Coverage.roleRunImpl FIPS205.core) program).run
          ((∅, family), (AnswerTape.ClassPos.init, ∅))] ≤ limit) :
    ∫⁻ value, value ∂𝒟[(fun outcome => credit (returnedPK outcome) outcome.2) <$>
      wholeRun seed adv caps fallback relative family] ≤ limit := by
  classical
  rw [marked_wholeRun_eq_prefix_suffix, lintegral_id_evalDist_map_bind]
  apply lintegral_id_evalDist_map_le_of_le_of_mem_support
  intro stage member
  let pk := stage.1.1.1.1.1
  let sk := stage.1.1.1.1.2
  let program := roleProgram seed caps fallback (suffixSource seed adv pk sk)
    stage.1.1.1.2.2 stage.1.1.2 stage.1.2
  let initial : Coverage.RoleState FIPS205.core :=
    ((∅, family), (AnswerTape.ClassPos.init, ∅))
  have same := (marked_keygen_uniform_and_role_state_unchanged seed caps fallback
    ((0, 0), false) ∅ relative initial).2 stage member
  obtain ⟨allowed, retained⟩ :=
    SLHDSA.SHAKE128s.MarkedClient.marked_rejecting_postkeygen_allowed_and_retained_key
      seed adv pk sk caps fallback stage.1.1.1.2.2 stage.1.1.2 stage.1.2 stage.2
  let action := (simulateQ (Coverage.roleRunImpl FIPS205.core) program).run stage.2
  have bound : ∫⁻ value, value ∂𝒟[(fun outcome => credit pk outcome.2) <$> action] ≤ limit := by
    change ∫⁻ value, value ∂𝒟[(fun outcome => credit pk outcome.2) <$>
      (simulateQ (Coverage.roleRunImpl FIPS205.core) program).run stage.2] ≤ limit
    rw [same]
    exact funded pk program allowed
  apply le_trans _ bound
  let _ : MeasurableSpace Outcome := ⊤
  change (∫⁻ value, value ∂𝒟[(fun outcome => credit (returnedPK outcome) outcome.2) <$> action]) ≤ _
  rw [lintegral_id_evalDist_map, lintegral_id_evalDist_map]
  apply lintegral_mono_ae
  apply evalDist.ae_of_forall_mem_support _ _ MeasurableSet.of_discrete
  intro outcome supported
  exact le_of_eq (congrArg (fun key => credit key outcome.2) (retained outcome supported))

/-- The marked run funds one terminal slot for its returned public key. -/
theorem marked_whole_terminal_credit
    (seed : FIPS205.core.PkSeed) (adv : Game.Adversary FIPS205.Answer PK)
    (caps : Nat × Nat)
    (fallback : (input : LabCommon.Domain) → LabCommon.Range input)
    (relative : CoverageDeferred.S FIPS205.core)
    (family : (j : Coverage.TapeClass) → List (Coverage.tapeClassRange FIPS205.core j))
    (otherEmpty : family .other = []) (index : Nat) :
    ∫⁻ value, value ∂𝒟[(fun outcome =>
      terminalValue FIPS205.core (returnedPK outcome) index outcome.2) <$>
        wholeRun seed adv caps fallback relative family] ≤
      (Nat.card FIPS205.core.Y : ℝ≥0∞)⁻¹ := by
  apply whole_credit_of_allowed seed adv caps fallback relative family
    (fun pk state => terminalValue FIPS205.core pk index state)
  intro pk program allowed
  exact (allowed_program_terminal_credit FIPS205.core pk (fun key => key.pkSeed)
    family otherEmpty index program allowed _).trans_eq
    (potential_initial FIPS205.core pk (fun key => key.pkSeed) family index)

/-- Two ordered slots share the product-potential bound at the same returned public key. -/
theorem marked_whole_pair_terminal_credit
    (seed : FIPS205.core.PkSeed) (adv : Game.Adversary FIPS205.Answer PK)
    (caps : Nat × Nat)
    (fallback : (input : LabCommon.Domain) → LabCommon.Range input)
    (relative : CoverageDeferred.S FIPS205.core)
    (family : (j : Coverage.TapeClass) → List (Coverage.tapeClassRange FIPS205.core j))
    (otherEmpty : family .other = []) (first second : Nat) (order : first < second) :
    ∫⁻ value, value ∂𝒟[(fun outcome =>
      Pair.pairTerminalValue FIPS205.core (returnedPK outcome) first second outcome.2) <$>
        wholeRun seed adv caps fallback relative family] ≤
      ((Nat.card FIPS205.core.Y : ℝ≥0∞)⁻¹) ^ 2 := by
  apply whole_credit_of_allowed seed adv caps fallback relative family
    (fun pk state => Pair.pairTerminalValue FIPS205.core pk first second state)
  intro pk program allowed
  exact (Pair.allowed_program_pair_terminal_credit FIPS205.core pk (fun key => key.pkSeed)
    family otherEmpty first second order program allowed _).trans_eq (by
      rw [pow_two]
      exact congrArg₂ (· * ·) (potential_initial FIPS205.core pk _ family first)
        (potential_initial FIPS205.core pk _ family second))

/-- Run the complete guarded experiment on the supplied signer and forger digest blocks. -/
noncomputable abbrev run (seed : FIPS205.core.PkSeed)
    (adv : Game.Adversary FIPS205.Answer PK) (caps : Nat × Nat)
    (fallback : (input : LabCommon.Domain) → LabCommon.Range input)
    (relative : CoverageDeferred.S FIPS205.core) (left right : List HashOutput) :
    ProbComp Outcome :=
  wholeRun seed adv caps fallback relative (SLHDSA.SHAKE128s.ConsumedPrefix.tapes left right)

/-- Consumed signer cells and the complete forger count bound marked coverage. -/
theorem marked_whole_consumed_credit
    (seed : FIPS205.core.PkSeed) (adv : Game.Adversary FIPS205.Answer PK)
    (caps : Nat × Nat)
    (fallback : (input : LabCommon.Domain) → LabCommon.Range input)
    (relative : CoverageDeferred.S FIPS205.core) (rightLength : Nat) :
    Pr{let outcome ← blockRunOf (run seed adv caps fallback relative)
        (2 ^ 64 + 1) rightLength}[
      FiredCoverage.FiredCovered forgerCount fired (signerPrefix outcome.2)
        rightLength outcome] ≤
      ((1 : ℝ≥0∞) / ((8 * 2 ^ 128 : Nat) : ℝ≥0∞)) *
        Pr{let outcome ← blockRunOf (run seed adv caps fallback relative)
            (2 ^ 64 + 1) rightLength}[2 ≤ signerCount outcome.2] +
      (∑' outcome,
        Pr{let x ← blockRunOf (run seed adv caps fallback relative)
            (2 ^ 64 + 1) rightLength}[x = outcome] *
          (forgerCount outcome.2 : ℝ≥0∞)) *
        ((((9 * 2 ^ 99 : Nat) : ℝ≥0∞) / ((2 ^ 231 : Nat) : ℝ≥0∞)) +
          (rightLength : ℝ≥0∞) / ((2 ^ 303 : Nat) : ℝ≥0∞)) := by
  apply RoleProgramCredit.role_program_consumed_credit
    (wholeRoleProgram seed adv caps fallback relative) (fun stage => stage.1.1.1.1.1)
  · intro left right index
    exact marked_whole_terminal_credit seed adv caps fallback relative
      (SLHDSA.SHAKE128s.ConsumedPrefix.tapes left right) rfl index
  · intro left right first second order
    exact marked_whole_pair_terminal_credit seed adv caps fallback relative
      (SLHDSA.SHAKE128s.ConsumedPrefix.tapes left right) rfl first second order
  · norm_num
  · norm_num

end SLHDSA.SHAKE128s.MarkedPrefix
