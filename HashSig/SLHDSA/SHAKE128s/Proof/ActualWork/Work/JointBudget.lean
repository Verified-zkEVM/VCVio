/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module

public import HashSig.SLHDSA.SHAKE128s.Proof.ActualWork.Work.Counters
import all HashSig.SLHDSA.SHAKE128s.Bridge.SharedExperiment.Joint.Source
import all VCVio.OracleComp.QueryTracking.Enforcement
import VCVio.ProgramLogic.Relational.SimulateQ.Coupling
import VCVio.OracleComp.SimSemantics.StateT.StateProjection
import VCVio.OracleComp.QueryTracking.CountingOracle.Core
import Lean.Elab.Tactic.Omega

/-! # Transporting a probability-one joint work budget

The original sampled public seed, full generated key pair, complete source vector and byte
cache remain joint until their explicit observations. Actual successful verification supplies
one original hash; at a nonweak retained key its message-digest marker supplies the reserve unit.
-/

public section

open OracleComp OracleSpec SignatureAlg
open SLHDSA SLHDSA.Security SLHDSA.SHAKE128s
open scoped ENNReal

namespace SLHDSA.SHAKE128s.Bridge.SharedExperiment

open Guarded (PK Raw H R Ev O Native Common Meta encoding policy selectedRaw aux)

/-- The two existing physical observations follow identical answers and cache updates.
The reserve writer and existing selected-raw metadata fit the original selected work, while
the full original vector and exact signing-attempt coordinate remain available in the relation. -/
private theorem physical_reserve_original_cost_relation
    {alpha : Type} (seed : FIPS205.core.PkSeed) (program : OracleComp Common alpha) :
    let physical : QueryImpl Common (StateT Raw.QueryCache ProbComp) :=
      eraseObsImpl (Ev := Ev) (Raw.romImpl ∘ₛ (encoding seed).encodeImpl)
    let observed := physical.extendState (aux (spec := Native) (selectedRaw seed))
    let originalCost : Common.Domain → Game.Counted.SourceCounts :=
      Sum.elim (fun _ => 0) Game.Counted.sourcePolicy
    let reserveCost : Common.Domain → Nat × Nat :=
      Sum.elim (fun _ => (0, 0)) (policy true seed)
    let original := ((simulateQ (physical.withAddCost originalCost) program).runAdd).run ∅
    let reserve := ((simulateQ (observed.withAddCost reserveCost) program).runAdd).run
      (∅, (0, .keygen))
    OracleComp.ProgramLogic.Relational.RelTriple original reserve
      (fun left right =>
        left.1.1 = right.1.1 ∧ left.2 = right.2.1 ∧
          right.1.2.1 + right.2.2.1 ≤
            32 * (∑ kind ∈ Game.adversaryWork, left.1.2 kind) ∧
          right.1.2.2 = left.1.2 .sign) := by
  classical
  intro physical observed originalCost reserveCost original reserve
  let work : Game.Counted.SourceCounts → Nat :=
    fun counts => ∑ kind ∈ Game.adversaryWork, counts kind
  have work_add (left right : Game.Counted.SourceCounts) :
      work (left + right) = work left + work right := by
    simp only [work, Pi.add_apply, Finset.sum_add_distrib]
  let leftImpl := QueryImpl.sourceCounted (0 : Game.Counted.SourceCounts)
    originalCost physical
  let rightImpl := QueryImpl.sourceCounted (0 : Nat × Nat) reserveCost observed
  let invariant : (Raw.QueryCache × (Game.Counted.SourceCounts × Bool)) →
      ((Raw.QueryCache × Meta) × ((Nat × Nat) × Bool)) → Prop :=
    fun left right => left.1 = right.1.1 ∧
      right.2.1.1 + right.1.2.1 ≤ 32 * work left.2.1 ∧
      right.2.1.2 = left.2.1 .sign
  have step (input : Common.Domain)
      (left : Raw.QueryCache × (Game.Counted.SourceCounts × Bool))
      (right : (Raw.QueryCache × Meta) × ((Nat × Nat) × Bool))
      (related : invariant left right) :
      OracleComp.ProgramLogic.Relational.RelTriple
        ((leftImpl input).run left) ((rightImpl input).run right)
        (fun first second => first.1 = second.1 ∧ invariant first.2 second.2) := by
    rcases left with ⟨cache, counts, flag⟩
    rcases right with ⟨⟨otherCache, metadata⟩, paid, otherFlag⟩
    rcases related with ⟨sameCache, workBound, signCount⟩
    dsimp only at sameCache
    subst otherCache
    change paid.1 + metadata.1 ≤ 32 * work counts at workBound
    change paid.2 = counts .sign at signCount
    simp only [leftImpl, rightImpl, observed, QueryImpl.sourceCounted,
      QueryImpl.extendState_apply, bind_assoc, pure_bind]
    apply OracleComp.ProgramLogic.Relational.relTriple_bind
      (OracleComp.ProgramLogic.Relational.relTriple_refl ((physical input).run cache))
    rintro ⟨answer, nextCache⟩ ⟨otherAnswer, otherNextCache⟩ same
    cases same
    apply OracleComp.ProgramLogic.Relational.relTriple_pure_pure
    refine ⟨rfl, rfl, ?_, ?_⟩
    · rcases input with native | event
      · simpa only [invariant, originalCost, reserveCost, aux, work,
          Pi.zero_apply, Pi.add_apply, zero_add, add_zero, Prod.fst_add,
          Finset.sum_add_distrib, Finset.sum_const_zero, Sum.elim_inl] using workBound
      · have eventBound := Guarded.policy_true_work_add_selectedRaw_le_original seed event
        have originalWork : (Guarded.originalPolicy event).1 =
            work (Game.Counted.sourcePolicy event) := by
          simp only [Guarded.originalPolicy, work, Game.adversaryWork]
        dsimp only [originalCost, reserveCost, invariant]
        simp only [Sum.elim_inr]
        cases event with
        | signingAttempt request =>
          simp only [aux]
          have bound := Nat.add_le_add workBound eventBound.1
          rw [originalWork] at bound
          simpa only [work_add, Nat.mul_add, Prod.fst_add] using
            (show paid.1 + (policy true seed (.signingAttempt request)).1 +
                (metadata.1 + selectedRaw seed (.signingAttempt request)) ≤
                  32 * work counts +
                    32 * work (Game.Counted.sourcePolicy (.signingAttempt request)) from by
              omega)
        | ambient phase native =>
          simp only [aux]
          have bound := Nat.add_le_add workBound eventBound.1
          rw [originalWork] at bound
          simpa only [work_add, Nat.mul_add, Prod.fst_add] using
            (show paid.1 + (policy true seed (.ambient phase native)).1 +
                (metadata.1 + selectedRaw seed (.ambient phase native)) ≤
                  32 * work counts +
                    32 * work (Game.Counted.sourcePolicy (.ambient phase native)) from by
              omega)
    · rcases input with native | event
      · simpa only [originalCost, reserveCost, Pi.add_apply, Pi.zero_apply,
          zero_add, add_zero, Prod.snd_add, Sum.elim_inl] using signCount
      · have eventBound := Guarded.policy_true_work_add_selectedRaw_le_original seed event
        change paid.2 + (policy true seed event).2 =
          counts .sign + Game.Counted.sourcePolicy event .sign
        rw [signCount, eventBound.2]
        rfl
  have relation := OracleComp.ProgramLogic.Relational.relTriple_simulateQ_run
    leftImpl rightImpl invariant program step
    (∅, (0, false)) ((∅, (0, .keygen)), ((0, 0), false))
    (by simp [invariant, work])
  let leftProjection := fun result :
      alpha × (Raw.QueryCache × (Game.Counted.SourceCounts × Bool)) =>
    ((result.1, result.2.2.1), result.2.1)
  let rightProjection := fun result :
      alpha × ((Raw.QueryCache × Meta) × ((Nat × Nat) × Bool)) =>
    ((result.1, result.2.2.1), result.2.1)
  have projected : OracleComp.ProgramLogic.Relational.RelTriple
      (leftProjection <$> (simulateQ leftImpl program).run (∅, (0, false)))
      (rightProjection <$> (simulateQ rightImpl program).run
        ((∅, (0, .keygen)), ((0, 0), false)))
      (fun left right =>
        left.1.1 = right.1.1 ∧ left.2 = right.2.1 ∧
          right.1.2.1 + right.2.2.1 ≤
            32 * (∑ kind ∈ Game.adversaryWork, left.1.2 kind) ∧
          right.1.2.2 = left.1.2 .sign) := by
    apply OracleComp.ProgramLogic.Relational.relTriple_map
    apply OracleComp.ProgramLogic.Relational.relTriple_post_mono relation
    intro left right related
    exact ⟨related.1, related.2.1, related.2.2.1, related.2.2.2⟩
  have originalProjection := QueryImpl.source_run_cost (0 : Game.Counted.SourceCounts)
    originalCost physical program ∅ 0 false
  have reserveProjection := QueryImpl.source_run_cost (0 : Nat × Nat)
    reserveCost observed program (∅, (0, .keygen)) 0 false
  simp only [zero_add, Prod.eta, id_map'] at originalProjection reserveProjection
  change OracleComp.ProgramLogic.Relational.RelTriple
    (leftProjection <$> (simulateQ leftImpl program).run (∅, (0, false)))
    (rightProjection <$> (simulateQ rightImpl program).run
      ((∅, (0, .keygen)), ((0, 0), false))) _ at projected
  rw [show leftProjection <$> (simulateQ leftImpl program).run (∅, (0, false)) =
      original from originalProjection,
    show rightProjection <$> (simulateQ rightImpl program).run
      ((∅, (0, .keygen)), ((0, 0), false)) = reserve from reserveProjection] at projected
  exact projected

open Classical in
/-- Projecting the retained physical source gives the exact original winning bit and all five
counts in one joint law. The sampled seed is forgotten only by this explicit final projection. -/
private theorem physical_original_joint_game
    (adv : Game.Adversary FIPS205.Answer (PublicKeyCore FIPS205.core)) :
    let physical := fun seed : FIPS205.core.PkSeed =>
      (eraseObsImpl (Ev := Ev) (Raw.romImpl ∘ₛ (encoding seed).encodeImpl) :
        QueryImpl Common (StateT Raw.QueryCache ProbComp))
    let cost : Common.Domain → Game.Counted.SourceCounts :=
      Sum.elim (fun _ => 0) Game.Counted.sourcePolicy
    let source := do
      let seed ← ($ᵗ FIPS205.core.PkSeed : ProbComp FIPS205.core.PkSeed)
      let out ← ((simulateQ ((physical seed).withAddCost cost)
        (mixedSourceAt seed adv)).runAdd).run ∅
      pure (seed, out)
    (fun sampled =>
      (decide (SigningView.Wins id sampled.2.1.1.2), sampled.2.1.2)) <$> source =ᵈ
      (Game.securityGame FIPS205.scheme).experiment () adv := by
  classical
  intro physical cost source
  let view := Game.Counted.externalView FIPS205.scheme
  let main := Game.Counted.externalMain adv
  let marked := SigningView.Events.fullExperiment view main
  let rawHandler := SigningView.Events.handlerWithEvents (Request := Message) Raw.romImpl
  let rawCost : (Guarded.R + Guarded.O).Domain → Game.Counted.SourceCounts :=
    Sum.elim (fun _ => 0) Game.Counted.sourcePolicy
  let original := ((simulateQ (rawHandler.withAddCost rawCost) marked).runAdd).run ∅
  let counted : SigningView.CostM Guarded.R Game.Counted.SourceCounts
      (((PublicKeyCore FIPS205.core) × (SecretKeyCore FIPS205.core)) ×
        SigningView.Outcome Message (List Byte) (Option (List Byte))) := do
    let keys ← SigningView.costed Game.Counted.sourcePolicy .keygen view.keygen
    let outcome ← SigningView.countedAfterKeygen Game.Counted.sourcePolicy
      view keys.1 keys.2 main
    pure (keys, outcome)
  have countedSource : original = (simulateQ Raw.romImpl counted.runAdd).run ∅ := by
    have countedLaw := SigningView.Events.runObs_fullKeys_eq_counted view main
      Game.Counted.sourcePolicy Raw.romImpl (∅ : Raw.QueryCache)
    have handlers : rawHandler.withAddCost rawCost =
        (eraseObsImpl (Ev := Ev) Raw.romImpl).withCost
          (obsCostFn (fun event => Multiplicative.ofAdd
            (Game.Counted.sourcePolicy event))) := by
      funext input
      cases input <;>
        simp [rawHandler, rawCost, SigningView.Events.handlerWithEvents,
          QueryImpl.withAddCost, eraseObsImpl, obsCostFn, ofAdd_zero]
    change (fun result =>
      ((result.1.1, Multiplicative.toAdd result.1.2), result.2)) <$>
      (runObs Raw.romImpl
        (fun event => Multiplicative.ofAdd (Game.Counted.sourcePolicy event)) marked).run ∅ =
      (simulateQ Raw.romImpl counted.runAdd).run ∅ at countedLaw
    have originalObservation : original =
        (fun result => ((result.1.1, Multiplicative.toAdd result.1.2), result.2)) <$>
          (runObs Raw.romImpl
            (fun event => Multiplicative.ofAdd (Game.Counted.sourcePolicy event))
            marked).run ∅ := by
      dsimp only [original]
      rw [handlers]
      simp only [AddWriterT.runAdd, runObs, StateT.run_map, Prod.map, id_eq]
    exact originalObservation.trans countedLaw
  have dropKeys : (fun result =>
      ({ toOutcome := result.1.2, cost := result.2 } :
        SigningView.Observation Message (List Byte) (Option (List Byte))
          Game.Counted.SourceCounts)) <$> counted.runAdd =
      Game.Counted.canonicalExperiment FIPS205.scheme adv := by
    simp only [counted, SigningView.countedExperiment, SigningView.countedAfterKeygen,
      Game.Counted.canonicalExperiment, view, main,
      AddWriterT.runAdd_bind, AddWriterT.runAdd_pure, map_bind, map_pure,
      Prod.map, id_eq, add_zero]
    simp only [bind_assoc, pure_bind]
  have originalGame :
      (fun result => (decide (SigningView.Wins id result.1.1.2), result.1.2)) <$>
        original = (Game.securityGame FIPS205.scheme).experiment () adv := by
    rw [← jointExperiment FIPS205.scheme adv, countedSource]
    change _ = (fun result => (decide (SigningView.Wins id result.toOutcome),
      result.cost)) <$> RandomOracleModel.run
        (Game.Counted.canonicalExperiment FIPS205.scheme adv)
    rw [← dropKeys, run_map]
    simp only [RandomOracleModel.run, RandomOracleModel.impl, OracleSpec.romImpl,
      StateT.run'_eq, Functor.map_map]
  have fullSource := physical_original_full_source_counts adv
  dsimp only at fullSource
  have projected := fullSource.symm.map (fun sampled =>
    (decide (SigningView.Wins id sampled.2.1.1.2), sampled.2.1.2))
  simp only [Functor.map_map] at projected
  change _ =ᵈ (fun result =>
    (decide (SigningView.Wins id result.1.1.2), result.1.2)) <$> original at projected
  rw [originalGame] at projected
  exact projected

/-- Successful physical verification performs an original verifier hash. At a nonweak retained
public key its honest message-digest prefix also increments the existing selected-raw metadata.
The statement retains the complete original source vector, keys, outcome and physical cache. -/
theorem physical_verifier_work_and_nonweak_selectedRaw
    (seed : FIPS205.core.PkSeed)
    (adv : Game.Adversary FIPS205.Answer (PublicKeyCore FIPS205.core)) :
    let Alpha := ((PublicKeyCore FIPS205.core) × (SecretKeyCore FIPS205.core)) ×
      SigningView.Outcome Message (List Byte) (Option (List Byte))
    let physical : QueryImpl Common (StateT Raw.QueryCache ProbComp) :=
      eraseObsImpl (Ev := Ev) (Raw.romImpl ∘ₛ (encoding seed).encodeImpl)
    let observed := physical.extendState (aux (spec := Native) (selectedRaw seed))
    let cost : Common.Domain → Game.Counted.SourceCounts :=
      Sum.elim (fun _ => 0) Game.Counted.sourcePolicy
    ∀ out : ((Alpha × Game.Counted.SourceCounts) × (Raw.QueryCache × Meta)),
      out ∈ support (((simulateQ (observed.withAddCost cost)
        (mixedSourceAt seed adv)).runAdd).run (∅, (0, .keygen))) →
      out.1.1.1.1.pkSeed = seed ∧
        (out.1.1.2.verified = true →
          1 ≤ out.1.2 .verifier ∧
            (¬IsWeakKey FIPS205.params out.1.1.1.1 → 1 ≤ out.2.2.1)) := by
  classical
  intro Alpha physical observed cost out member
  let State := (Raw.QueryCache × Meta) × (Game.Counted.SourceCounts × Bool)
  let counted := QueryImpl.sourceCounted (0 : Game.Counted.SourceCounts) cost observed
  have monotone {beta : Type} (body : OracleComp Common beta) (initial : State)
      (result : beta × State)
      (supported : result ∈ support ((simulateQ counted body).run initial)) :
      initial.2.1 .verifier ≤ result.2.2.1 .verifier ∧
        initial.1.2.1 ≤ result.2.1.2.1 := by
    let invariant := fun state : State =>
      initial.2.1 .verifier ≤ state.2.1 .verifier ∧
        initial.1.2.1 ≤ state.1.2.1
    apply simulateQ_run_preservesInv counted invariant ?_ body initial
      ⟨le_rfl, le_rfl⟩ result supported
    intro input state held next hnext
    simp only [counted, QueryImpl.sourceCounted, QueryImpl.extendState_apply,
      mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hnext
    obtain ⟨base, hbase, rfl⟩ := hnext
    simp only [observed, QueryImpl.extendState_apply, mem_support_bind_iff,
      support_pure, Set.mem_singleton_iff] at hbase
    obtain ⟨physicalResult, _, rfl⟩ := hbase
    rcases input with native | event
    · simpa only [invariant, cost, aux, Sum.elim_inl,
        Pi.add_apply, Pi.zero_apply, add_zero] using held
    · cases event <;> simp only [invariant, aux, Pi.add_apply]
      all_goals exact ⟨held.1.trans (Nat.le_add_right _ _),
        held.2.trans (Nat.le_add_right _ _)⟩
  have projection := QueryImpl.source_run_cost (0 : Game.Counted.SourceCounts)
    cost observed (mixedSourceAt seed adv) (∅, (0, .keygen)) 0 false
  simp only [zero_add, Prod.eta, id_map'] at projection
  rw [← projection, support_map] at member
  obtain ⟨actual, actualSupport, rfl⟩ := member
  let typedAlg := romScheme FIPS205.core (Equiv.refl _) FIPS205.deterministicRand (pure seed)
  let view := SLHDSA.SigningView.fromInternalPure FIPS205.params
    (SLHDSA.Concrete.shakeWireCodec FIPS205.params.params)
    (typedAlg.map (simulateQ' (liftTypedImpl (hs := H) (ext := Raw))))
    (fun request : Message =>
      (External.encodePureMessage request.context request.message).toOption)
  let marker : QueryImpl (SigningView.Events.Spec Native Message) (OracleComp Common) :=
    QueryImpl.add (spec₁ := Native)
      (spec₂ := ObsSpec (SigningView.Event Native Message))
      (QueryImpl.ofLift Native (OracleComp Common))
      (fun event => liftM (Common.query (.inr (mixedEventToRaw event))))
  let rawMain := fun pk : PublicKeyCore FIPS205.core =>
    simulateQ (QueryImpl.add (spec₁ := R) (spec₂ := Guarded.Sign)
      (fun input => simulateQ (QueryImpl.ofLift Native (OracleComp (Native + Guarded.Sign)))
        (liftRawImpl (hs := H) input))
      (fun request => liftM ((Native + Guarded.Sign).query (.inr request))))
      (Game.Counted.externalMain adv pk)
  have sourceForm : mixedSourceAt seed adv =
      simulateQ marker (SigningView.Events.fullExperiment view rawMain) := rfl
  let marked := counted ∘ₛ marker
  rw [sourceForm, ← QueryImpl.simulateQ_compose] at actualSupport
  change actual ∈ support ((simulateQ marked
    (SigningView.Events.fullExperiment view rawMain)).run
      ((∅, (0, .keygen)), (0, false))) at actualSupport
  simp only [SigningView.Events.fullExperiment, simulateQ_bind, simulateQ_pure,
    StateT.run_bind, StateT.run_pure, mem_support_bind_iff, support_pure,
    Set.mem_singleton_iff] at actualSupport
  obtain ⟨keys, keySupport, phase, _phaseSupport, verified, verifySupport, rfl⟩ := actualSupport
  have keyProgramSupport : keys.1 ∈ support
      (simulateQ (SigningView.Events.phaseImpl Native Message .keygen) view.keygen) := by
    exact support_simulateQ_run'_subset marked _ _
      (by rw [StateT.run'_eq, support_map]; exact ⟨keys, keySupport, rfl⟩)
  have viewKeySupport := support_simulateQ_subset
    (SigningView.Events.phaseImpl Native Message .keygen) view.keygen keyProgramSupport
  have typedKeySupport : keys.1 ∈ support typedAlg.keygen := by
    apply support_simulateQ_subset (liftTypedImpl (hs := H) (ext := Raw)) typedAlg.keygen
    simpa only [view, SLHDSA.SigningView.fromInternalPure,
      SigningView.rejectingEncoding_keygen, SignatureAlg.map_keygen, simulateQ'_apply]
      using viewKeySupport
  have keySeed : keys.1.1.pkSeed = seed :=
    pkSeed_eq_of_mem_support_romScheme_keygen FIPS205.core (Equiv.refl _) typedKeySupport
  refine ⟨keySeed, ?_⟩
  intro accepted
  let request := phase.1.1.1
  let wire := phase.1.1.2
  let verifier := simulateQ marker
    (simulateQ (SigningView.Events.phaseImpl Native Message .verification)
      (view.verify keys.1.1 request wire))
  have verificationSupport : verified ∈ support
      ((simulateQ counted verifier).run phase.2) := by
    simpa only [verifier, marked, QueryImpl.simulateQ_compose,
      SigningView.Events.viewWithEvents, request, wire] using verifySupport
  obtain ⟨message, signature, framed, decoded⟩ :
      ∃ (message : List Byte)
        (signature : GeneralScheme.SignatureCore FIPS205.params FIPS205.core),
        (External.encodePureMessage request.context request.message).toOption = some message ∧
        (SLHDSA.decodeSignature FIPS205.params
          (SLHDSA.Concrete.shakeWireCodec FIPS205.params.params) wire).toOption =
            some signature := by
    cases frame : (External.encodePureMessage request.context request.message).toOption with
    | none =>
      simp only [verifier, view, SLHDSA.SigningView.fromInternalPure,
        SigningView.rejectingEncoding_verify, frame, simulateQ_pure,
        StateT.run_pure, support_pure, Set.mem_singleton_iff] at verificationSupport
      cases verificationSupport
      simp at accepted
    | some message =>
      cases decode : (SLHDSA.decodeSignature FIPS205.params
          (SLHDSA.Concrete.shakeWireCodec FIPS205.params.params) wire).toOption with
      | none =>
        simp only [verifier, view, SLHDSA.SigningView.fromInternalPure,
          SigningView.rejectingEncoding_verify, frame, decode, simulateQ_pure,
          StateT.run_pure, support_pure, Set.mem_singleton_iff] at verificationSupport
        cases verificationSupport
        simp at accepted
      | some signature => exact ⟨message, signature, rfl, rfl⟩
  let point : H.Domain :=
    .inl (.hmsg signature.randomness keys.1.1.pkSeed keys.1.1.pkRoot message)
  let label : Ev := .ambient .verification (.inr (encode FIPS205.params point))
  let tail := fun digest : SLHDSA.Bytes FIPS205.params.params.m => do
    let parts := splitDigest FIPS205.params.params digest
    let forsPk ← forsPkFromSigM FIPS205.core signature.fors parts.md.toList
      keys.1.1.pkSeed parts.forsAdrs
    (GeneralHypertree.verifyM FIPS205.params FIPS205.core forsPk signature.hypertree
      keys.1.1.pkSeed parts keys.1.1.pkRoot : OracleComp Native Bool)
  let rest : OracleComp Common Bool := simulateQ marker (do
    let digest ← (liftM (Native.query (.inr (.inl point))) :
      OracleComp (SigningView.Events.Spec Native Message) (SLHDSA.Bytes FIPS205.params.params.m))
    simulateQ (SigningView.Events.phaseImpl Native Message .verification) (tail digest))
  have firstHmsg : verifier = (do
      let _ ← (liftM (Common.query (.inr label)) : OracleComp Common PUnit)
      rest) := by
    have nativeVerification :
        simulateQ (liftTypedImpl (hs := H) (ext := Raw))
            (typedAlg.verify keys.1.1 message signature) =
          (GeneralScheme.verifyInternalM FIPS205.params FIPS205.core
            message signature keys.1.1 : OracleComp Native Bool) := by
      dsimp only [typedAlg]
      rw [SLHDSA.Security.romScheme_verify (vp := FIPS205.params) FIPS205.core
        (Equiv.refl FIPS205.core.SkSeed) FIPS205.deterministicRand (pure seed)
        keys.1.1 message signature]
      exact GeneralScheme.verifyInternalM_natural FIPS205.params FIPS205.core
        ({ toMonadHom := simulateQ' (liftTypedImpl (hs := H) (ext := Raw))
           map_query' := by
             intro input
             change simulateQ (liftTypedImpl (hs := H) (ext := Raw))
                 (liftM ((unifSpec + H).query (.inr (.inl input)))) =
               (liftM (Native.query (.inr (.inl (.inl input)))) :
                 OracleComp Native ((publicHashSpec FIPS205.core).Range input))
             rw [simulateQ_spec_query]
             rfl } : HasQuery.QueryHom (publicHashSpec FIPS205.core)
          (OracleComp (unifSpec + H)) (OracleComp Native))
        message signature keys.1.1
    have hmsgQuery :
        (PublicHash.hmsg FIPS205.core signature.randomness keys.1.1.pkSeed
          keys.1.1.pkRoot message : OracleComp Native (SLHDSA.Bytes FIPS205.params.params.m)) =
          (liftM (Native.query (.inr (.inl point))) :
            OracleComp Native (SLHDSA.Bytes FIPS205.params.params.m)) := by
      rfl
    simp only [verifier, view, SLHDSA.SigningView.fromInternalPure,
      SigningView.rejectingEncoding_verify, framed, decoded, SignatureAlg.map_verify]
    rw [nativeVerification,
      GeneralScheme.verifyInternalM_components FIPS205.params FIPS205.core, hmsgQuery]
    simp only [rest, tail, simulateQ_bind]
    simp only [simulateQ_spec_query, SigningView.Events.phaseImpl,
      QueryImpl.preInsert_apply, SigningView.Events.emit]
    simp only [simulateQ_bind, simulateQ_spec_query, marker,
      mixedEventToRaw, label, point, bind_assoc]
    rfl
  let afterMarker : State :=
    ((phase.2.1.1, (phase.2.1.2.1 + selectedRaw seed label, .verification)),
      (phase.2.2.1 + cost (.inr label),
        phase.2.2.2 || decide (¬(phase.2.2.1 + cost (.inr label) ≤ 0))))
  have tailSupport : verified ∈ support ((simulateQ counted rest).run afterMarker) := by
    rw [firstHmsg] at verificationSupport
    simpa only [counted, QueryImpl.sourceCounted, QueryImpl.extendState_apply,
      physical, observed, eraseObsImpl_inr, simulateQ_bind, simulateQ_spec_query,
      StateT.run_bind, StateT.run_pure, pure_bind, aux, label, afterMarker]
      using verificationSupport
  have growth := monotone rest afterMarker verified tailSupport
  have originalUnit : 1 ≤ afterMarker.2.1 .verifier := by
    simp only [afterMarker, cost, Sum.elim_inr, Pi.add_apply, label,
      Game.Counted.sourcePolicy, Game.Counted.sourceKind, Game.hashCost,
      RandomOracleModel.hashCost, Pi.single_eq_same]
    omega
  refine ⟨originalUnit.trans growth.1, ?_⟩
  intro nonweak
  have notThash : ¬IsThashString FIPS205.params
      (IsHonestKey FIPS205.params FIPS205.core) seed
      (encode FIPS205.params
        (.inl (.hmsg signature.randomness seed keys.1.1.pkRoot message))) := by
    intro thash
    have weak := isWeakKey_of_isThashString_encode_hmsg
      (vp := FIPS205.params) (by decide) thash
    apply nonweak
    simpa only [← keySeed] using weak
  have routed := shakeEncoding_route_encode_hmsg (vp := FIPS205.params)
    (hn := by decide) (hnm := by decide) (pkSeed := seed)
    signature.randomness keys.1.1.pkRoot message notThash
  have selected : selectedRaw seed label = 1 := by
    simp only [Guarded.selectedRaw, label, point, keySeed, encoding, routed]
  have selectedUnit : 1 ≤ afterMarker.1.2.1 := by
    dsimp only [afterMarker]
    rw [selected]
    omega
  exact selectedUnit.trans growth.2

/-- One global original joint budget controls reserve work and all attempts after the sampled
public seed. Losing verification remains charged; only a successful nonweak verifier supplies
the selected-raw unit used for the strict winning cap. -/
theorem physical_reserve_global_ae
    (adv : Game.Adversary FIPS205.Answer (PublicKeyCore FIPS205.core)) (q : Nat)
    (hlimit : Game.WithinSigningLimit FIPS205.scheme adv)
    (hbound : (Game.securityGame FIPS205.scheme).HasQueryBound () Game.adversaryWork adv q) :
    let physical := fun seed : FIPS205.core.PkSeed =>
      (eraseObsImpl (Ev := Ev) (Raw.romImpl ∘ₛ (encoding seed).encodeImpl) :
        QueryImpl Common (StateT Raw.QueryCache ProbComp))
    let source := do
      let seed ← ($ᵗ FIPS205.core.PkSeed : ProbComp FIPS205.core.PkSeed)
      let observed := (physical seed).extendState (aux (spec := Native) (selectedRaw seed))
      let out ← ((simulateQ (observed.withAddCost
        (Sum.elim (fun _ : Native.Domain => (0, 0)) (policy true seed)))
        (mixedSourceAt seed adv)).runAdd).run (∅, (0, .keygen))
      pure (seed, out)
    Pr{let sampled ← source}[
      sampled.2.1.2.1 + sampled.2.2.2.1 ≤ 32 * q ∧
        sampled.2.1.2.2 ≤ 2 ^ 64 ∧
        (sampled.2.1.1.2.verified = true ∧
          ¬IsWeakKey FIPS205.params sampled.2.1.1.1.1 →
            1 ≤ sampled.2.2.2.1)] = 1 := by
  classical
  intro physical source
  let Alpha := ((PublicKeyCore FIPS205.core) × (SecretKeyCore FIPS205.core)) ×
    SigningView.Outcome Message (List Byte) (Option (List Byte))
  let originalCost : Common.Domain → Game.Counted.SourceCounts :=
    Sum.elim (fun _ => 0) Game.Counted.sourcePolicy
  let reserveCost := fun seed : FIPS205.core.PkSeed =>
    Sum.elim (fun _ : Native.Domain => (0, 0)) (policy true seed)
  let observed := fun seed : FIPS205.core.PkSeed =>
    (physical seed).extendState (aux (spec := Native) (selectedRaw seed))
  let originalSource := do
    let seed ← ($ᵗ FIPS205.core.PkSeed : ProbComp FIPS205.core.PkSeed)
    let out ← ((simulateQ ((physical seed).withAddCost originalCost)
      (mixedSourceAt seed adv)).runAdd).run ∅
    pure (seed, out)
  have joint := physical_original_joint_game adv
  have workLaw := joint.prEvent_eq (fun result =>
    (∑ kind ∈ Game.adversaryWork, result.2 kind) ≤ q)
  have attemptLaw := joint.prEvent_eq (fun result => result.2 .sign ≤ 2 ^ 64)
  simp only [prEvent_map] at workLaw attemptLaw
  have originalWork : Pr{let sampled ← originalSource}[
      (∑ kind ∈ Game.adversaryWork, sampled.2.1.2 kind) ≤ q] = 1 := by
    exact workLaw.trans hbound
  have originalAttempts : Pr{let sampled ← originalSource}[
      sampled.2.1.2 .sign ≤ 2 ^ 64] = 1 := by
    exact attemptLaw.trans hlimit
  have originalCaps : Pr{let sampled ← originalSource}[
      (∑ kind ∈ Game.adversaryWork, sampled.2.1.2 kind) ≤ q ∧
        sampled.2.1.2 .sign ≤ 2 ^ 64] = 1 := by
    apply (prEvent_eq_one_iff _ _).mpr
    intro sampled member
    exact ⟨(prEvent_eq_one_iff _ _).mp originalWork sampled member,
      (prEvent_eq_one_iff _ _).mp originalAttempts sampled member⟩
  have coupled : OracleComp.ProgramLogic.Relational.RelTriple originalSource source
      (fun left right =>
        left.1 = right.1 ∧ left.2.1.1 = right.2.1.1 ∧
          right.2.1.2.1 + right.2.2.2.1 ≤
            32 * (∑ kind ∈ Game.adversaryWork, left.2.1.2 kind) ∧
          right.2.1.2.2 = left.2.1.2 .sign) := by
    dsimp only [originalSource, source]
    apply OracleComp.ProgramLogic.Relational.relTriple_bind
      (OracleComp.ProgramLogic.Relational.relTriple_refl
        ($ᵗ FIPS205.core.PkSeed : ProbComp FIPS205.core.PkSeed))
    intro seed other same
    cases same
    simp only [bind_pure_comp]
    apply OracleComp.ProgramLogic.Relational.relTriple_map
    apply OracleComp.ProgramLogic.Relational.relTriple_post_mono
      (physical_reserve_original_cost_relation seed (mixedSourceAt seed adv))
    intro left right related
    exact ⟨rfl, related.1, related.2.2.1, related.2.2.2⟩
  have reserveCaps : Pr{let sampled ← source}[
      sampled.2.1.2.1 + sampled.2.2.2.1 ≤ 32 * q ∧
        sampled.2.1.2.2 ≤ 2 ^ 64] = 1 := by
    have bound := OracleComp.ProgramLogic.Relational.prEvent_le_of_relTriple coupled
      (p := fun sampled =>
        (∑ kind ∈ Game.adversaryWork, sampled.2.1.2 kind) ≤ q ∧
          sampled.2.1.2 .sign ≤ 2 ^ 64)
      (q := fun sampled =>
        sampled.2.1.2.1 + sampled.2.2.2.1 ≤ 32 * q ∧
          sampled.2.1.2.2 ≤ 2 ^ 64)
      (fun left right related caps =>
        ⟨related.2.2.1.trans (Nat.mul_le_mul_left 32 caps.1),
          related.2.2.2.trans_le caps.2⟩)
    rw [originalCaps] at bound
    exact le_antisymm (prEvent_le_one _) bound
  have eraseCost {C : Type} [AddMonoid C] (seed : FIPS205.core.PkSeed)
      (charge : Common.Domain → C) :
      (fun out : (Alpha × C) × (Raw.QueryCache × Meta) => (out.1.1, out.2)) <$>
          ((simulateQ ((observed seed).withAddCost charge)
            (mixedSourceAt seed adv)).runAdd).run (∅, (0, .keygen)) =
        (simulateQ (observed seed) (mixedSourceAt seed adv)).run (∅, (0, .keygen)) := by
    have erased := congrArg
      (fun action : StateT (Raw.QueryCache × Meta) ProbComp Alpha =>
        action.run (∅, (0, .keygen)))
      (QueryImpl.fst_map_run_withCost (observed seed)
        (fun input => Multiplicative.ofAdd (charge input)) (mixedSourceAt seed adv))
    simpa only [QueryImpl.withAddCost, AddWriterT.runAdd, StateT.run_map,
      Functor.map_map, Function.comp_def, Prod.map, id_eq] using erased
  apply (prEvent_eq_one_iff _ _).mpr
  intro sampled member
  have caps := (prEvent_eq_one_iff _ _).mp reserveCaps sampled member
  refine ⟨caps.1, caps.2, ?_⟩
  rcases sampled with ⟨seed, result⟩
  intro verifiedNonweak
  have resultSupport : result ∈ support
      (((simulateQ ((observed seed).withAddCost (reserveCost seed))
        (mixedSourceAt seed adv)).runAdd).run (∅, (0, .keygen))) := by
    simp only [source, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at member
    obtain ⟨drawn, _, out, hout, equality⟩ := member
    cases equality
    exact hout
  have plainSupport : (result.1.1, result.2) ∈ support
      ((simulateQ (observed seed) (mixedSourceAt seed adv)).run (∅, (0, .keygen))) := by
    rw [← eraseCost seed (reserveCost seed), support_map]
    exact ⟨result, resultSupport, rfl⟩
  rw [← eraseCost seed originalCost, support_map] at plainSupport
  obtain ⟨originalResult, originalSupport, matching⟩ := plainSupport
  have samePayload : originalResult.1.1 = result.1.1 := (Prod.mk.inj matching).1
  have sameState : originalResult.2 = result.2 := (Prod.mk.inj matching).2
  have actual := physical_verifier_work_and_nonweak_selectedRaw seed adv
    originalResult originalSupport
  have verified : originalResult.1.1.2.verified = true := by
    simpa only [samePayload] using verifiedNonweak.1
  have nonweak : ¬IsWeakKey FIPS205.params originalResult.1.1.1.1 := by
    simpa only [samePayload] using verifiedNonweak.2
  have unit := (actual.2 verified).2 nonweak
  simpa only [sameState] using unit

/-- The original global budgets fund the strict reserve cap on nonweak winning branches.
The guard checks the marker before the complete encoded physical query and its cache effects;
weak winning mass remains an explicit separate term. The physical state and outcome are retained. -/
theorem physical_reserve_nonweak_win_guard
    (adv : Game.Adversary FIPS205.Answer (PublicKeyCore FIPS205.core)) (q : Nat)
    (hlimit : Game.WithinSigningLimit FIPS205.scheme adv)
    (hbound : (Game.securityGame FIPS205.scheme).HasQueryBound () Game.adversaryWork adv q)
    (fallback : (seed : FIPS205.core.PkSeed) →
      (input : Common.Domain) → Common.Range input) :
    let physical := fun seed : FIPS205.core.PkSeed =>
      (eraseObsImpl (Ev := Ev) (Raw.romImpl ∘ₛ (encoding seed).encodeImpl) :
        QueryImpl Common (StateT Raw.QueryCache ProbComp))
    let observed := fun seed : FIPS205.core.PkSeed =>
      (physical seed).extendState (aux (spec := Native) (selectedRaw seed))
    let cost := fun seed : FIPS205.core.PkSeed =>
      Sum.elim (fun _ : Native.Domain => (0, 0)) (policy true seed)
    let source := do
      let seed ← ($ᵗ FIPS205.core.PkSeed : ProbComp FIPS205.core.PkSeed)
      let out ← ((simulateQ ((observed seed).withAddCost (cost seed))
        (mixedSourceAt seed adv)).runAdd).run (∅, (0, .keygen))
      pure (seed, out)
    let guarded := do
      let seed ← ($ᵗ FIPS205.core.PkSeed : ProbComp FIPS205.core.PkSeed)
      let out ← (simulateQ (QueryImpl.guardQueryBudget (32 * q - 1, 2 ^ 64)
        (cost seed) (observed seed) (fallback seed)) (mixedSourceAt seed adv)).run
          ((∅, (0, .keygen)), ((0, 0), false))
      pure (seed, out)
    (Pr{let sampled ← guarded}[
      SigningView.Wins id sampled.2.1.2 ∧
        ¬IsWeakKey FIPS205.params sampled.2.1.1.1 ∧ sampled.2.2.2.2 = false] =
      Pr{let sampled ← source}[
        SigningView.Wins id sampled.2.1.1.2 ∧
          ¬IsWeakKey FIPS205.params sampled.2.1.1.1.1]) ∧
    (Pr{let out ← (Game.securityGame FIPS205.scheme).experiment () adv}[out.1 = true] ≤
      Pr{let sampled ← guarded}[
        SigningView.Wins id sampled.2.1.2 ∧ sampled.2.2.2.2 = false] +
      Pr{let sampled ← source}[
        SigningView.Wins id sampled.2.1.1.2 ∧
          IsWeakKey FIPS205.params sampled.2.1.1.1.1]) := by
  classical
  intro physical observed cost source guarded
  let Alpha := ((PublicKeyCore FIPS205.core) × (SecretKeyCore FIPS205.core)) ×
    SigningView.Outcome Message (List Byte) (Option (List Byte))
  let event := fun (_seed : FIPS205.core.PkSeed)
      (result : (Alpha × (Nat × Nat)) × (Raw.QueryCache × Meta)) =>
    SigningView.Wins id result.1.1.2 ∧ ¬IsWeakKey FIPS205.params result.1.1.1.1
  have globalBudget := physical_reserve_global_ae adv q hlimit hbound
  change Pr{let sampled ← source}[
    sampled.2.1.2.1 + sampled.2.2.2.1 ≤ 32 * q ∧
      sampled.2.1.2.2 ≤ 2 ^ 64 ∧
      (sampled.2.1.1.2.verified = true ∧
        ¬IsWeakKey FIPS205.params sampled.2.1.1.1.1 →
          1 ≤ sampled.2.2.2.1)] = 1 at globalBudget
  have eventCaps : Pr{let sampled ← source}[
      event sampled.1 sampled.2 → sampled.2.1.2 ≤ (32 * q - 1, 2 ^ 64)] = 1 := by
    apply (prEvent_eq_one_iff _ _).mpr
    intro sampled member winning
    have facts := (prEvent_eq_one_iff _ _).mp globalBudget sampled member
    have unit := facts.2.2 ⟨winning.1.1, winning.2⟩
    rw [Prod.le_def]
    exact ⟨by omega, facts.2.1⟩
  have nonweak :
      Pr{let sampled ← guarded}[
        SigningView.Wins id sampled.2.1.2 ∧
          ¬IsWeakKey FIPS205.params sampled.2.1.1.1 ∧ sampled.2.2.2.2 = false] =
      Pr{let sampled ← source}[
        SigningView.Wins id sampled.2.1.1.2 ∧
          ¬IsWeakKey FIPS205.params sampled.2.1.1.1.1] := by
    have equality :=
      QueryImpl.prEvent_bind_guardQueryBudget_and_not_aborted_eq_source_of_ae_event_caps
        ($ᵗ FIPS205.core.PkSeed : ProbComp FIPS205.core.PkSeed)
        (fun _ => (32 * q - 1, 2 ^ 64)) cost observed fallback
        (fun seed => mixedSourceAt seed adv) (fun _ => pure (∅, (0, .keygen))) event
        (by simpa only [pure_bind] using eventCaps)
    have zeroPair : (0 : Nat × Nat) = (0, 0) := rfl
    simpa only [pure_bind, event, guarded, source, and_assoc, zeroPair] using equality
  refine ⟨nonweak, ?_⟩
  let originalCost : Common.Domain → Game.Counted.SourceCounts :=
    Sum.elim (fun _ => 0) Game.Counted.sourcePolicy
  let originalSource := do
    let seed ← ($ᵗ FIPS205.core.PkSeed : ProbComp FIPS205.core.PkSeed)
    let out ← ((simulateQ ((physical seed).withAddCost originalCost)
      (mixedSourceAt seed adv)).runAdd).run ∅
    pure (seed, out)
  have sameAlpha (seed : FIPS205.core.PkSeed) :
      (fun out => out.1.1) <$>
          ((simulateQ ((physical seed).withAddCost originalCost)
            (mixedSourceAt seed adv)).runAdd).run ∅ =ᵈ
        (fun out => out.1.1) <$>
          ((simulateQ ((observed seed).withAddCost (cost seed))
            (mixedSourceAt seed adv)).runAdd).run (∅, (0, .keygen)) := by
    exact OracleComp.ProgramLogic.Relational.evalDistEq_map_of_relTriple
      (OracleComp.ProgramLogic.Relational.relTriple_post_mono
        (physical_reserve_original_cost_relation seed (mixedSourceAt seed adv))
        (fun _ _ related => related.1))
  have alphaFamily : (fun sampled => sampled.2.1.1) <$> originalSource =ᵈ
      (fun sampled => sampled.2.1.1) <$> source := by
    simp only [originalSource, source, map_bind, map_pure]
    apply EvalDistEq.bind_right
    intro seed
    simpa only [map_eq_bind_pure_comp, Function.comp_def] using sameAlpha seed
  have gameFamily := (physical_original_joint_game adv).map Prod.fst
  simp only [Functor.map_map] at gameFamily
  change (fun sampled => decide (SigningView.Wins id sampled.2.1.1.2)) <$>
      originalSource =ᵈ Prod.fst <$>
        (Game.securityGame FIPS205.scheme).experiment () adv at gameFamily
  have winningFamily := alphaFamily.map
    (fun alpha => decide (SigningView.Wins id alpha.2))
  simp only [Functor.map_map] at winningFamily
  have reserveGame := winningFamily.symm.trans gameFamily
  have originalWinning :
      Pr{let out ← (Game.securityGame FIPS205.scheme).experiment () adv}[out.1 = true] =
        Pr{let sampled ← source}[SigningView.Wins id sampled.2.1.1.2] := by
    have equality := reserveGame.prEvent_eq (fun winning => winning = true)
    simpa only [prEvent_map, decide_eq_true_eq] using equality.symm
  rw [originalWinning]
  have split : Pr{let sampled ← source}[SigningView.Wins id sampled.2.1.1.2] ≤
      Pr{let sampled ← source}[
        SigningView.Wins id sampled.2.1.1.2 ∧
          ¬IsWeakKey FIPS205.params sampled.2.1.1.1.1] +
      Pr{let sampled ← source}[
        SigningView.Wins id sampled.2.1.1.2 ∧
          IsWeakKey FIPS205.params sampled.2.1.1.1.1] := by
    apply (prEvent_mono source _ _ (fun sampled winning => ?_)).trans
      (prEvent_or_le source _ _)
    by_cases weak : IsWeakKey FIPS205.params sampled.2.1.1.1.1
    · exact Or.inr ⟨winning, weak⟩
    · exact Or.inl ⟨winning, weak⟩
  calc
    _ ≤ _ := split
    _ = Pr{let sampled ← guarded}[
          SigningView.Wins id sampled.2.1.2 ∧
            ¬IsWeakKey FIPS205.params sampled.2.1.1.1 ∧ sampled.2.2.2.2 = false] +
        Pr{let sampled ← source}[
          SigningView.Wins id sampled.2.1.1.2 ∧
            IsWeakKey FIPS205.params sampled.2.1.1.1.1] := by rw [nonweak]
    _ ≤ _ := add_le_add (prEvent_mono guarded _ _
      (fun _ winning => ⟨winning.1, winning.2.2⟩)) le_rfl

end SLHDSA.SHAKE128s.Bridge.SharedExperiment
