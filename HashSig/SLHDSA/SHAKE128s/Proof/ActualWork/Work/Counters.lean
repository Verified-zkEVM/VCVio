/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module

public import HashSig.SLHDSA.SHAKE128s.Bridge.SharedExperiment.Joint
import all HashSig.SLHDSA.SHAKE128s.Bridge.SharedExperiment.Joint.Source
import VCVio.OracleComp.SimSemantics.WriterT.Core
import Lean.Elab.Tactic.Omega

/-! # Projecting native source counts through the guarded experiment

The physical byte cache, complete source counts, generated key pair and chronological raw
outcome remain joint when the original experiment exposes its sampled public seed.
-/

public section

open OracleComp OracleSpec SignatureAlg
open SLHDSA SLHDSA.Security SLHDSA.SHAKE128s

namespace SLHDSA.SHAKE128s.Bridge.SharedExperiment.Guarded

/-- Every selected message digest retains one unit of the original work allowance.
The signing-attempt coordinate agrees exactly with the original event policy. -/
theorem policy_true_work_add_selectedRaw_le_original
    (seed : FIPS205.core.PkSeed) (event : Ev) :
    (policy true seed event).1 + selectedRaw seed event ≤
        32 * (originalPolicy event).1 ∧
      (policy true seed event).2 = (originalPolicy event).2 := by
  classical
  have reserveBound (bytes : List Byte) :
      reserveExtra seed (.ambient .adversary (.inr bytes)) +
        selectedRaw seed (.ambient .adversary (.inr bytes)) ≤ 31 := by
    cases routed : (encoding seed).route bytes with
    | none =>
      simp only [reserveExtra, selectedRaw, routed]
      omega
    | some typed =>
      rcases typed with publicQuery | privateInput
      · cases publicQuery <;> simp only [reserveExtra, selectedRaw, routed]
        all_goals first | omega | (split_ifs <;> omega)
      · simp only [reserveExtra, selectedRaw, routed]
        split_ifs
        all_goals omega
  cases event with
  | signingAttempt request =>
    simp [policy, originalPolicy, reserveExtra, selectedRaw, Game.Counted.sourcePolicy]
  | ambient phase input =>
    cases phase with
    | keygen =>
      simp [policy, originalPolicy, reserveExtra, selectedRaw,
        Game.Counted.sourcePolicy, Game.Counted.sourceKind]
    | signer =>
      simp [policy, originalPolicy, reserveExtra, selectedRaw,
        Game.Counted.sourcePolicy, Game.Counted.sourceKind]
    | adversary =>
      rcases input with sample | bytes
      · simp [policy, originalPolicy, reserveExtra, selectedRaw,
          Game.Counted.sourcePolicy, Game.Counted.sourceKind,
          Game.hashCost, RandomOracleModel.hashCost]
      · simpa [policy, originalPolicy, reserveExtra, selectedRaw,
          Game.Counted.sourcePolicy, Game.Counted.sourceKind,
          Game.hashCost, RandomOracleModel.hashCost, Nat.add_assoc] using
          Nat.add_le_add_left (reserveBound bytes) 1
    | verification =>
      rcases input with sample | bytes
      · simp [policy, originalPolicy, reserveExtra, selectedRaw,
          Game.Counted.sourcePolicy, Game.Counted.sourceKind,
          Game.hashCost, RandomOracleModel.hashCost]
      · simpa [policy, originalPolicy, reserveExtra, selectedRaw,
          Game.Counted.sourcePolicy, Game.Counted.sourceKind,
          Game.hashCost, RandomOracleModel.hashCost, Nat.add_assoc] using
          Nat.add_le_add_left (reserveBound bytes) 1

end SLHDSA.SHAKE128s.Bridge.SharedExperiment.Guarded

namespace SLHDSA.SHAKE128s.Bridge.SharedExperiment

/-- The physical byte execution retains its public seed, full key pair, chronological
outcome, complete source vector and byte cache jointly across fixed-seed mixed sources. -/
theorem physical_original_full_source_counts
    (adv : Game.Adversary FIPS205.Answer (PublicKeyCore FIPS205.core)) :
    let Raw := shakeSpec FIPS205.params
    let H := hashSpec FIPS205.core
    let R := Game.World FIPS205.Answer
    let Ev := SigningView.Event R Message
    let Native := unifSpec + (H + Raw)
    let Common := Native + ObsSpec Ev
    let Alpha := ((PublicKeyCore FIPS205.core) × (SecretKeyCore FIPS205.core)) ×
      SigningView.Outcome Message (List Byte) (Option (List Byte))
    let Counts := Game.Counted.SourceCounts
    let rawHandler : QueryImpl (SigningView.Events.Spec R Message)
        (StateT Raw.QueryCache ProbComp) :=
      SigningView.Events.handlerWithEvents (Request := Message) Raw.romImpl
    let rawCost : (SigningView.Events.Spec R Message).Domain → Counts :=
      Sum.elim (fun _ => 0) Game.Counted.sourcePolicy
    let mixedCost : Common.Domain → Counts :=
      Sum.elim (fun _ => 0) Game.Counted.sourcePolicy
    let physical := fun seed : FIPS205.core.PkSeed =>
      (eraseObsImpl (Ev := Ev)
        (Raw.romImpl ∘ₛ (Guarded.encoding seed).encodeImpl) :
        QueryImpl Common (StateT Raw.QueryCache ProbComp))
    let original := ((simulateQ (rawHandler.withAddCost rawCost)
      (SigningView.Events.fullExperiment (Game.Counted.externalView FIPS205.scheme)
        (Game.Counted.externalMain adv))).runAdd).run ∅
    (fun out : ((Alpha × Counts) × Raw.QueryCache) =>
      (out.1.1.1.1.pkSeed, out)) <$> original =ᵈ
      (do
        let seed ← ($ᵗ FIPS205.core.PkSeed : ProbComp FIPS205.core.PkSeed)
        let out ← ((simulateQ ((physical seed).withAddCost mixedCost)
          (mixedSourceAt seed adv)).runAdd).run ∅
        pure (seed, out)) := by
  classical
  intro Raw H R Ev Native Common Alpha Counts rawHandler rawCost mixedCost physical original
  let CostState := AddWriterT Counts (StateT Raw.QueryCache ProbComp)
  let _ : LawfulMonadLift (StateT Raw.QueryCache ProbComp) CostState := by
    dsimp only [CostState]
    constructor
    · intro alpha value
      apply WriterT.ext
      simp [MonadLift.monadLift]
    · intro alpha beta action next
      apply WriterT.ext
      simp [MonadLift.monadLift]
  let rawCounted : QueryImpl (SigningView.Events.Spec R Message) CostState :=
    rawHandler.withAddCost rawCost
  let rawInclude : QueryImpl R (OracleComp (SigningView.Events.Spec R Message)) :=
    QueryImpl.ofLift R (OracleComp (SigningView.Events.Spec R Message))
  let marked : OracleComp (SigningView.Events.Spec R Message) Alpha :=
    SigningView.Events.fullExperiment (Game.Counted.externalView FIPS205.scheme)
      (Game.Counted.externalMain adv)
  let fixedRaw := fun seed : FIPS205.core.PkSeed =>
    SigningView.Events.fullExperiment
      (pureShakeView FIPS205.params FIPS205.deterministicRand (pure seed))
      (Game.Counted.externalMain adv)
  let encodeObserved := fun seed : FIPS205.core.PkSeed =>
    (QueryImpl.add (spec₁ := Native) (spec₂ := ObsSpec Ev)
      (fun input => simulateQ rawInclude ((Guarded.encoding seed).encodeImpl input))
      (fun event => liftM ((R + ObsSpec Ev).query (.inr event))) :
      QueryImpl Common (OracleComp (SigningView.Events.Spec R Message)))
  have includeQuery (input : R.Domain) :
      rawInclude input =
        (liftM ((R + ObsSpec Ev).query (.inl input)) :
          OracleComp (SigningView.Events.Spec R Message) (R.Range input)) := by
    rcases input with sample | bytes <;> rfl
  have rawNative {alpha : Type} (body : OracleComp R alpha) :
      simulateQ rawCounted (simulateQ rawInclude body) =
        (liftM (simulateQ Raw.romImpl body) : CostState alpha) := by
    rw [← simulateQ_liftTarget]
    apply QueryImpl.simulateQ_simulateQ_eq_of_apply
    intro input
    rw [includeQuery, simulateQ_spec_query]
    apply WriterT.ext
    simp [rawCounted, rawHandler, rawCost, QueryImpl.withAddCost_apply,
      SigningView.Events.handlerWithEvents, AddWriterT.addTell]
  have encodingFold {alpha : Type} (seed : FIPS205.core.PkSeed)
      (program : OracleComp Common alpha) :
      simulateQ rawCounted (simulateQ (encodeObserved seed) program) =
        simulateQ ((physical seed).withAddCost mixedCost) program := by
    apply QueryImpl.simulateQ_simulateQ_eq_of_apply
    rintro (input | event)
    · change simulateQ rawCounted
        (simulateQ rawInclude ((Guarded.encoding seed).encodeImpl input)) = _
      rw [rawNative]
      apply WriterT.ext
      simp [physical, mixedCost, QueryImpl.withAddCost_apply, eraseObsImpl_inl,
        QueryImpl.apply_compose, AddWriterT.addTell]
    · change simulateQ rawCounted
        (liftM ((R + ObsSpec Ev).query (.inr event))) = _
      rw [simulateQ_spec_query]
      apply WriterT.ext
      simp [rawCounted, rawHandler, rawCost, physical, mixedCost,
        QueryImpl.withAddCost_apply, SigningView.Events.handlerWithEvents,
        eraseObsImpl_inr, AddWriterT.addTell]
  have fixedFold (seed : FIPS205.core.PkSeed) :
      ((simulateQ rawCounted (fixedRaw seed)).runAdd).run ∅ =
        ((simulateQ ((physical seed).withAddCost mixedCost)
          (mixedSourceAt seed adv)).runAdd).run ∅ := by
    have encoded := simulateQ_encode_mixedSourceAt seed adv
    dsimp only at encoded
    change simulateQ (encodeObserved seed) (mixedSourceAt seed adv) = fixedRaw seed at encoded
    rw [← encoded, encodingFold]
  let fromUniform : QueryImpl unifSpec (OracleComp R) :=
    QueryImpl.ofLift unifSpec (OracleComp R)
  let uniform : QueryImpl unifSpec CostState :=
    ((QueryImpl.id' unifSpec).liftTarget (StateT Raw.QueryCache ProbComp)).liftTarget
      CostState
  have uniformPrefix {alpha : Type} (body : ProbComp alpha) :
      simulateQ rawCounted
        (simulateQ (SigningView.Events.phaseImpl R Message .keygen)
          (liftM body : OracleComp R alpha)) =
        (liftM (liftM body : StateT Raw.QueryCache ProbComp alpha) : CostState alpha) := by
    change simulateQ rawCounted
      (simulateQ (SigningView.Events.phaseImpl R Message .keygen)
        (simulateQ fromUniform body)) = _
    rw [← QueryImpl.simulateQ_compose]
    calc
      _ = simulateQ uniform body := by
        apply QueryImpl.simulateQ_simulateQ_eq_of_apply
        intro sample
        have sampleQuery : fromUniform sample =
            (liftM (R.query (.inl sample)) : OracleComp R (unifSpec.Range sample)) := by
          simpa only [fromUniform, QueryImpl.ofLift_apply,
            OracleQuery.liftM_add_left_query] using
            (OracleComp.liftM_eq_liftM_liftM (spec := unifSpec) (superSpec := R)
              (unifSpec.query sample))
        rw [QueryImpl.simulateQ_compose, sampleQuery]
        rw [simulateQ_spec_query]
        apply WriterT.ext
        apply StateT.ext
        intro cache
        simp [rawCounted, rawHandler, rawCost, uniform, CostState,
          SigningView.Events.phaseImpl,
          SigningView.Events.emit, seqRight_eq_bind, simulateQ_bind,
          QueryImpl.withAddCost_apply, SigningView.Events.handlerWithEvents,
          QueryImpl.id'_apply, AddWriterT.addTell,
          Game.Counted.sourcePolicy, Game.Counted.sourceKind,
          Game.hashCost, RandomOracleModel.hashCost, OracleSpec.romImpl, unifFwdImpl]
      _ = _ := by
        simp only [uniform, simulateQ_liftTarget, simulateQ_id']
  have chronological := actualMarkedSource_publicSeed_joint adv
  dsimp only at chronological
  let repack : ((FIPS205.core.PkSeed × Alpha) × Counts) × Raw.QueryCache →
      FIPS205.core.PkSeed × ((Alpha × Counts) × Raw.QueryCache) :=
    fun out => (out.1.1.1, ((out.1.1.2, out.1.2), out.2))
  have folded := congrArg (fun program : OracleComp
      (SigningView.Events.Spec R Message) (FIPS205.core.PkSeed × Alpha) =>
    ((simulateQ rawCounted program).runAdd).run ∅) chronological
  have repacked := congrArg (fun action => repack <$> action) folded
  simp only [simulateQ_map, simulateQ_bind, simulateQ_pure] at repacked
  rw [uniformPrefix] at repacked
  have sourceFamily :
      (fun out : ((Alpha × Counts) × Raw.QueryCache) =>
        (out.1.1.1.1.pkSeed, out)) <$> original =
      (do
        let seed ← ($ᵗ FIPS205.core.PkSeed : ProbComp FIPS205.core.PkSeed)
        let out ← ((simulateQ rawCounted (fixedRaw seed)).runAdd).run ∅
        pure (seed, out)) := by
    change (fun out : ((Alpha × Counts) × Raw.QueryCache) =>
        (out.1.1.1.1.pkSeed, out)) <$>
        ((simulateQ rawCounted marked).runAdd).run ∅ = _
    simpa only [repack, marked, fixedRaw, id_eq,
      AddWriterT.runAdd_bind, AddWriterT.runAdd_map,
      AddWriterT.runAdd_pure, AddWriterT.runAdd_liftM,
      StateT.run_bind, StateT.run_map, StateT.run_pure, StateT.run_liftM,
      map_bind, bind_map_left, map_pure, bind_assoc, pure_bind, zero_add, add_zero,
      Functor.map_map, Function.comp_def, Prod.map, Prod.eta] using repacked
  have equality :
      (fun out : ((Alpha × Counts) × Raw.QueryCache) =>
        (out.1.1.1.1.pkSeed, out)) <$> original =
      (do
        let seed ← ($ᵗ FIPS205.core.PkSeed : ProbComp FIPS205.core.PkSeed)
        let out ← ((simulateQ ((physical seed).withAddCost mixedCost)
          (mixedSourceAt seed adv)).runAdd).run ∅
        pure (seed, out)) := by
    rw [sourceFamily]
    apply bind_congr
    intro seed
    rw [fixedFold]
  rw [equality]

end SLHDSA.SHAKE128s.Bridge.SharedExperiment
