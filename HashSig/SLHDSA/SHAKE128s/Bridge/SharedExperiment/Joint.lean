/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module
public import HashSig.SLHDSA.SHAKE128s.Bridge.SharedExperiment.Observation
public import HashSig.SLHDSA.SHAKE128s.Statement.FIPS205
public import VCVio.OracleComp.QueryTracking.Enforcement
import VCVio.CryptoFoundations.SignatureAlg.CountedExperiment.CostMap

/-!
# Joint winning and source-count transport

The same complete counted program is interpreted once by the shared random oracle.
Raw optional replies determine the same fresh pair, and the five counters are retained jointly.
-/

public section

open OracleComp OracleSpec SignatureAlg
open SLHDSA.SHAKE128s

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
    let marked : OracleComp
        (SigningView.Events.Spec (Game.World FIPS205.Answer) Message)
        (((PublicKeyCore FIPS205.core) × (SecretKeyCore FIPS205.core)) ×
          SigningView.Outcome Message Bytes (Option Bytes)) := do
      let keys ← (SigningView.Events.viewWithEvents view).keygen
      let (forgery, rawLog) ← (SigningView.Events.viewWithEvents view).runWithSigningOracle
        keys.1 keys.2 (SigningView.Events.mainWithEvents main keys.1)
      let verified ← (SigningView.Events.viewWithEvents view).verify
        keys.1 forgery.1 forgery.2
      return (keys, ⟨forgery, rawLog, verified⟩)
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

end SLHDSA.SHAKE128s.Bridge.SharedExperiment
