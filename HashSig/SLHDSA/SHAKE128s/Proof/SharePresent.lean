/-
Copyright (c) 2026 Tom Wambsgans. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Wambsgans
-/

module

public import HashSig.SLHDSA.SHAKE128s.Proof.ShareBound
public import HashSig.SLHDSA.SHAKE128s.Proof.TableTail
public import HashSig.SLHDSA.SHAKE128s.Proof.RecordedStripping
public import HashSig.SLHDSA.SHAKE128s.Proof.TouchedKeys

/-!
# The real game, flattened

The shared half's event is read off `RecordedTail.recordedTail` at a drawn table. To compare it
with the lenient game it has to be one handler's run over the adversary's own oracles, as the
lenient game is. This file gets it there in two moves.

* **The chain** (`probEvent_recordedTail_linked`): the outer count is dropped, the honest phase
  stripped, the keys handed in, and the game becomes one computation — `TableTail`'s chain,
  carried with the record the event reads.
* **The flattening** (`run_flat`, `run_flatVerify`): the three layers the linked run nests — the
  phase's cost writer, the uncharged signing handler, and the random oracle — are one handler
  over the adversary's oracles, with the tally, the log and the cache as its state; and the
  verifier's two layers likewise.
-/

public section

open OracleComp OracleSpec ENNReal

namespace SlhDsaSecurity.SharePresent

variable {α : Type}

open Security CanonicalGraph WarmedGame WalkTable TableTail RecordedQueries RecordedPhase

attribute [local irreducible] WarmedGame.afterSeeds Scheme.verify Scheme.keygenInternal
  Security.countQueries

/-! ## The recorded tail is the linked run -/

/-- **The recorded tail at a drawn table is the linked game**, the record carried. -/
theorem probEvent_recordedTail_linked (adversary : Adversary) (prfSeed publicSeed : Digest)
    (table : Cells × Padding) (event : (Outcome × Multiset Bytes) × QueryCache HashSpec → Prop) :
    Pr{let result ← RecordedTail.recordedTail adversary (walkOfTable prfSeed publicSeed table)}[
        event (result.1.1, result.2)] =
      Pr{let result ← linkedRun adversary prfSeed publicSeed table}[
        event (LinkedGame.outcomeOf result.1, result.2)] := by
  have hmap : (simulateQ KeygenUniform.rom (RecordedTail.recordedAfterSeeds adversary
        (walkOfTable prfSeed publicSeed table).1.1)).run (walkOfTable prfSeed publicSeed table).2 =
      (fun result : ((Outcome × Multiset Bytes) × Nat) × QueryCache HashSpec =>
        (result.1.1, result.2)) <$>
        RecordedTail.recordedTail adversary (walkOfTable prfSeed publicSeed table) := by
    conv_lhs => rw [← RecordedBudget.map_countAllHashes (RecordedTail.recordedAfterSeeds adversary
      (walkOfTable prfSeed publicSeed table).1.1)]
    rw [simulateQ_map, StateT.run_map]
    rfl
  have hstrip := RecordedStripping.evalDist_run_recordedAfterSeeds adversary
    (walkOfTable prfSeed publicSeed table).1.1 (walkOfTable prfSeed publicSeed table).2
    (walkOfTable prfSeed publicSeed table).2 (StrippedGame.Extends.refl _)
  have hkeys : (simulateQ KeygenUniform.rom (RecordedQueries.recordedAfterSeeds adversary
        ((walkOfTable prfSeed publicSeed table).1.1)
        (walkOfTable prfSeed publicSeed table).2)).run
          (walkOfTable prfSeed publicSeed table).2 =
      (simulateQ KeygenUniform.rom (KeygenValue.recordedAfterSeedsAt adversary
        (keysOf prfSeed publicSeed table)
        (walkOfTable prfSeed publicSeed table).2)).run
          (walkOfTable prfSeed publicSeed table).2 := by
    rw [walkOfTable_cache prfSeed publicSeed table]
    exact KeygenValue.run_recordedAfterSeeds adversary
      (table.1 Node.secretSeed, prfSeed, publicSeed) (fullOutput table.1 table.2)
  rw [← prEvent_map (RecordedTail.recordedTail adversary (walkOfTable prfSeed publicSeed table))
      (fun result : ((Outcome × Multiset Bytes) × Nat) × QueryCache HashSpec =>
        (result.1.1, result.2)) event, ← hmap, ← hstrip.prEvent_eq event, hkeys,
    LinkedGame.recordedAfterSeedsAt_eq, simulateQ_map, StateT.run_map, prEvent_map, linkedRun]

/-! ## The adversary's phase, flattened -/

/-- The flattened state: the phase's tally, the signing log, and the oracle's cache. -/
abbrev RealState := Multiplicative Tally × SigningLog × QueryCache HashSpec

/-- **The real phase as one handler** over the adversary's oracles: a world query is the oracle's
step, charged; a signing request runs the signer against the oracle and is logged. -/
@[expose] noncomputable def realImpl (signer : Message → OracleComp OracleWorld (Option Bytes)) :
    QueryImpl (OracleWorld + SigningSpec) (StateT RealState ProbComp) :=
  fun queried state => match queried with
    | Sum.inl world =>
        (fun z => (z.1, (state.1 * Multiplicative.ofAdd (phaseCost (Sum.inl world)), state.2.1,
          z.2))) <$> (KeygenUniform.rom world).run state.2.2
    | Sum.inr request =>
        (fun z => (z.1, (state.1 * Multiplicative.ofAdd (phaseCost (Sum.inr request)),
          state.2.1 ++ [⟨request, z.1⟩], z.2))) <$>
          (simulateQ KeygenUniform.rom (signer request)).run state.2.2

theorem realImpl_world_run (signer : Message → OracleComp OracleWorld (Option Bytes))
    (world : OracleWorld.Domain) (state : RealState) :
    ((realImpl signer) (Sum.inl world)).run state =
      (fun z => (z.1, (state.1 * Multiplicative.ofAdd (phaseCost (Sum.inl world)), state.2.1,
        z.2))) <$> (KeygenUniform.rom world).run state.2.2 := rfl

theorem realImpl_request_run (signer : Message → OracleComp OracleWorld (Option Bytes))
    (request : Message) (state : RealState) :
    ((realImpl signer) (Sum.inr request)).run state =
      (fun z => (z.1, (state.1 * Multiplicative.ofAdd (phaseCost (Sum.inr request)),
        state.2.1 ++ [⟨request, z.1⟩], z.2))) <$>
        (simulateQ KeygenUniform.rom (signer request)).run state.2.2 := rfl

theorem run_ofLift_world (world : OracleWorld.Domain) (log : SigningLog) :
    ((QueryImpl.ofLift OracleWorld (StateT SigningLog (OracleComp OracleWorld))) world).run log =
      (fun answer => (answer, log)) <$>
        (liftM (OracleWorld.query world) : OracleComp OracleWorld (OracleWorld.Range world)) := by
  have h := LinkedGame.run_simulateQ_ofLift
    (liftM (OracleWorld.query world) : OracleComp OracleWorld (OracleWorld.Range world)) log
  rwa [simulateQ_spec_query] at h

theorem rom_run_ofLift_world (world : OracleWorld.Domain) (log : SigningLog)
    (cache : QueryCache HashSpec) :
    (simulateQ KeygenUniform.rom
        (((QueryImpl.ofLift OracleWorld (StateT SigningLog (OracleComp OracleWorld))) world).run
          log)).run cache =
      (fun z => ((z.1, log), z.2)) <$> (KeygenUniform.rom world).run cache := by
  erw [run_ofLift_world]
  rw [map_eq_bind_pure_comp, simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
  simp

theorem run_unchargedSigner (signer : Message → OracleComp OracleWorld (Option Bytes))
    (request : Message) (log : SigningLog) :
    (unchargedSigner signer request).run log =
      (fun answer => (answer, log ++ [⟨request, answer⟩])) <$> signer request := by
  simp only [unchargedSigner, StateT.run_bind, StateT.run_monadLift, StateT.run_modify,
    StateT.run_pure, map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_def]
  rfl

theorem rom_run_unchargedSigner (signer : Message → OracleComp OracleWorld (Option Bytes))
    (request : Message) (log : SigningLog) (cache : QueryCache HashSpec) :
    (simulateQ KeygenUniform.rom ((unchargedSigner signer request).run log)).run cache =
      (fun z => ((z.1, log ++ [⟨request, z.1⟩]), z.2)) <$>
        (simulateQ KeygenUniform.rom (signer request)).run cache := by
  rw [run_unchargedSigner, simulateQ_map, StateT.run_map]

theorem run_addCost_query_bind {ι : Type} {spec : OracleSpec ι} {ω : Type} [AddCommMonoid ω]
    {α : Type} (cost : spec.Domain → ω) (queried : spec.Domain)
    (next : spec.Range queried → OracleComp spec α) :
    (simulateQ (addCostOracle cost) (liftM (spec.query queried) >>= next)).run =
      liftM (spec.query queried) >>= fun answer =>
        (fun result => (result.1, Multiplicative.ofAdd (cost queried) * result.2)) <$>
          (simulateQ (addCostOracle cost) (next answer)).run := by
  simp only [simulateQ_bind, simulateQ_spec_query, addCostOracle, QueryImpl.withAddCost,
    QueryImpl.withCost]
  simp [map_bind, bind_map_left]

/-- **The phase's three layers are one handler.** -/
theorem run_flat (signer : Message → OracleComp OracleWorld (Option Bytes)) {α : Type}
    (computation : OracleComp (OracleWorld + SigningSpec) α) :
    ∀ (tally : Multiplicative Tally) (log : SigningLog) (cache : QueryCache HashSpec),
      (fun z => ((z.1.1.1, tally * z.1.1.2), z.1.2, z.2)) <$>
          (simulateQ KeygenUniform.rom ((simulateQ (unchargedPhase signer)
            ((simulateQ (addCostOracle phaseCost) computation).run)).run log)).run cache =
        (fun z => ((z.1, z.2.1), z.2.2.1, z.2.2.2)) <$>
          (simulateQ (realImpl signer) computation).run (tally, log, cache) := by
  induction computation using OracleComp.inductionOn with
  | pure value => intro tally log cache; simp
  | query_bind queried next ih =>
    intro tally log cache
    rw [run_addCost_query_bind, simulateQ_bind, StateT.run_bind, simulateQ_bind, StateT.run_bind,
      simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
    rcases queried with world | request
    · simp only [unchargedPhase, QueryImpl.add_apply_inl]
      erw [rom_run_ofLift_world]
      simp only [simulateQ_map, StateT.run_map, simulateQ_spec_query, realImpl_world_run,
        map_bind, Functor.map_map]
      erw [bind_map_left, bind_map_left]
      refine bind_congr fun p => ?_
      convert ih p.1 (tally * Multiplicative.ofAdd (phaseCost (Sum.inl world))) log p.2 using 2
      · funext a
        rw [mul_assoc]
      · rfl
    · simp only [unchargedPhase, QueryImpl.add_apply_inr]
      erw [rom_run_unchargedSigner]
      simp only [simulateQ_map, StateT.run_map, simulateQ_spec_query, realImpl_request_run,
        map_bind, Functor.map_map]
      erw [bind_map_left, bind_map_left]
      refine bind_congr fun p => ?_
      convert ih p.1 (tally * Multiplicative.ofAdd (phaseCost (Sum.inr request)))
        (log ++ [⟨request, p.1⟩]) p.2 using 2
      · funext a
        rw [mul_assoc]
      · rfl

/-! ## The verifier, flattened -/

/-- The verifier's state: its tally and the cache. -/
abbrev VerifyState := Multiplicative Tally × QueryCache HashSpec

/-- **The verifier as one handler**: the oracle's step, charged as verification. -/
@[expose] noncomputable def realWorldImpl : QueryImpl OracleWorld (StateT VerifyState ProbComp) :=
  fun world state =>
    (fun z => (z.1, (state.1 * Multiplicative.ofAdd (verifierCost world), z.2))) <$>
      (KeygenUniform.rom world).run state.2

theorem realWorldImpl_run (world : OracleWorld.Domain) (state : VerifyState) :
    (realWorldImpl world).run state =
      (fun z => (z.1, (state.1 * Multiplicative.ofAdd (verifierCost world), z.2))) <$>
        (KeygenUniform.rom world).run state.2 := rfl

/-- **The verifier's two layers are one handler.** -/
theorem run_flatVerify {α : Type} (computation : OracleComp OracleWorld α) :
    ∀ (tally : Multiplicative Tally) (cache : QueryCache HashSpec),
      (fun z => ((z.1.1, tally * z.1.2), z.2)) <$>
          (simulateQ KeygenUniform.rom
            ((simulateQ (addCostOracle verifierCost) computation).run)).run cache =
        (fun z => ((z.1, z.2.1), z.2.2)) <$>
          (simulateQ realWorldImpl computation).run (tally, cache) := by
  induction computation using OracleComp.inductionOn with
  | pure value => intro tally cache; simp
  | query_bind queried next ih =>
    intro tally cache
    rw [run_addCost_query_bind, simulateQ_bind, StateT.run_bind, simulateQ_bind,
      simulateQ_spec_query, StateT.run_bind, simulateQ_spec_query, realWorldImpl_run]
    simp only [simulateQ_map, StateT.run_map, map_bind, Functor.map_map]
    erw [bind_map_left]
    refine bind_congr fun p => ?_
    convert ih p.1 (tally * Multiplicative.ofAdd (verifierCost queried)) p.2 using 2
    funext a
    rw [mul_assoc]

/-! ## The linked run, flattened -/

theorem rom_phase_eq (signer : Message → OracleComp OracleWorld (Option Bytes)) {α : Type}
    (computation : OracleComp (OracleWorld + SigningSpec) α) (cache : QueryCache HashSpec) :
    (simulateQ KeygenUniform.rom ((simulateQ (unchargedPhase signer)
        ((simulateQ (addCostOracle phaseCost) computation).run)).run [])).run cache =
      (fun z => (((z.1, z.2.1), z.2.2.1), z.2.2.2)) <$>
        (simulateQ (realImpl signer) computation).run (1, [], cache) := by
  have h := congrArg (fun x => (fun w => (((w.1.1, w.1.2), w.2.1), w.2.2)) <$> x)
    (run_flat signer computation 1 [] cache)
  simp only [Functor.map_map, one_mul] at h
  rw [← h]
  simp

theorem rom_verify_eq {α : Type} (computation : OracleComp OracleWorld α)
    (cache : QueryCache HashSpec) :
    (simulateQ KeygenUniform.rom (countRecorded verifierCost computation)).run cache =
      (fun z => ((z.1, Multiplicative.toAdd z.2.1), z.2.2)) <$>
        (simulateQ realWorldImpl computation).run (1, cache) := by
  have h := congrArg (fun x => (fun w => ((w.1.1, Multiplicative.toAdd w.1.2), w.2)) <$> x)
    (run_flatVerify computation 1 cache)
  simp only [Functor.map_map, one_mul] at h
  rw [countRecorded, simulateQ_map, StateT.run_map, ← h]

/-- **The real game at a drawn table, flattened**: the adversary's phase under one handler, then
the verifier under another. -/
@[expose] noncomputable def realFlat (adversary : Adversary) (keys : SecretKey × PublicKey)
    (warm : QueryCache HashSpec) :
    ProbComp ((((Forgery × Multiplicative Tally) × (Bool × Tally)) × SigningLog) ×
      QueryCache HashSpec) := do
  let z ← (simulateQ (realImpl (StrippedGame.strippedSign warm keys.1)) (adversary.main keys.2)).run
    (1, [], warm)
  let w ← (simulateQ realWorldImpl (Scheme.verify keys.2 z.1.message z.1.signature)).run
    (1, z.2.2.2)
  pure ((((z.1, z.2.1), (w.1, Multiplicative.toAdd w.2.1)), z.2.2.1), w.2.2)

theorem linkedRun_eq (adversary : Adversary) (prfSeed publicSeed : Digest)
    (table : Cells × Padding) :
    linkedRun adversary prfSeed publicSeed table =
      realFlat adversary (keysOf prfSeed publicSeed table)
        (walkOfTable prfSeed publicSeed table).2 := by
  rw [linkedRun, LinkedGame.linkedAfterSeeds, simulateQ_bind, StateT.run_bind, simulateQ_bind,
    StateT.run_bind, rom_phase_eq, realFlat, bind_map_left]
  refine bind_congr fun z => ?_
  simp only [simulateQ_bind, StateT.run_bind, LinkedGame.run_unchargedPhase_lift,
    simulateQ_pure, StateT.run_pure, bind_map_left, rom_verify_eq]

end SlhDsaSecurity.SharePresent
