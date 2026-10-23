/-
Copyright (c) 2026 Tom Wambsgans. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Wambsgans
-/

module

public import HashSig.SLHDSA.SHAKE128s.Proof.SplitCounted
public import HashSig.SLHDSA.SHAKE128s.Proof.CarrierTail
public import HashSig.SLHDSA.SHAKE128s.Proof.AnswerCarrier
public import HashSig.SLHDSA.SHAKE128s.Proof.SplitTail

/-!
# The carrier's tail, with the counter split in two

`CarrierTail.carrierTail` keeps one counter in its handler's state. The answer half's two
charges need two: the structural clause is paid by the queries *outside* the target class and
the coverage clause by those inside, and the two must be read off **one** run. This file is the
same three-stage tail with `SplitCounted.withSplit` as the handler's counter, and the projection
that reads `SplitTail.splitCarrierTail` as a run of the shared oracle with
`Security.countQueries (ClassGrowth.splitCost …)` wrapped around the computation.

Every statement is `CarrierTail`'s with `Nat` replaced by `Counts` and `hashCost` by `splitCost`,
and every proof is the same proof: the counter is an extra component of the handler's state,
`CountedHandler.withExtra` carries it, and the brackets write the framing and nothing else.
`SplitCounted.run_withSplit_withCount` relates this tail to the counted one, so they are the
same run read two ways. The last theorem, `forget_splitCarrierTail`, is the file's output.
-/

@[expose] public section

open OracleComp OracleSpec

namespace SlhDsaSecurity.SplitCarrierTail

variable {α β : Type}

open Security RecorderView CarriedWitness PhaseFusion RecordedQueries BracketedRun
open CarrierTail ClassGrowth SplitCounted

/-! ## The shared oracle, counting into two slots

`CountedHandler.romWithCount` is the shared oracle with a counter beside its cache; this is the
same with a pair of slots. It is a separate definition because the carrier's state associates
the other way, and merging the two would cost a reassociation at every call site. -/

/-- The shared oracle with a two-slot hash counter beside its cache. -/
noncomputable def romWithSplit (inClass : Bytes → Prop) (inside outside : QueryKind) :
    QueryImpl OracleWorld (StateT (QueryCache HashSpec × Counts) ProbComp) :=
  fun queried state => do
    let step ← (KeygenUniform.rom queried).run state.1
    pure (step.1, (step.2, state.2 + splitCost inClass inside outside queried))

theorem romWithSplit_run (inClass : Bytes → Prop) (inside outside : QueryKind)
    (queried : OracleWorld.Domain) (state : QueryCache HashSpec × Counts) :
    (romWithSplit inClass inside outside queried).run state =
      (KeygenUniform.rom queried).run state.1 >>= fun step =>
        (pure (step.1, (step.2, state.2 + splitCost inClass inside outside queried)) :
          ProbComp (OracleWorld.Range queried × (QueryCache HashSpec × Counts))) := rfl

/-- **Its slots are `countQueries (splitCost …)`'s count.** `CountedHandler.run_romWithCount_count`
with the pair in place of the number; the counter the run started at is carried so that the
tail's three stages add up. -/
theorem run_romWithSplit_count (inClass : Bytes → Prop) (inside outside : QueryKind)
    {α : Type} (computation : OracleComp OracleWorld α) :
    ∀ state : QueryCache HashSpec × Counts,
      (fun z : α × (QueryCache HashSpec × Counts) => ((z.1, z.2.2), z.2.1)) <$>
          (simulateQ (romWithSplit inClass inside outside) computation).run state =
        (fun r : (α × Counts) × QueryCache HashSpec => ((r.1.1, state.2 + r.1.2), r.2)) <$>
          (simulateQ KeygenUniform.rom
            (countQueries (splitCost inClass inside outside) computation)).run state.1 := by
  induction computation using OracleComp.inductionOn with
  | pure value =>
    intro state
    rw [simulateQ_pure, StateT.run_pure, map_pure, VerificationBudget.countQueries_pure,
      simulateQ_pure, StateT.run_pure, map_pure, add_zero]
  | query_bind queried next ih =>
    intro state
    rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, map_bind, romWithSplit_run,
      bind_assoc, WarmedSplit.countQueries_query_bind, simulateQ_bind, simulateQ_spec_query,
      StateT.run_bind, map_bind]
    refine bind_congr fun inner => ?_
    rw [pure_bind, ih inner.1 (inner.2, state.2 + splitCost inClass inside outside queried),
      simulateQ_map, StateT.run_map, Functor.map_map]
    refine congrArg (fun f => f <$> (simulateQ KeygenUniform.rom
      (countQueries (splitCost inClass inside outside) (next inner.1))).run inner.2)
      (funext fun result => ?_)
    change ((result.1.1, state.2 + splitCost inClass inside outside queried + result.1.2),
        result.2) =
      ((result.1.1, state.2 + (splitCost inClass inside outside queried + result.1.2)),
        result.2)
    rw [add_assoc]

/-! ## The tail is `SplitTail.splitCarrierTail`

Everything below is stated at `SplitTail.splitCarrierTail`: the shared oracle with two slots,
and the laws the *handler* satisfies. -/

/-- The handler's state, with two slots where the tail's has one. -/
abbrev SplitCountedState : Type :=
  HandlerCarrier.State × ((DigestTape.Record × DigestTape.Record) × Counts)

/-! ## The stages project, exactly as they do at one counter -/

theorem splitHandlerAt_step_forget (inClass : Bytes → Prop) (inside outside : QueryKind)
    (rightKeep : Walk → Bytes → HandlerCarrier.State → Prop) (walk : Walk)
    (queried : OracleWorld.Domain) (state : SplitCountedState) :
    (fun z : OracleWorld.Range queried × SplitCountedState => (z.1, (z.2.1.cache, z.2.2.2))) <$>
        ((SplitTail.splitHandlerAt inClass inside outside rightKeep walk) queried).run state =
      (romWithSplit inClass inside outside queried).run (state.1.cache, state.2.2) := by
  rw [SplitTail.splitHandlerAt, SplitCounted.splitCarrierRecorder, SplitCounted.withSplit_run,
    romWithSplit_run, map_eq_bind_pure_comp, bind_assoc]
  change _ = (KeygenUniform.rom queried).run
      (CacheView.cacheOf (σ := HandlerCarrier.State) (state.1, state.2.1).1) >>= _
  rw [← CarrierFiles.noticingRecorderOf_forget_step (keyAt walk) (rightKeep walk) queried
      (state.1, state.2.1), map_eq_bind_pure_comp, bind_assoc]
  refine bind_congr fun step => ?_
  simp only [Function.comp_def, pure_bind]
  rfl

theorem forgetsAlong_romWithSplit (inClass : Bytes → Prop) (inside outside : QueryKind)
    (rightKeep : Walk → Bytes → HandlerCarrier.State → Prop) (walk : Walk) :
    ServingForget.ForgetsAlong (fun state : SplitCountedState => (state.1.cache, state.2.2))
      (SplitTail.splitHandlerAt inClass inside outside rightKeep walk)
      (romWithSplit inClass inside outside) := by
  intro β computation
  induction computation using OracleComp.inductionOn with
  | pure value =>
    intro state
    rw [simulateQ_pure, StateT.run_pure, simulateQ_pure, StateT.run_pure, map_pure]
  | query_bind queried next ih =>
    intro state
    rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, map_bind, simulateQ_bind,
      simulateQ_spec_query, StateT.run_bind,
      ← splitHandlerAt_step_forget inClass inside outside rightKeep walk queried state,
      bind_map_left]
    exact bind_congr fun step => ih step.1 step.2

/-- **The brackets keep the cache and both slots.** -/
theorem startServingOn_cacheSplit (request : Message) (state : SplitCountedState) :
    ((ServedAgreement.startServingOn request state).1.cache,
        (ServedAgreement.startServingOn request state).2.2) =
      (state.1.cache, state.2.2) := by
  rw [ServedAgreement.startServingOn]
  cases request.frame with
  | none => rfl
  | some framed => rfl

theorem stopServingOn_cacheSplit (state : SplitCountedState) :
    ((ServedAgreement.stopServingOn state).1.cache,
      (ServedAgreement.stopServingOn (τ := (DigestTape.Record × DigestTape.Record) × Counts)
        state).2.2) = (state.1.cache, state.2.2) := rfl

theorem rom_middle_forget {α : Type} (inClass : Bytes → Prop) (inside outside : QueryKind)
    (rightKeep : Walk → Bytes → HandlerCarrier.State → Prop) (walk : Walk)
    (inner : QueryImpl (OracleWorld + SigningSpec)
      (WriterT (Multiplicative Tally) (StateT SigningLog (OracleComp OracleWorld))))
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (accumulated : Multiplicative Tally) (log : SigningLog) (state : SplitCountedState) :
    (fun step : α × (Multiplicative Tally × SigningLog × SplitCountedState) =>
        (step.1, (step.2.1, step.2.2.1, (step.2.2.2.1.cache, step.2.2.2.2.2)))) <$>
      (simulateQ (fuseServing (SplitTail.splitHandlerAt inClass inside outside rightKeep walk) inner
        ServedAgreement.startServingOn ServedAgreement.stopServingOn) computation).run
        (accumulated, log, state) =
      (simulateQ (fuse (romWithSplit inClass inside outside) inner) computation).run
        (accumulated, log, (state.1.cache, state.2.2)) :=
  ServingForget.run_fuseServing_map (fun s : SplitCountedState => (s.1.cache, s.2.2))
    (SplitTail.splitHandlerAt inClass inside outside rightKeep walk)
    (romWithSplit inClass inside outside)
    inner ServedAgreement.startServingOn ServedAgreement.stopServingOn
    startServingOn_cacheSplit stopServingOn_cacheSplit
    (forgetsAlong_romWithSplit inClass inside outside rightKeep walk) computation accumulated log
    state

/-! ## The three stages as binds -/

theorem rom_first_stage_forget (inClass : Bytes → Prop) (inside outside : QueryKind)
    (rightKeep : Walk → Bytes → HandlerCarrier.State → Prop) (walk : Walk)
    {α : Type} (computation : OracleComp OracleWorld α) :
    (fun z : α × SplitCountedState => (z.1, (z.2.1.cache, z.2.2.2))) <$>
        (simulateQ (SplitTail.splitHandlerAt inClass inside outside rightKeep walk) computation).run
          (startAt walk.2, (([], []), 0)) =
      (simulateQ (romWithSplit inClass inside outside) computation).run (walk.2, 0) :=
  forgetsAlong_romWithSplit inClass inside outside rightKeep walk computation
    (startAt walk.2, (([], []), 0))

theorem rom_first_stage_bind (inClass : Bytes → Prop) (inside outside : QueryKind)
    (rightKeep : Walk → Bytes → HandlerCarrier.State → Prop) (walk : Walk)
    {α : Type} (computation : OracleComp OracleWorld α) :
    (simulateQ (romWithSplit inClass inside outside) computation).run (walk.2, 0) =
      (simulateQ (SplitTail.splitHandlerAt inClass inside outside rightKeep walk) computation).run
          (startAt walk.2, (([], []), 0)) >>= fun z =>
        (pure (z.1, (z.2.1.cache, z.2.2.2)) :
          ProbComp (α × (QueryCache HashSpec × Counts))) := by
  rw [← rom_first_stage_forget inClass inside outside rightKeep walk computation,
    map_eq_bind_pure_comp]
  rfl

theorem rom_middle_stage_bind (inClass : Bytes → Prop) (inside outside : QueryKind)
    (rightKeep : Walk → Bytes → HandlerCarrier.State → Prop) (walk : Walk)
    (adversary : Adversary) (keys : (SecretKey × PublicKey) × SplitCountedState) :
    (simulateQ (romWithSplit inClass inside outside)
        (((simulateQ (recordedAdversaryImpl + recordedSigningOracle (Scheme.sign keys.1.1))
          (adversary.main keys.1.2)).run).run [])).run (keys.2.1.cache, keys.2.2.2) =
      (simulateQ (fuseServing (SplitTail.splitHandlerAt inClass inside outside rightKeep walk)
          (recordedAdversaryImpl + recordedSigningOracle (Scheme.sign keys.1.1))
          ServedAgreement.startServingOn ServedAgreement.stopServingOn)
          (adversary.main keys.1.2)).run (1, [], keys.2) >>= fun step =>
        (pure (((step.1, step.2.1), step.2.2.1), (step.2.2.2.1.cache, step.2.2.2.2.2)) :
          ProbComp (((Forgery × Multiplicative Tally) × SigningLog) ×
            (QueryCache HashSpec × Counts))) := by
  rw [PhaseFusion.run_phase_fused (romWithSplit inClass inside outside)
      (recordedAdversaryImpl + recordedSigningOracle (Scheme.sign keys.1.1))
      (adversary.main keys.1.2) [] (keys.2.1.cache, keys.2.2.2),
    ← rom_middle_forget inClass inside outside rightKeep walk
      (recordedAdversaryImpl + recordedSigningOracle (Scheme.sign keys.1.1))
      (adversary.main keys.1.2) 1 [] keys.2, Functor.map_map, map_eq_bind_pure_comp]
  rfl

theorem rom_last_stage_bind (inClass : Bytes → Prop) (inside outside : QueryKind)
    (rightKeep : Walk → Bytes → HandlerCarrier.State → Prop) (walk : Walk)
    (pk : PublicKey) (forgery : Forgery) (state : SplitCountedState) :
    (simulateQ (romWithSplit inClass inside outside) (countRecorded verifierCost
        (Scheme.verify pk forgery.message forgery.signature))).run
        (state.1.cache, state.2.2) =
      (simulateQ (SplitTail.splitHandlerAt inClass inside outside rightKeep walk)
          (countRecorded verifierCost
            (Scheme.verify pk forgery.message forgery.signature))).run state >>= fun z =>
        (pure (z.1, (z.2.1.cache, z.2.2.2)) :
          ProbComp ((Bool × Tally) × (QueryCache HashSpec × Counts))) := by
  rw [← forgetsAlong_romWithSplit inClass inside outside rightKeep walk
      (countRecorded verifierCost (Scheme.verify pk forgery.message forgery.signature)) state,
    map_eq_bind_pure_comp]
  rfl

/-! ## The assembly

`SplitTail.splitCarrierTail` is three stages over the same computation as a run of the shared
oracle with the two slots, so the composition is a composition. `run_romWithSplit_recorded` puts
the oracle's side at the split handler (the slots move from `countQueries`, wrapped around the
computation, into the handler's own state), and after that the two sides differ only in the
handler. -/

attribute [local irreducible] RecordedTail.recordedAfterSeeds Scheme.keygenInternal
  Scheme.verify Scheme.sign Security.countQueries

/-- **The split-counted shared oracle's slots are `countQueries (splitCost …)`'s**, at the run
the tail is compared against. `CarrierTail.recordedTail_eq_counted` at the pair: the run starts
at an empty counter, so the counter it started from adds nothing. -/
theorem run_romWithSplit_recorded (inClass : Bytes → Prop) (inside outside : QueryKind)
    (adversary : Adversary) (walk : Walk) :
    (fun z : (Outcome × Multiset Bytes) × (QueryCache HashSpec × Counts) =>
        ((z.1, z.2.2), z.2.1)) <$>
        (simulateQ (romWithSplit inClass inside outside)
          (RecordedTail.recordedAfterSeeds adversary walk.1.1)).run (walk.2, 0) =
      (simulateQ KeygenUniform.rom (countQueries (splitCost inClass inside outside)
        (RecordedTail.recordedAfterSeeds adversary walk.1.1))).run walk.2 := by
  rw [run_romWithSplit_count inClass inside outside
      (RecordedTail.recordedAfterSeeds adversary walk.1.1) (walk.2, 0),
    show (fun r : ((Outcome × Multiset Bytes) × Counts) × QueryCache HashSpec =>
        ((r.1.1, (0 : Counts) + r.1.2), r.2)) = id from funext fun r => by rw [zero_add]; rfl,
    id_map]

/-- **The split tail is a split-counted run of the shared oracle**, once its recordings are
dropped and its slots are read out of the state. `CarrierTail.forget_carrierTail` at the pair,
matched stage for stage by the three bind laws above. -/
theorem forget_splitCarrierTail (inClass : Bytes → Prop) (inside outside : QueryKind)
    (rightKeep : Walk → Bytes → HandlerCarrier.State → Prop) (adversary : Adversary)
    (walk : Walk) :
    (fun z : (((Outcome × Multiset Bytes) × Nat) × SplitPrefix.SplitState) × Counts =>
        ((z.1.1.1, z.2), z.1.2.1)) <$>
        SplitTail.splitCarrierTail inClass inside outside rightKeep adversary walk =
      (simulateQ KeygenUniform.rom (countQueries (splitCost inClass inside outside)
        (RecordedTail.recordedAfterSeeds adversary walk.1.1))).run walk.2 := by
  rw [← run_romWithSplit_recorded inClass inside outside adversary walk,
    run_recordedAfterSeeds_split (romWithSplit inClass inside outside) adversary walk.1.1
      (walk.2, 0),
    rom_first_stage_bind inClass inside outside rightKeep walk
      (Scheme.keygenInternal walk.1.1.1 walk.1.1.2.1 walk.1.1.2.2),
    SplitTail.splitCarrierTail]
  simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_def]
  refine bind_congr fun keys => ?_
  rw [rom_middle_stage_bind inClass inside outside rightKeep walk adversary keys]
  simp only [bind_assoc, pure_bind]
  refine bind_congr fun middle => ?_
  rw [rom_last_stage_bind inClass inside outside rightKeep walk keys.1.2 middle.1
    middle.2.2.2]
  simp only [bind_assoc, pure_bind]
  refine bind_congr fun final => ?_
  rfl

end SlhDsaSecurity.SplitCarrierTail
