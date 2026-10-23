/-
Copyright (c) 2026 Tom Wambsgans. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Wambsgans
-/

module

public import HashSig.SLHDSA.SHAKE128s.Proof.AdversaryQueries

/-!
# Recording the adversary's and the verifier's own queries

The input half's event is that the adversary queries the canonical input of a sensitive node.
In the stripped game such a query leaves no trace in the cache — the walk installed every
canonical entry, so a hit changes nothing — so the event has to be observed by instrumentation.
This file adds that instrumentation at exactly the two places `Outcome.counts` charges a hash,
the adversary's own handler and the verifier's, and bounds what it records.

The honest phase is **not** recorded. It is stripped precisely so that its queries cannot be
sensitive, and recording it would put them back; and its remaining queries are bounded by the
number of signing requests rather than by the work budget, so recording them would also break
the cardinality bound.

Two design choices are worth stating, because the obvious alternatives look better than they
are.

* **The writer, not a global recording oracle.** Recording in the same writer as the counters
  makes `Multiset.card recorded = counts.work` true by construction at every query, so the
  cardinality bound is one induction with an equality invariant. A global oracle that recorded
  only at inputs the warm table answers would make the honest phase invisible for free — it
  never asks at one — but bounding what such an oracle records needs the *stripped* game's own
  total hash count, which couples the stripped and the real game. The writer design avoids it
  because `Outcome.counts` is what the stripping surgery leaves untouched: it counts the adversary's
  own calls, the verifier's, and signing *requests*, never the signer's hashing.

* **`Multiset`, not `Finset`.** `Multiset Bytes` is an `AddCommMonoid`, which is what a writer
  needs. The `Add` instance `Finset` carries is pointwise addition of its elements, which would
  typecheck and be silently wrong. The set is recovered at the end by `Multiset.toFinset`, whose
  cardinality is at most the multiset's.

Invisibility is the general fact that a simulation accumulating in one monoid is carried to one
accumulating in another by any homomorphism between them — `run_simulateQ_map_writer`, stated
for an arbitrary writer and handler, with the game-level statement an instance of it. It holds
one handler at two writers and concludes an equality of computations.
-/

@[expose] public section

open OracleComp OracleSpec

namespace SlhDsaSecurity.RecordedQueries

variable {α β : Type}

open Security

/-! ## Mapping a writer along a monoid homomorphism

A simulation whose handler accumulates in one monoid is carried to a simulation accumulating in
another by any monoid homomorphism between them: whatever the richer writer records, the poorer
one records its image, step for step. This is how an instrumentation is made invisible — the
instrumented run, read through the projection that forgets the instrumentation, *is* the
uninstrumented run, as an equality of computations.

The homomorphism is taken as a bare function with its two laws, rather than as a bundled
`MonoidHom`, so that it can be instantiated at a `Multiplicative` projection without instance
hunting. -/

theorem run_simulateQ_map_writer {ι : Type} {spec : OracleSpec ι} {M : Type → Type} [Monad M]
    [LawfulMonad M] {ω₁ ω₂ : Type} [Monoid ω₁] [Monoid ω₂] (φ : ω₁ → ω₂)
    (hone : φ 1 = 1) (hmul : ∀ left right : ω₁, φ (left * right) = φ left * φ right)
    (rich : QueryImpl spec (WriterT ω₁ M)) (poor : QueryImpl spec (WriterT ω₂ M))
    (himpl : ∀ t : spec.Domain,
      (poor t).run = (fun step => (step.1, φ step.2)) <$> (rich t).run)
    {α : Type} (computation : OracleComp spec α) :
    (simulateQ poor computation).run =
      (fun step => (step.1, φ step.2)) <$> (simulateQ rich computation).run := by
  induction computation using OracleComp.inductionOn with
  | pure value => simp [WriterT.run_pure, hone]
  | query_bind queried next ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, WriterT.run_bind, himpl, ih, map_bind,
      bind_map_left, Functor.map_map, hmul]

/-- A cost-recording handler, as the run it performs. -/
theorem run_withAddCost {ι : Type} {spec : OracleSpec ι} {M : Type → Type} [Monad M]
    [LawfulMonad M] {ω : Type} [AddMonoid ω] (impl : QueryImpl spec M)
    (cost : spec.Domain → ω) (t : spec.Domain) :
    ((impl.withAddCost cost) t).run =
      (fun value => (value, Multiplicative.ofAdd (cost t))) <$> impl t := by
  simp only [QueryImpl.withAddCost_apply, WriterT.run_bind, AddWriterT.run_addTell, pure_bind,
    WriterT.run_monadLift, Functor.map_map, mul_one]

/-- **Two cost functions related by a homomorphism give related handlers.** -/
theorem run_withAddCost_map {ι : Type} {spec : OracleSpec ι} {M : Type → Type} [Monad M]
    [LawfulMonad M] {ω₁ ω₂ : Type} [AddMonoid ω₁] [AddMonoid ω₂]
    (φ : Multiplicative ω₁ → Multiplicative ω₂) (impl : QueryImpl spec M)
    (rich : spec.Domain → ω₁) (poor : spec.Domain → ω₂)
    (hcost : ∀ t, Multiplicative.ofAdd (poor t) = φ (Multiplicative.ofAdd (rich t)))
    (t : spec.Domain) :
    ((impl.withAddCost poor) t).run =
      (fun step => (step.1, φ step.2)) <$> ((impl.withAddCost rich) t).run := by
  rw [run_withAddCost, run_withAddCost, Functor.map_map]
  exact congrArg (· <$> impl t) (funext fun value => by simp [hcost])

/-! ## The tally: counters together with a record

`Multiset`, not `Finset`: `Multiset Bytes` is an `AddCommMonoid`, which is what a writer needs,
while the `Add` instance `Finset` carries is pointwise addition of its elements and would be
silently wrong here. The set is recovered at the end by `Multiset.toFinset`, whose cardinality
is at most the multiset's. -/

/-- The counters, together with a record of the inputs charged. -/
abbrev Tally := Counts × Multiset Bytes

/-- What a query records: its own input if it is a hash call, nothing for a coin. -/
def recordOf : OracleWorld.Domain → Multiset Bytes
  | .inl _ => 0
  | .inr input => {input}

theorem card_recordOf (queried : OracleWorld.Domain) :
    Multiset.card (recordOf queried) = hashCost queried := by
  rcases queried with _ | _ <;> rfl

/-- The projection that forgets the record. -/
def forget : Multiplicative Tally → Multiplicative Counts :=
  fun tally => Multiplicative.ofAdd (Multiplicative.toAdd tally).1

theorem forget_one : forget 1 = 1 := rfl

theorem forget_mul (left right : Multiplicative Tally) :
    forget (left * right) = forget left * forget right := rfl

/-- The adversary's phase, recording as well as counting. -/
abbrev RecordedRun := AddWriterT Tally (StateT SigningLog (OracleComp OracleWorld))

/-- The adversary's own oracle, recording the input of every hash call it forwards. -/
noncomputable def recordedAdversaryImpl : QueryImpl OracleWorld RecordedRun :=
  (QueryImpl.ofLift OracleWorld (StateT SigningLog (OracleComp OracleWorld))).withAddCost
    (fun input => (Counts.single .hash (hashCost input), recordOf input))

/-- Forgetting the record turns the recording handler back into the counting one. -/
theorem run_adversaryImpl_map (queried : OracleWorld.Domain) :
    (AdversaryQueries.adversaryImpl queried).run =
      (fun step => (step.1, forget step.2)) <$> (recordedAdversaryImpl queried).run :=
  run_withAddCost_map forget
    (QueryImpl.ofLift OracleWorld (StateT SigningLog (OracleComp OracleWorld)))
    (fun input => (Counts.single .hash (hashCost input), recordOf input))
    (fun input => Counts.single .hash (hashCost input)) (fun _ => rfl) queried

/-! ### The signing oracle at the recording writer -/

theorem stateT_map_apply {α β : Type} (f : α → β)
    (x : StateT SigningLog (OracleComp OracleWorld) α) (log : SigningLog) :
    (f <$> x) log = (fun step => (f step.1, step.2)) <$> x log :=
  StateT.run_map f x log

theorem run_liftM_base {ω : Type} [Monoid ω] {α : Type} (x : OracleComp OracleWorld α)
    (log : SigningLog) :
    ((WriterT.run (liftM x : WriterT ω (StateT SigningLog (OracleComp OracleWorld)) α)).run
      log) = (fun value => ((value, (1 : ω)), log)) <$> x := by
  simp [liftM, monadLift, MonadLift.monadLift]

theorem run_liftM_inner {ω : Type} [Monoid ω] {α : Type}
    (x : StateT SigningLog (OracleComp OracleWorld) α) (log : SigningLog) :
    ((WriterT.run (liftM x : WriterT ω (StateT SigningLog (OracleComp OracleWorld)) α)).run
      log) = (fun step => ((step.1, (1 : ω)), step.2)) <$> x.run log := by
  simp [liftM, monadLift, MonadLift.monadLift]

/-- The signing oracle, recording nothing: the signer is honest, so its calls are not charged
and must not be recorded. -/
noncomputable def recordedSigningOracle
    (signer : Message → OracleComp OracleWorld (Option Bytes)) :
    QueryImpl SigningSpec RecordedRun := fun request => do
  AddWriterT.addTell ((Counts.single .signing 1, (0 : Multiset Bytes)))
  let answer ← liftM (signer request)
  liftM (modify (fun signed => signed ++ [⟨request, answer⟩]) :
    StateT SigningLog (OracleComp OracleWorld) Unit)
  return answer

theorem run_recordedSigningOracle
    (signer : Message → OracleComp OracleWorld (Option Bytes)) (request : Message)
    (log : SigningLog) :
    ((recordedSigningOracle signer request).run).run log =
      signer request >>= fun answer =>
        (pure ((answer, Multiplicative.ofAdd
            ((Counts.single .signing 1 : Counts), (0 : Multiset Bytes))),
          log ++ [⟨request, answer⟩]) :
          OracleComp OracleWorld ((Option Bytes × Multiplicative Tally) × SigningLog)) := by
  simp only [recordedSigningOracle, WriterT.run_bind, WriterT.run_pure, AddWriterT.run_addTell,
    StateT.run_bind, StateT.run_pure, run_liftM_base, run_liftM_inner, StateT.run_modify,
    map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_def, mul_one]

/-- Forgetting the record turns the recording signing oracle back into the counting one. -/
theorem run_signingOracle_map
    (signer : Message → OracleComp OracleWorld (Option Bytes)) (request : Message) :
    (StrippedGame.signingOracleWith signer request).run =
      (fun step => (step.1, forget step.2)) <$> (recordedSigningOracle signer request).run := by
  funext log
  change ((StrippedGame.signingOracleWith signer request).run).run log =
    ((fun step => (step.1, forget step.2)) <$> (recordedSigningOracle signer request).run).run log
  rw [StateT.run_map, StrippedGame.run_signingOracleWith, run_recordedSigningOracle]
  simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_def]
  rfl

/-! ### The verifier's instrumentation at the recording writer -/

/-- The verifier's instrumentation, recording as well as counting. -/
noncomputable def countRecorded {α : Type} (cost : OracleWorld.Domain → Tally)
    (computation : OracleComp OracleWorld α) : OracleComp OracleWorld (α × Tally) :=
  (fun result => (result.1, Multiplicative.toAdd result.2)) <$>
    (simulateQ (addCostOracle cost) computation).run

/-- Forgetting the record turns the recording instrumentation back into the counting one. -/
theorem countQueries_eq_map_countRecorded {α : Type} (cost : OracleWorld.Domain → Tally)
    (computation : OracleComp OracleWorld α) :
    countQueries (fun input => (cost input).1) computation =
      (fun result => (result.1, result.2.1)) <$> countRecorded cost computation := by
  rw [countQueries, countRecorded, Functor.map_map,
    run_simulateQ_map_writer forget forget_one forget_mul (addCostOracle cost)
      (addCostOracle fun input => (cost input).1)
      (fun t => run_withAddCost_map forget
        (QueryImpl.ofLift OracleWorld (OracleComp OracleWorld)) cost
        (fun input => (cost input).1) (fun _ => rfl) t) computation,
    Functor.map_map]
  rfl

/-- The verifier's cost: charge the call and record its input. -/
noncomputable def verifierCost : OracleWorld.Domain → Tally :=
  fun input => (Counts.single .verification (hashCost input), recordOf input)

/-- The verifier's own instrumentation, at the spelling the game uses. -/
theorem countQueries_verification_eq {α : Type} (computation : OracleComp OracleWorld α) :
    countQueries (fun input => Counts.single .verification (hashCost input)) computation =
      (fun result => (result.1, result.2.1)) <$> countRecorded verifierCost computation :=
  countQueries_eq_map_countRecorded verifierCost computation

/-! ## The instrumented game

The recording sits at exactly the two places `Outcome.counts` charges a hash: the adversary's
own handler and the verifier's instrumentation. The honest phase is not recorded — it is
stripped precisely so that its queries cannot be sensitive, and recording it would put them
back. -/

/-- The stripped game, recording the adversary's and the verifier's own hash inputs. -/
noncomputable def recordedAfterSeeds (adversary : Adversary) (sds : Digest × Digest × Digest)
    (warm : QueryCache HashSpec) : OracleComp OracleWorld (Outcome × Multiset Bytes) := do
  let (sk, pk) ← StrippedGame.strippedKeygen warm sds
  let ((forgery, adversaryTally), signed) ←
    (simulateQ (recordedAdversaryImpl +
      recordedSigningOracle (StrippedGame.strippedSign warm sk)) (adversary.main pk)).run.run []
  let (verified, verifierTally) ← countRecorded verifierCost
    (Scheme.verify pk forgery.message forgery.signature)
  return ({
    forgery := forgery
    signed := signed
    verified := verified
    counts := (Multiplicative.toAdd adversaryTally).1 + verifierTally.1 },
    (Multiplicative.toAdd adversaryTally).2 + verifierTally.2)

set_option linter.constructorNameAsVariable false in
set_option maxHeartbeats 1000000 in
/-- **The recording is invisible.** Forgetting it returns the stripped game exactly. -/
theorem map_recordedAfterSeeds (adversary : Adversary) (sds : Digest × Digest × Digest)
    (warm : QueryCache HashSpec) :
    Prod.fst <$> recordedAfterSeeds adversary sds warm =
      StrippedGame.strippedAfterSeeds adversary sds warm := by
  unfold recordedAfterSeeds StrippedGame.strippedAfterSeeds
  rw [map_bind]
  refine congrArg (Bind.bind _) (funext fun keys => ?_)
  obtain ⟨sk, pk⟩ := keys
  dsimp only
  rw [map_bind,
    show ((simulateQ
        (((QueryImpl.ofLift OracleWorld (StateT SigningLog (OracleComp OracleWorld))).withAddCost
            fun input => Counts.single QueryKind.hash (hashCost input)) +
          StrippedGame.strippedSigningOracle warm sk) (adversary.main pk)).run).run [] =
      (fun step => ((step.1.1, forget step.1.2), step.2)) <$>
        ((simulateQ (recordedAdversaryImpl +
          recordedSigningOracle (StrippedGame.strippedSign warm sk))
          (adversary.main pk)).run).run [] from by
      rw [run_simulateQ_map_writer forget forget_one forget_mul
        (recordedAdversaryImpl + recordedSigningOracle (StrippedGame.strippedSign warm sk))
        (((QueryImpl.ofLift OracleWorld (StateT SigningLog (OracleComp OracleWorld))).withAddCost
            fun input => Counts.single QueryKind.hash (hashCost input)) +
          StrippedGame.strippedSigningOracle warm sk)
        (fun t => by
          rcases t with world | request
          · exact run_adversaryImpl_map world
          · exact run_signingOracle_map _ request) (adversary.main pk)]
      exact stateT_map_apply _ _ [],
    bind_map_left]
  refine congrArg (Bind.bind _) (funext fun advStep => ?_)
  obtain ⟨⟨forgery, adversaryTally⟩, signed⟩ := advStep
  dsimp only
  rw [map_bind, countQueries_verification_eq, bind_map_left]
  refine congrArg (Bind.bind _) (funext fun verifyStep => ?_)
  obtain ⟨verified, verifierTally⟩ := verifyStep
  rfl

/-! ## The record is exactly as big as the charge

Because the record and the counters accumulate in the same writer, at the same queries, with
the same per-query size, the cardinality of the record equals the charged work step for step.
That is the whole advantage of recording in the writer rather than at the oracle. -/

/-- A cost whose record has exactly the cardinality its counters charge. -/
def Faithful (cost : OracleWorld.Domain → Tally) : Prop :=
  ∀ queried, Multiset.card (cost queried).2 = ((cost queried).1).work

theorem faithful_adversaryCost :
    Faithful (fun input => (Counts.single .hash (hashCost input), recordOf input)) := fun queried => by
  rw [AdversaryQueries.work_single_hash]
  exact card_recordOf queried

theorem faithful_verifierCost : Faithful verifierCost := fun queried => by
  rw [verifierCost, AdversaryQueries.work_single_verification]
  exact card_recordOf queried

theorem run_writer_bind {ω : Type} [Monoid ω] {α β : Type}
    (x : WriterT ω (StateT SigningLog (OracleComp OracleWorld)) α)
    (next : α → WriterT ω (StateT SigningLog (OracleComp OracleWorld)) β) (log : SigningLog) :
    (WriterT.run (x >>= next)).run log =
      (WriterT.run x).run log >>= fun outer =>
        (fun inner => ((inner.1.1, outer.1.2 * inner.1.2), inner.2)) <$>
          (WriterT.run (next outer.1.1)).run outer.2 := by
  simp only [WriterT.run_bind, StateT.run_bind, StateT.run_map]

theorem run_recordedAdversaryImpl (queried : OracleWorld.Domain) (log : SigningLog) :
    ((WriterT.run (recordedAdversaryImpl queried)).run log) =
      (fun value => ((value, Multiplicative.ofAdd
          ((Counts.single .hash (hashCost queried) : Counts), recordOf queried)), log)) <$>
        (liftM (OracleWorld.query queried) :
          OracleComp OracleWorld (OracleWorld.Range queried)) := by
  simp only [recordedAdversaryImpl, QueryImpl.withAddCost_apply, QueryImpl.ofLift_apply,
    WriterT.run_bind, AddWriterT.run_addTell, StateT.run_bind, StateT.run_pure, pure_bind,
    run_liftM_inner, StateT.run_monadLift, map_eq_bind_pure_comp, bind_assoc, pure_bind,
    Function.comp_def, mul_one]

/-- One of the adversary's own queries records exactly what it charges. -/
theorem card_eq_work_adversaryImpl (queried : OracleWorld.Domain) (log : SigningLog)
    (cache : QueryCache HashSpec)
    (outer : ((OracleWorld.Range queried × Multiplicative Tally) × SigningLog) ×
      QueryCache HashSpec)
    (houter : outer ∈ support ((simulateQ KeygenUniform.rom
      ((WriterT.run (recordedAdversaryImpl queried)).run log)).run cache)) :
    Multiset.card (Multiplicative.toAdd outer.1.1.2).2 =
      ((Multiplicative.toAdd outer.1.1.2).1).work := by
  rw [run_recordedAdversaryImpl, simulateQ_map, StateT.run_map, support_map] at houter
  obtain ⟨step, -, hstep⟩ := houter
  rw [show outer.1.1.2 = Multiplicative.ofAdd
      ((Counts.single .hash (hashCost queried) : Counts), recordOf queried) from by rw [← hstep]]
  exact faithful_adversaryCost queried

/-- A signing request records nothing and charges nothing to the work budget. -/
theorem card_eq_work_signingOracle (signer : Message → OracleComp OracleWorld (Option Bytes))
    (request : Message) (log : SigningLog) (cache : QueryCache HashSpec)
    (outer : ((Option Bytes × Multiplicative Tally) × SigningLog) × QueryCache HashSpec)
    (houter : outer ∈ support ((simulateQ KeygenUniform.rom
      ((WriterT.run (recordedSigningOracle signer request)).run log)).run cache)) :
    Multiset.card (Multiplicative.toAdd outer.1.1.2).2 =
      ((Multiplicative.toAdd outer.1.1.2).1).work := by
  rw [run_recordedSigningOracle, simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at houter
  obtain ⟨step, -, hstep⟩ := houter
  rw [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hstep
  rw [show outer.1.1.2 = Multiplicative.ofAdd
      ((Counts.single .signing 1 : Counts), (0 : Multiset Bytes)) from by rw [hstep]]
  rfl

set_option maxHeartbeats 1000000 in
/-- **The adversary's phase records exactly what it charges.** -/
theorem card_eq_work_adversary (signer : Message → OracleComp OracleWorld (Option Bytes))
    {α : Type} (computation : OracleComp (OracleWorld + SigningSpec) α) :
    ∀ (log : SigningLog) (cache : QueryCache HashSpec)
      (result : ((α × Multiplicative Tally) × SigningLog) × QueryCache HashSpec),
      result ∈ support ((simulateQ KeygenUniform.rom
        ((WriterT.run (simulateQ (recordedAdversaryImpl + recordedSigningOracle signer)
          computation)).run log)).run cache) →
        Multiset.card (Multiplicative.toAdd result.1.1.2).2 =
          ((Multiplicative.toAdd result.1.1.2).1).work := by
  induction computation using OracleComp.inductionOn with
  | pure value =>
    intro log cache result hmem
    rw [simulateQ_pure, show ((WriterT.run (pure value :
          WriterT (Multiplicative Tally) (StateT SigningLog (OracleComp OracleWorld)) α)).run
          log) = (pure ((value, (1 : Multiplicative Tally)), log) :
            OracleComp OracleWorld ((α × Multiplicative Tally) × SigningLog)) from rfl,
      simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
    rw [show result.1.1.2 = (1 : Multiplicative Tally) from by rw [hmem]]
    rfl
  | query_bind queried next ih =>
    intro log cache result hmem
    rw [simulateQ_bind, simulateQ_spec_query, run_writer_bind, simulateQ_bind, StateT.run_bind,
      mem_support_bind_iff] at hmem
    obtain ⟨outer, houter, hrest⟩ := hmem
    rw [simulateQ_map, StateT.run_map, support_map] at hrest
    obtain ⟨inner, hinner, heq⟩ := hrest
    have htail := ih outer.1.1.1 outer.1.2 outer.2 inner hinner
    have hhead : Multiset.card (Multiplicative.toAdd outer.1.1.2).2 =
        ((Multiplicative.toAdd outer.1.1.2).1).work := by
      rcases queried with world | request
      · exact card_eq_work_adversaryImpl world log cache outer houter
      · exact card_eq_work_signingOracle signer request log cache outer houter
    have hvalue : result.1.1.2 = outer.1.1.2 * inner.1.1.2 := by
      rw [← congrArg (fun z => z.1.1.2) heq]
    rw [hvalue, toAdd_mul]
    show Multiset.card ((Multiplicative.toAdd outer.1.1.2).2 +
      (Multiplicative.toAdd inner.1.1.2).2) =
        ((Multiplicative.toAdd outer.1.1.2).1 + (Multiplicative.toAdd inner.1.1.2).1).work
    rw [Multiset.card_add, AdversaryQueries.work_add, hhead, htail]

theorem countRecorded_pure {α : Type} (cost : OracleWorld.Domain → Tally) (value : α) :
    countRecorded cost (pure value) = pure (value, 0) := rfl

theorem countRecorded_query_bind {α : Type} (cost : OracleWorld.Domain → Tally)
    (queried : OracleWorld.Domain)
    (next : OracleWorld.Range queried → OracleComp OracleWorld α) :
    countRecorded cost (liftM (OracleWorld.query queried) >>= next) =
      liftM (OracleWorld.query queried) >>= fun answer =>
        (fun result => (result.1, cost queried + result.2)) <$>
          countRecorded cost (next answer) := by
  simp only [countRecorded, simulateQ_bind, simulateQ_spec_query, addCostOracle,
    QueryImpl.withAddCost, QueryImpl.withCost]
  simp [Functor.map_map, map_bind, bind_map_left]

/-- **The verifier's phase records exactly what it charges.** -/
theorem card_eq_work_countRecorded (cost : OracleWorld.Domain → Tally) (hcost : Faithful cost)
    {α : Type} (computation : OracleComp OracleWorld α) :
    ∀ (cache : QueryCache HashSpec) (result : (α × Tally) × QueryCache HashSpec),
      result ∈ support ((simulateQ KeygenUniform.rom
        (countRecorded cost computation)).run cache) →
        Multiset.card result.1.2.2 = (result.1.2.1).work := by
  induction computation using OracleComp.inductionOn with
  | pure value =>
    intro cache result hmem
    rw [countRecorded_pure, simulateQ_pure, StateT.run_pure, support_pure,
      Set.mem_singleton_iff] at hmem
    rw [show result.1.2 = (0 : Tally) from by rw [hmem]]
    rfl
  | query_bind queried next ih =>
    intro cache result hmem
    rw [countRecorded_query_bind, simulateQ_bind, simulateQ_spec_query, StateT.run_bind,
      mem_support_bind_iff] at hmem
    obtain ⟨step, -, hrest⟩ := hmem
    rw [simulateQ_map, StateT.run_map, support_map] at hrest
    obtain ⟨inner, hinner, heq⟩ := hrest
    have htail := ih step.1 step.2 inner hinner
    rw [show result.1.2 = cost queried + inner.1.2 from by rw [← heq]]
    show Multiset.card ((cost queried).2 + inner.1.2.2) =
      ((cost queried).1 + inner.1.2.1).work
    rw [Multiset.card_add, AdversaryQueries.work_add, hcost queried, htail]

/-! ## The deliverable -/

set_option linter.constructorNameAsVariable false in
set_option maxHeartbeats 1000000 in
/-- **The record is exactly as big as the work the game charges.** -/
theorem card_eq_work (adversary : Adversary) (sds : Digest × Digest × Digest)
    (warm cache : QueryCache HashSpec)
    (result : (Outcome × Multiset Bytes) × QueryCache HashSpec)
    (hmem : result ∈ support ((simulateQ KeygenUniform.rom
      (recordedAfterSeeds adversary sds warm)).run cache)) :
    Multiset.card result.1.2 = result.1.1.counts.work := by
  unfold recordedAfterSeeds at hmem
  rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hmem
  obtain ⟨⟨⟨sk, pk⟩, keyCache⟩, -, hmem⟩ := hmem
  rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hmem
  obtain ⟨⟨⟨⟨forgery, advTally⟩, signed⟩, advCache⟩, hadv, hmem⟩ := hmem
  rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hmem
  obtain ⟨⟨⟨verified, verifierTally⟩, verifyCache⟩, hverify, hmem⟩ := hmem
  rw [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
  have hadvCard := card_eq_work_adversary (StrippedGame.strippedSign warm sk)
    (adversary.main pk) [] keyCache ⟨⟨⟨forgery, advTally⟩, signed⟩, advCache⟩ hadv
  have hverifyCard := card_eq_work_countRecorded verifierCost faithful_verifierCost
    (Scheme.verify pk forgery.message forgery.signature) advCache
    ⟨⟨verified, verifierTally⟩, verifyCache⟩ hverify
  rw [show result.1.2 = (Multiplicative.toAdd advTally).2 + verifierTally.2 from by rw [hmem],
    show result.1.1.counts = (Multiplicative.toAdd advTally).1 + verifierTally.1 from by
      rw [hmem],
    Multiset.card_add, AdversaryQueries.work_add, hadvCard, hverifyCard]

attribute [local irreducible] recordedAfterSeeds StrippedGame.strippedAfterSeeds
  WarmedGame.afterSeeds Scheme.verify Scheme.keygenInternal Security.countQueries

/-- **The recorded set is no bigger than the charged work.** -/
theorem card_toFinset_le_work (adversary : Adversary) (sds : Digest × Digest × Digest)
    (warm cache : QueryCache HashSpec)
    (result : (Outcome × Multiset Bytes) × QueryCache HashSpec)
    (hmem : result ∈ support ((simulateQ KeygenUniform.rom
      (recordedAfterSeeds adversary sds warm)).run cache)) :
    (Multiset.toFinset result.1.2).card ≤ result.1.1.counts.work :=
  le_of_le_of_eq (Multiset.toFinset_card_le _)
    (card_eq_work adversary sds warm cache result hmem)

end SlhDsaSecurity.RecordedQueries
