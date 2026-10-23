/-
Copyright (c) 2026 Tom Wambsgans. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Wambsgans
-/

module

public import HashSig.SLHDSA.SHAKE128s.Proof.RecordedQueries
public import HashSig.SLHDSA.SHAKE128s.Proof.WarmedSplit

/-!
# The warmed tail, carrying the adversary's record as a value

A charge on the adversary's own hash inputs needs the record to be a *value of the computation
whose probability is being bounded*; an existentially quantified record over the support is
useless, since a one-element multiset satisfies it whenever the run charges anything.

`RecordedQueries` builds that presentation for the **stripped** game. The randomiser defect is
stated over `WarmedGame.afterSeeds`, the game with the real `Scheme.keygenInternal` and
`Scheme.sign`, so the same presentation is built here at those. The construction is
`RecordedQueries`' verbatim, recording in the writer that already carries the counters, at
exactly the adversary's handler and the verifier's instrumentation, and so are the two facts
about it: forgetting the record returns the game exactly, and the record's cardinality is the
work the game charges.

`tail_eq_map_recordedTail` is what the charges read: the warmed tail **is** the recorded tail
with the record dropped, as an equality of computations, so a probability at the one is a
probability at the other and nothing is paid for the instrumentation.
-/

@[expose] public section

open OracleComp OracleSpec

namespace SlhDsaSecurity.RecordedTail

variable {α β : Type}

open Security RecordedQueries

/-! ## The game, recording the adversary's and the verifier's own inputs -/

/-- `WarmedGame.afterSeeds`, recording the adversary's and the verifier's own hash inputs. -/
noncomputable def recordedAfterSeeds (adversary : Adversary) (sds : Digest × Digest × Digest) :
    OracleComp OracleWorld (Outcome × Multiset Bytes) := do
  let (sk, pk) ← Scheme.keygenInternal sds.1 sds.2.1 sds.2.2
  let ((forgery, adversaryTally), signed) ←
    (simulateQ (recordedAdversaryImpl + recordedSigningOracle (Scheme.sign sk))
      (adversary.main pk)).run.run []
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
/-- **The recording is invisible.** Forgetting it returns the game exactly. -/
theorem map_recordedAfterSeeds (adversary : Adversary) (sds : Digest × Digest × Digest) :
    Prod.fst <$> recordedAfterSeeds adversary sds = WarmedGame.afterSeeds adversary sds := by
  unfold recordedAfterSeeds WarmedGame.afterSeeds
  rw [map_bind]
  refine congrArg (Bind.bind _) (funext fun keys => ?_)
  obtain ⟨sk, pk⟩ := keys
  dsimp only
  rw [map_bind,
    show ((simulateQ
        (((QueryImpl.ofLift OracleWorld (StateT SigningLog (OracleComp OracleWorld))).withAddCost
            fun input => Counts.single Game.QueryKind.hash (hashCost input)) +
          Security.signingOracle sk) (adversary.main pk)).run).run [] =
      (fun step => ((step.1.1, forget step.1.2), step.2)) <$>
        ((simulateQ (recordedAdversaryImpl + recordedSigningOracle (Scheme.sign sk))
          (adversary.main pk)).run).run [] from by
      rw [run_simulateQ_map_writer forget forget_one forget_mul
        (recordedAdversaryImpl + recordedSigningOracle (Scheme.sign sk))
        (((QueryImpl.ofLift OracleWorld (StateT SigningLog (OracleComp OracleWorld))).withAddCost
            fun input => Counts.single Game.QueryKind.hash (hashCost input)) +
          Security.signingOracle sk)
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

/-! ## The record is as big as the charge, here too -/

set_option linter.constructorNameAsVariable false in
set_option maxHeartbeats 1000000 in
/-- **The record is exactly as big as the work the game charges.** -/
theorem card_eq_work (adversary : Adversary) (sds : Digest × Digest × Digest)
    (cache : QueryCache HashSpec)
    (result : (Outcome × Multiset Bytes) × QueryCache HashSpec)
    (hmem : result ∈ support ((simulateQ KeygenUniform.rom
      (recordedAfterSeeds adversary sds)).run cache)) :
    Multiset.card result.1.2 = result.1.1.counts.work := by
  unfold recordedAfterSeeds at hmem
  rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hmem
  obtain ⟨⟨⟨sk, pk⟩, keyCache⟩, -, hmem⟩ := hmem
  rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hmem
  obtain ⟨⟨⟨⟨forgery, advTally⟩, signed⟩, advCache⟩, hadv, hmem⟩ := hmem
  rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hmem
  obtain ⟨⟨⟨verified, verifierTally⟩, verifyCache⟩, hverify, hmem⟩ := hmem
  rw [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
  have hadvCard := card_eq_work_adversary (Scheme.sign sk)
    (adversary.main pk) [] keyCache ⟨⟨⟨forgery, advTally⟩, signed⟩, advCache⟩ hadv
  have hverifyCard := card_eq_work_countRecorded verifierCost faithful_verifierCost
    (Scheme.verify pk forgery.message forgery.signature) advCache
    ⟨⟨verified, verifierTally⟩, verifyCache⟩ hverify
  rw [show result.1.2 = (Multiplicative.toAdd advTally).2 + verifierTally.2 from by rw [hmem],
    show result.1.1.counts = (Multiplicative.toAdd advTally).1 + verifierTally.1 from by
      rw [hmem],
    Multiset.card_add, AdversaryQueries.work_add, hadvCard, hverifyCard]

attribute [local irreducible] recordedAfterSeeds WarmedGame.afterSeeds Scheme.verify
  Scheme.keygenInternal Security.countQueries

/-- **The recorded set is no bigger than the charged work.** -/
theorem card_toFinset_le_work (adversary : Adversary) (sds : Digest × Digest × Digest)
    (cache : QueryCache HashSpec)
    (result : (Outcome × Multiset Bytes) × QueryCache HashSpec)
    (hmem : result ∈ support ((simulateQ KeygenUniform.rom
      (recordedAfterSeeds adversary sds)).run cache)) :
    (Multiset.toFinset result.1.2).card ≤ result.1.1.counts.work :=
  le_of_le_of_eq (Multiset.toFinset_card_le _) (card_eq_work adversary sds cache result hmem)

/-! ## The tail, with the record carried along

The hash counter sits outside the recording writer — `countAllHashes` wraps the whole of
`afterSeeds`, record and all — so dropping the record commutes with counting, and the warmed
tail is the recorded tail read through that projection. -/

/-- Counting every hash call commutes with a projection of the value. -/
theorem countAllHashes_map {α β : Type} (f : α → β) (computation : OracleComp OracleWorld α) :
    countAllHashes (f <$> computation) =
      (fun result => (f result.1, result.2)) <$> countAllHashes computation := by
  rw [countAllHashes, countAllHashes, simulateQ_map, WriterT.run_map, Functor.map_map,
    Functor.map_map]

/-- The counted game played from what the walk left, carrying the record. -/
noncomputable def recordedTail (adversary : Adversary)
    (start : ((Digest × Digest × Digest) × CanonicalGraph.Cells) × QueryCache HashSpec) :
    ProbComp (((Outcome × Multiset Bytes) × Nat) × QueryCache HashSpec) :=
  (simulateQ KeygenUniform.rom
    (countAllHashes (recordedAfterSeeds adversary start.1.1))).run start.2

/-- **The warmed tail is the recorded tail with the record dropped.** -/
theorem tail_eq_map_recordedTail (adversary : Adversary)
    (start : ((Digest × Digest × Digest) × CanonicalGraph.Cells) × QueryCache HashSpec) :
    WarmedGame.tail adversary start =
      (fun result => ((result.1.1.1, result.1.2), result.2)) <$>
        recordedTail adversary start := by
  rw [WarmedGame.tail, recordedTail, ← map_recordedAfterSeeds adversary start.1.1,
    countAllHashes_map, simulateQ_map, StateT.run_map]

/-- **A result of the recorded tail is a result of the tail**, with the record besides. -/
theorem mem_support_tail_of_recorded (adversary : Adversary)
    {start : ((Digest × Digest × Digest) × CanonicalGraph.Cells) × QueryCache HashSpec}
    {result : ((Outcome × Multiset Bytes) × Nat) × QueryCache HashSpec}
    (hresult : result ∈ support (recordedTail adversary start)) :
    ((result.1.1.1, result.1.2), result.2) ∈ support (WarmedGame.tail adversary start) := by
  rw [tail_eq_map_recordedTail, support_map]
  exact ⟨result, hresult, rfl⟩

/-- **The recorded set is no bigger than the budget**, read at the tail. -/
theorem card_toFinset_le_count (adversary : Adversary)
    {start : ((Digest × Digest × Digest) × CanonicalGraph.Cells) × QueryCache HashSpec}
    {result : ((Outcome × Multiset Bytes) × Nat) × QueryCache HashSpec}
    (hresult : result ∈ support (recordedTail adversary start)) :
    (Multiset.toFinset result.1.1.2).card ≤ result.1.1.1.counts.work :=
  card_toFinset_le_work adversary start.1.1 start.2 (result.1.1, result.2)
    (WarmedSplit.mem_support_of_countAllHashes _ start.2 result hresult)

end SlhDsaSecurity.RecordedTail
