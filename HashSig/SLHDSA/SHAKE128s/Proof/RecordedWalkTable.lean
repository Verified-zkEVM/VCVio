/-
Copyright (c) 2026 Tom Wambsgans. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Wambsgans
-/

module

public import HashSig.SLHDSA.SHAKE128s.Proof.WalkTable
public import HashSig.SLHDSA.SHAKE128s.Proof.RandomiserRecord
public import HashSig.SLHDSA.SHAKE128s.Proof.ClassGrowth

/-!
# The recorded paired run, with its walk drawn as a table

`WalkTable` presents the walk as a uniform cells-and-padding pair. This file carries that
presentation to `RandomiserRecord.recordedPairedRun`, the recorded paired run the shared side
reads: `recordedTableRun` is the recorded game at a drawn table with the walk it determines kept,
and `evalDist_recordedPairedRun` says the recorded paired run draws its table, the two seeds
first. Conditioning on the walk fixes the cell table, so the shared side averages over the two
seeds the table does not carry, with the table still in the measure.
-/

public section

open OracleComp OracleSpec ENNReal

namespace SlhDsaSecurity.RecordedWalkTable

open Security WarmedGame WalkTable

/-! ## The recorded paired run at a drawn table -/

/-- The recorded game at a drawn table, with the walk it determines kept. -/
@[expose] noncomputable def recordedTableRun (adversary : Adversary) (prfSeed publicSeed : Digest) :
    ProbComp ((((Digest × Digest × Digest) × CanonicalGraph.Cells) × QueryCache HashSpec) ×
      (((Outcome × Multiset Bytes) × Nat) × QueryCache HashSpec)) := do
  let table ← ($ᵗ (CanonicalGraph.Cells × CanonicalGraph.Padding) :
    ProbComp (CanonicalGraph.Cells × CanonicalGraph.Padding))
  let result ← RecordedTail.recordedTail adversary (walkOfTable prfSeed publicSeed table)
  pure (walkOfTable prfSeed publicSeed table, result)

/-- **The recorded paired run draws its table.** -/
theorem evalDist_recordedPairedRun (adversary : Adversary) :
    RandomiserRecord.recordedPairedRun adversary =ᵈ
      (do
        let prfSeed ← ($ᵗ Digest : ProbComp Digest)
        let publicSeed ← ($ᵗ Digest : ProbComp Digest)
        recordedTableRun adversary prfSeed publicSeed) := by
  rw [RandomiserRecord.recordedPairedRun]
  refine (EvalDistEq.bind_left evalDist_graphWalk _).trans ?_
  rw [tableWalk]
  simp only [recordedTableRun, bind_assoc, pure_bind]
  exact EvalDistEq.refl _

end SlhDsaSecurity.RecordedWalkTable
