/-
Copyright (c) 2026 Tom Wambsgans. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Wambsgans
-/

module

public import HashSig.SLHDSA.SHAKE128s.Proof.WalkTable
public import HashSig.SLHDSA.SHAKE128s.Proof.LinkedGame
public import HashSig.SLHDSA.SHAKE128s.Proof.RecordedBudget
public import HashSig.SLHDSA.SHAKE128s.Proof.RedrawCell

/-!
# The tail at a drawn table, as one computation under one handler

`linkedRun` is the game at the walk a drawn table determines, written as one computation under
one handler with the keys handed in (`keysOf`) and the record kept. It is reached from
`WarmedGame.tail` by equalities rather than bounds:

* **The outer count is dropped.** `tail` counts every hash call and the downstream event never
  reads that count. `RecordedBudget.map_countAllHashes` is the projection.
* **The honest phase is stripped.** Key generation and the signer are answered from the walk's
  own table, which changes nothing about the law of the run and leaves them asking only inputs
  no table of graph cells holds.
* **The record is kept.** Forgetting it returns the stripped game exactly.
* **The keys are handed in.** Run from the walk's cache, key generation samples nothing, so the
  key may be the value the cache determines (`KeygenValue.run_recordedAfterSeeds`), which is
  what lets the signer move into the handler.
* **The game becomes one computation.** `LinkedGame.recordedAfterSeedsAt_eq` is that move, an
  equality of computations, so every field of the outcome survives it unchanged.

`walkOfTable_cache` says the cache a drawn table's walk leaves is the warm cache of that table's
own cells and padding, the form `KeygenValue.run_recordedAfterSeeds` is stated at.
-/

@[expose] public section

open OracleComp OracleSpec

namespace SlhDsaSecurity.TableTail

open Security CanonicalGraph WarmedGame WalkTable

/-! ## The cache a drawn table leaves -/

/-- **The walk's cache is the warm cache of the table's own output table.** -/
theorem walkOfTable_cache (prfSeed publicSeed : Digest) (table : Cells × Padding) :
    (walkOfTable prfSeed publicSeed table).2 =
      HonestProbes.warmCache publicSeed (table.1 Node.secretSeed)
        (fullOutput table.1 table.2) := by
  rw [walkOfTable, HonestProbes.warmCache, cellsOfOutputs_fullOutput]

/-- The keys the drawn table's own cache determines. Their only table coordinates are the secret
seed and the honest root, which is what the charge's blindness hypothesis asks of them. -/
noncomputable def keysOf (prfSeed publicSeed : Digest) (table : Cells × Padding) :
    SecretKey × PublicKey :=
  KeygenValue.honestKeys (table.1 Node.secretSeed, prfSeed, publicSeed)
    (fullOutput table.1 table.2)

/-- The game at a drawn table, as one computation under one handler. -/
noncomputable def linkedRun (adversary : Adversary) (prfSeed publicSeed : Digest)
    (table : Cells × Padding) :
    ProbComp ((((Forgery × Multiplicative RecordedQueries.Tally) ×
      (Bool × RecordedQueries.Tally)) × SigningLog) × QueryCache HashSpec) :=
  (simulateQ KeygenUniform.rom
    ((simulateQ (RecordedPhase.unchargedPhase
        (StrippedGame.strippedSign (walkOfTable prfSeed publicSeed table).2
          (keysOf prfSeed publicSeed table).1))
      (LinkedGame.linkedAfterSeeds adversary (keysOf prfSeed publicSeed table))).run [])).run
    (walkOfTable prfSeed publicSeed table).2

end SlhDsaSecurity.TableTail
