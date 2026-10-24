/-
Copyright (c) 2026 Tom Wambsgans. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Wambsgans
-/

module

public import HashSig.SLHDSA.SHAKE128s.Proof.TableTail
public import HashSig.SLHDSA.SHAKE128s.Proof.LinkedGame
public import HashSig.SLHDSA.SHAKE128s.Proof.RecordedTail

/-!
# The keys as two cells of the table

Everything the honest linked run reads off the table goes through `TableTail.keysOf`, and
`keysOf_eq` says what that is: the secret key is the seed cell, the drawn `prfSeed`, and a public
key of the drawn `publicSeed` and the root cell. The root arrives as `Scheme.keygenInternal`'s own
`Merkle.node` call, run from the walk's cache; `CanonicalGraph.keygen_root_cell` names it as the
graph's top cell and `HonestProbes.replayCells_warmCache` evaluates it there — the cache was
built from those cells, so replaying it returns them. `honestKeys_eq` is the same statement for
the keys the cache determines.

So the run mentions only two table coordinates, the secret seed and the honest root. It is the
unstripped signer that makes this true: `StrippedGame.strippedSign` carries the walk's whole
cache as an argument and would mention every cell, whereas `Scheme.sign` carries only the key.
-/

public section

open OracleComp OracleSpec

namespace SlhDsaSecurity.TouchedKeys

open Security CanonicalGraph WalkTable TableTail KeygenValue

/-! ## The keys, as two cells -/

/-- **The keys the walk's cache determines are the seed cell and the root cell.** -/
theorem honestKeys_eq (sds : Digest × Digest × Digest) (outputs : Programming.Outputs) :
    honestKeys sds outputs =
      (⟨sds.1, sds.2.1,
          ⟨sds.2.2, Programming.cellsOfOutputs sds.1 outputs (.structural topRoot)⟩⟩,
        ⟨sds.2.2, Programming.cellsOfOutputs sds.1 outputs (.structural topRoot)⟩) := by
  have hroot : (honestKeys sds outputs).2.root =
      Programming.cellsOfOutputs sds.1 outputs (.structural topRoot) :=
    (@keygen_root_cell (CacheReplay.replayQuery (HonestProbes.warmCache sds.2.2 sds.1 outputs))
      sds.1 sds.2.1 sds.2.2).trans
      (congrFun (HonestProbes.replayCells_warmCache sds.2.2 sds.1 outputs) (.structural topRoot))
  rw [show honestKeys sds outputs =
    (⟨sds.1, sds.2.1, ⟨sds.2.2, (honestKeys sds outputs).2.root⟩⟩,
      ⟨sds.2.2, (honestKeys sds outputs).2.root⟩) from rfl, hroot]

/-- **The keys at a drawn table are two of its cells.** -/
theorem keysOf_eq (prfSeed publicSeed : Digest) (table : Cells × Padding) :
    keysOf prfSeed publicSeed table =
      (⟨table.1 Node.secretSeed, prfSeed,
          ⟨publicSeed, table.1 (.structural topRoot)⟩⟩,
        ⟨publicSeed, table.1 (.structural topRoot)⟩) := by
  rw [keysOf, honestKeys_eq, cellsOfOutputs_fullOutput]

end SlhDsaSecurity.TouchedKeys
