/-
Copyright (c) 2026 Tom Wambsgans. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Wambsgans
-/

module

public import HashSig.SLHDSA.SHAKE128s.Proof.CacheReplay
public import HashSig.SLHDSA.SHAKE128s.Proof.Extraction.BinaryPath

/-!
# A verifier path's queries are cached

Chaining the peeling lemmas onto a verifier path: a fold of tweakable calls, one per height,
whose charge needs an entry in the cache at the byte input of the step where the collision
sits.

The scheme has two such paths and they have the same shape, so this is stated once over an
arbitrary `addressOf`. The hypertree's Merkle path instantiates it at
`Merkle.nodeAddress address` and `subtreeHeight`; a FORS tree's path, which
`Extraction.Fors.recoveredRoot` folds, instantiates it at `Fors.nodeAddress address` and
`forsHeight`. Writing it once was not foresight — the Merkle version came first and the FORS
path turned out to reuse it unchanged.

Three identifications do it. `CacheReplay.queriesUnder_foldlM_get` says the `k`-th step
consults its input at the value `replayFold` has reached; `CacheReplay.replayFold_eq_foldl`
and `CacheReplay.foldl_finRange_take` rewrite that value as a fold over `List.finRange k`;
and `Extraction.BinaryPath.value_eq_fold` recognises *that* fold as
`Extraction.BinaryPath.value`, which is the value the collision is stated about.

The step of the replayed fold is `Hashing.tweakable` under `CacheReplay.replayQuery`
(`CacheReplay.replayFold_step_eq_tweakable`), so the `combine` the extraction reasons with and
the advance the replay performs are the same function.
-/

@[expose] public section

open OracleComp OracleSpec

namespace SlhDsaSecurity.PathEntry

open CacheReplay Extraction

/-- The byte input the Merkle path's `j`-th step hashes. -/
def pathInput {height : Nat} (publicSeed : Digest) (addressOf : Nat → Nat → Address)
    (index : Nat) (siblings : Nat → Digest) : Digest → Fin height → Bytes :=
  fun value j => Hashing.tweakableInput publicSeed
    (addressOf (j.val + 1) (index / 2 ^ (j.val + 1)))
    (BinaryPath.pairBytes (BinaryPath.ordered index j.val value (siblings j.val)))

/-- The recombination the extraction reasons with, answered from this cache. -/
noncomputable def pathCombine (cache : QueryCache HashSpec) (publicSeed : Digest)
    (addressOf : Nat → Nat → Address) : Nat → Nat → Digest → Digest → Digest :=
  fun nodeHeight nodeIndex left right =>
    @Hashing.tweakable Id _ (replayQuery cache) publicSeed (addressOf nodeHeight nodeIndex)
      (BinaryPath.pairBytes (left, right))

/-- **The replayed path fold is the extraction's path value.** -/
theorem replayFold_eq_value (cache : QueryCache HashSpec) (publicSeed : Digest)
    (addressOf : Nat → Nat → Address) (index : Nat) (leaf : Digest) (siblings : Nat → Digest)
    (height k : Nat) (hk : k ≤ height) :
    replayFold cache (pathInput (height := height) publicSeed addressOf index siblings)
        ((List.finRange height).take k) leaf =
      BinaryPath.value (pathCombine cache publicSeed addressOf) index leaf siblings k := by
  rw [replayFold_eq_foldl, BinaryPath.value_eq_fold]
  exact foldl_finRange_take height k hk
    (fun value j => Hashing.truncate (replay cache (Hashing.tweakableInput publicSeed
      (addressOf (j + 1) (index / 2 ^ (j + 1)))
      (BinaryPath.pairBytes (BinaryPath.ordered index j value (siblings j)))))) leaf

/-- **The `step`-th call of the fold consults its input** at the running value the extraction's
`BinaryPath.value` names. -/
theorem queriesUnder_pathInput {height : Nat} (cache : QueryCache HashSpec)
    (publicSeed : Digest) (addressOf : Nat → Nat → Address) (index : Nat) (leaf : Digest)
    (siblings : Nat → Digest) (step : Fin height) :
    QueriesUnder cache
      ((List.finRange height).foldlM (m := OracleComp HashSpec)
        (fun value j => Hashing.shortHash
          (pathInput publicSeed addressOf index siblings value j)) leaf)
      (pathInput publicSeed addressOf index siblings
        (BinaryPath.value (pathCombine cache publicSeed addressOf) index leaf siblings step.val)
        step) := by
  have hlt : step.val < (List.finRange height).length := by simp [step.isLt]
  have hquery := queriesUnder_foldlM_get cache
    (pathInput (height := height) publicSeed addressOf index siblings)
    (List.finRange height) leaf step.val hlt
  rwa [show (List.finRange height)[step.val]'hlt = step from by apply Fin.ext; simp,
    replayFold_eq_value cache publicSeed addressOf index leaf siblings height step.val
      (le_of_lt step.isLt)] at hquery

end SlhDsaSecurity.PathEntry
