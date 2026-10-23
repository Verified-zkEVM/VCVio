/-
Copyright (c) 2026 Tom Wambsgans. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Wambsgans
-/

module

public import HashSig.SLHDSA.SHAKE128s.Proof.AdversaryQueries
public import HashSig.SLHDSA.SHAKE128s.Proof.WarmedCharges
public import HashSig.SLHDSA.SHAKE128s.Proof.HonestProbes

/-!
# What key generation buys with the budget it spends

The target is `q / 2 ^ 127` exactly, and the charges carry three small defects that have to be
paid for out of the same budget. The room comes from the accounting itself: every hash call in
the game is charged, key generation's included, and after the graph is walked key generation
adds nothing to the cache. It spends and buys nothing.

So the growth a charge sees is bounded not by the whole count but by the count less what key
generation took. `HonestProbes.run_keygenInternal_world_eq_pure` is the half about the cache —
from the walk's table key generation is a `pure` computation, leaving the table exactly as it
found it — and `AdversaryQueries.mem_support_counted_bind_count` is the half about the count,
remembering how the total splits between the phases.

How much key generation takes is read off the Merkle recursion, and it is the whole subtree
rather than one path through it: every leaf ends in a compression call, so a subtree of height
`h` costs at least `2 ^ h`, and at `subtreeHeight` that is `512`. Following a single path would
give only `h + 1`, which covers the charges' defects but not the forgery's own claimed cells —
the input half records one candidate per claimed cell, a few hundred of them, and that is what
the larger constant pays for.
-/

@[expose] public section

open OracleComp OracleSpec

namespace SlhDsaSecurity.HonestGrowth

open Security WarmedGame CacheReplay CanonicalGraph

/-- The walk's cache is the cache key generation is known to ask nothing new of. -/
theorem walk_cache_eq_warmCache
    {walk : ((Digest × Digest × Digest) × Cells) × QueryCache HashSpec}
    (hwalk : walk ∈ support graphWalk) :
    ∃ outputs : Programming.Outputs,
      walk.2 = HonestProbes.warmCache walk.1.1.2.2 walk.1.1.1 outputs := by
  obtain ⟨outputs, hcells, hcache⟩ := mem_support_graphWalk hwalk
  exact ⟨outputs, by rw [hcache, hcells]; rfl⟩

/-! ## How much key generation spends

The exact number is not needed — the defects the charges carry sum to less than `2 ^ -125`, and
four units of budget at `2 ^ -127` apiece already exceed that.

What is proved is `pow_le_count_keygen : 2 ^ subtreeHeight ≤ count`, and the `4` of
`growth_le_count_sub_four` is that weakened by `omega`; it is not read off the recursion. The
*power* is, and the recursion doubles rather than adds: a node of height `h + 1` costs its two
children and one compression call, so a subtree of height `subtreeHeight = 9` costs at least
`2 ^ 9 = 512` — one call per **leaf**, not one per level. `pow_le_count_merkleNode` is that
induction. -/

/-- A single query is charged its own cost. -/
theorem count_query (queried : OracleWorld.Domain) (cache : QueryCache HashSpec)
    (result : (OracleWorld.Range queried × Nat) × QueryCache HashSpec)
    (hmem : result ∈ support ((simulateQ KeygenUniform.rom (countAllHashes
      (liftM (OracleWorld.query queried) :
        OracleComp OracleWorld (OracleWorld.Range queried)))).run cache)) :
    result.1.2 = hashCost queried := by
  rw [GrowthBudget.countAllHashes_query, simulateQ_bind, simulateQ_spec_query, StateT.run_bind,
    mem_support_bind_iff] at hmem
  obtain ⟨step, -, hpure⟩ := hmem
  rw [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hpure
  rw [hpure]

/-- A tweakable call is charged one unit. -/
theorem one_le_count_tweakable (publicSeed : Digest) (address : Address) (payload : Bytes)
    (cache : QueryCache HashSpec) (result : (Digest × Nat) × QueryCache HashSpec)
    (hmem : result ∈ support ((simulateQ KeygenUniform.rom (countAllHashes
      (Hashing.tweakable (m := OracleComp OracleWorld) publicSeed address payload))).run cache)) :
    1 ≤ result.1.2 := by
  rw [show (Hashing.tweakable (m := OracleComp OracleWorld) publicSeed address payload) =
      Hashing.truncate <$> (Hashing.hash (m := OracleComp OracleWorld)
        (Hashing.tweakableInput publicSeed address payload)) from by
      simp [Hashing.tweakable, Hashing.shortHash, map_eq_bind_pure_comp],
    AdversaryQueries.countAllHashes_map, simulateQ_map, StateT.run_map, support_map] at hmem
  obtain ⟨inner, hinner, heq⟩ := hmem
  have hcount := count_query (Sum.inr (Hashing.tweakableInput publicSeed address payload)) cache
    inner hinner
  rw [show result.1.2 = inner.1.2 from by rw [← heq], hcount]
  exact Nat.le_refl 1

attribute [local irreducible] SlhDsaSecurity.Merkle.node

attribute [local irreducible] WarmedGame.afterSeeds Scheme.keygenInternal Scheme.verify
  Scheme.sign Security.signingOracle Security.countQueries

end SlhDsaSecurity.HonestGrowth
