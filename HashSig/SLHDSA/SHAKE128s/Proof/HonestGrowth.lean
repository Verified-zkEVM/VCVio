/-
Copyright (c) 2026 Tom Wambsgans. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Wambsgans
-/

module

public import HashSig.SLHDSA.SHAKE128s.Proof.AdversaryQueries
public import HashSig.SLHDSA.SHAKE128s.Proof.KeygenCost
public import HashSig.SLHDSA.SHAKE128s.Proof.WarmedCharges
public import HashSig.SLHDSA.SHAKE128s.Proof.HonestProbes

/-!
# The canonical warm cache at key generation

A supported graph walk yields the canonical cache used when replaying key generation.
-/

public section

open OracleComp OracleSpec

namespace SLHDSA.SHAKE128s.HonestGrowth

open Security WarmedGame CacheReplay CanonicalGraph

/-- The walk's cache is the cache key generation is known to ask nothing new of. -/
theorem walk_cache_eq_warmCache
    {walk : ((Digest × Digest × Digest) × Cells) × QueryCache HashSpec}
    (hwalk : walk ∈ support graphWalk) :
    ∃ outputs : Programming.Outputs,
      walk.2 = HonestProbes.warmCache walk.1.1.2.2 walk.1.1.1 outputs := by
  obtain ⟨outputs, hcells, hcache⟩ := mem_support_graphWalk hwalk
  exact ⟨outputs, by rw [hcache, hcells]; rfl⟩

end SLHDSA.SHAKE128s.HonestGrowth
