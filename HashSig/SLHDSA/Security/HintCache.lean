/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import HashSig.SLHDSA.Security.CacheReaders
public import VCVio.OracleComp.QueryTracking.RandomOracle.CachePartial.Hint

/-!
# Replaying WOTS+ chain readings from a cache hint

A public label can select one cache for several hidden oracle histories. Every settled WOTS+
chain reading survives the choice when the selected cache contains each answer already present.
A family with consistent answers within each label admits such a choice for all chain inputs.
-/

public section

namespace SLHDSA.Security

open OracleSpec

variable {p : Params} {core : CorePrimitives p} {T H : Type*}

/-- A cache selected by a hint reproduces a settled WOTS+ chain of any length. -/
theorem chain?_eq_some_of_hint {cache : T → PublicHash.Cache core} {hint : T → H}
    {replay : H → PublicHash.Cache core}
    (extendsCache : ∀ t, cache t ≤ replay (hint t))
    (t : T) (pk : core.PkSeed) (adrs : Adrs) (x : core.Y) (i steps : ℕ) {y : core.Y}
    (settled : chain? core (cache t) pk adrs x i steps = some y) :
    chain? core (replay (hint t)) pk adrs x i steps = some y :=
  QueryCache.simulateQ_toPartialImpl_mono (extendsCache t) _ settled

/-- If caches with the same hint agree wherever both have an answer, one replay cache per hint
preserves every settled WOTS+ chain, simultaneously over all hidden states and chain inputs. -/
theorem exists_hint_cache_for_chains (cache : T → PublicHash.Cache core) (hint : T → H)
    (consistent : ∀ t t', hint t = hint t' → ∀ q b b', cache t q = some b →
      cache t' q = some b' → b = b') :
    ∃ replay : H → PublicHash.Cache core, ∀ t pk adrs x i steps y,
      chain? core (cache t) pk adrs x i steps = some y →
      chain? core (replay (hint t)) pk adrs x i steps = some y := by
  obtain ⟨replay, extendsCache⟩ := (QueryCache.exists_hint_upperBound_iff cache hint).2 consistent
  exact ⟨replay, fun t pk adrs x i steps _ =>
    chain?_eq_some_of_hint extendsCache t pk adrs x i steps⟩

end SLHDSA.Security
