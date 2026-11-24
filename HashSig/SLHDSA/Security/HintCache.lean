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

Consider two steps of a WOTS+ chain starting at `x`. At hash address `i`, the first query
hashes `x` to `y`. At address `i + 1`, the next query hashes `y` to `z`. Its input depends
on the first answer. If both entries occur in the same source cache, any cache extending it
replays the two steps and returns `z`. The
[two-step regression](../../../HashSigTest/SLHDSA/HintCache.lean)
checks this with the public hash queries used by the chain reader.

A public hint can select one replay cache for several source caches. If those sharing a hint
agree on every query they both answer, `exists_hint_cache_for_chains` supplies a single choice
per hint that preserves every successful chain read at every starting input and length.
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
