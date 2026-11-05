/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module

public import VCVio.OracleComp.QueryTracking.RandomOracle.CachePartial.Cost

/-!
# Full-word cache replay with query charges

Repeated warm calls pay their weights even when no answer is sampled.
The controls retain all 256 answer bits and arbitrary unrelated cache rows.
A stateful miss handler distinguishes a cache hit from a fresh draw.
-/

public section

open OracleSpec OracleComp

namespace VCVioTest.OracleComp.CostedCacheReplay

/-- Raw natural-number queries return entire 256-bit words. -/
abbrev Spec := Nat →ₒ BitVec 256

/-- Three calls repeat the first raw query after an unrelated one. -/
def repeated : OracleComp Spec (BitVec 256) := do
  let _ ← Spec.query 0
  let _ ← Spec.query 7
  Spec.query 0

/-- Each cache miss advances the sampler state exactly once. -/
def nextWord : QueryImpl Spec (StateM Nat) :=
  fun _ => StateT.mk fun n => pure (BitVec.ofNat 256 n, n + 1)

/-- Arbitrary warm words and extra rows survive all three weighted calls. -/
theorem warm_weighted {m : Type → Type} [Monad m] [LawfulMonad m]
    (so : QueryImpl Spec m) (w : Spec.Domain → Nat) (cache : Spec.QueryCache)
    (a b : BitVec 256) (h0 : cache 0 = some a) (h7 : cache 7 = some b) :
    ((simulateQ (so.withCaching.withAddCost w) repeated).runAdd).run cache =
      pure ((a, w 0 + w 7 + w 0), cache) := by
  simp [repeated, QueryImpl.withAddCost_apply, AddWriterT.runAdd, WriterT.run_bind,
    StateT.run_bind, StateT.run_map, QueryImpl.withCaching_apply, h0, h7, Nat.add_assoc]

/-- The public replay contract supplies one score for the partial and live interpretations. -/
example {m : Type → Type} [Monad m] [LawfulMonad m] (so : QueryImpl Spec m)
    (w : Spec.Domain → Nat) (known live : Spec.QueryCache) (hcache : known ≤ live)
    (a b : BitVec 256) (h0 : known 0 = some a) (h7 : known 7 = some b) :
    ∃ delta,
      simulateQ known.toPartialImpl
        (simulateQ ((QueryImpl.id' Spec).withAddCost w) repeated).runAdd = some (a, delta) ∧
      ((simulateQ (so.withCaching.withAddCost w) repeated).runAdd).run live =
        pure ((a, delta), live) := by
  apply QueryImpl.run_simulateQ_withCaching_withAddCost_eq_pure_of_toPartialImpl
    so w repeated known live hcache a
  simp [repeated, h0, h7]

/-- A positive charge is paid on each warm occurrence without advancing the miss sampler. -/
example (cache : Spec.QueryCache) (a b : BitVec 256) (start : Nat)
    (h0 : cache 0 = some a) (h7 : cache 7 = some b) :
    (((simulateQ (nextWord.withCaching.withAddCost (fun _ => 3)) repeated).runAdd).run cache).run
        start = (((a, 9), cache), start) := by
  rw [warm_weighted nextWord _ cache a b h0 h7]
  rfl

/-- A miss draws once, its repeated query hits, and the unrelated warm word is retained. -/
example (cache : Spec.QueryCache) (b : BitVec 256) (start : Nat)
    (h0 : cache 0 = none) (h7 : cache 7 = some b) :
    (((simulateQ (nextWord.withCaching.withAddCost (fun _ => 1)) repeated).runAdd).run cache).run
        start = (((BitVec.ofNat 256 start, 3),
          cache.cacheQuery 0 (BitVec.ofNat 256 start)), start + 1) := by
  simp [repeated, QueryImpl.withAddCost_apply, AddWriterT.runAdd, WriterT.run_bind,
    StateT.run_bind, StateT.run_map, QueryImpl.withCaching_apply, nextWord, h0, h7]
  rfl

/-- A missing query prevents settlement, even if the first query is known. -/
example (cache : Spec.QueryCache) (a : BitVec 256)
    (h0 : cache 0 = some a) (h7 : cache 7 = none) :
    simulateQ cache.toPartialImpl repeated = none := by
  simp [repeated, h0, h7]

/-- A cache extension can add a row while keeping the settled score and full live cache. -/
example {m : Type → Type} [Monad m] [LawfulMonad m] (so : QueryImpl Spec m)
    (known live : Spec.QueryCache) (a b extra : BitVec 256)
    (hcache : known ≤ live) (h0 : known 0 = some a) (h7 : known 7 = some b)
    (h99 : live 99 = some extra) :
    ((simulateQ (so.withCaching.withAddCost (fun t => t + 1)) repeated).runAdd).run live =
      pure ((a, 10), live) ∧ live 99 = some extra := by
  exact ⟨warm_weighted so _ live a b (hcache h0) (hcache h7), h99⟩

/-- A high-half bit is returned intact rather than projected to 128 bits. -/
example (cache : Spec.QueryCache) (b : BitVec 256)
    (h0 : cache 0 = some (BitVec.ofNat 256 (2 ^ 200))) (h7 : cache 7 = some b) :
    (((simulateQ (nextWord.withCaching.withAddCost (fun _ => 1)) repeated).runAdd).run cache).run
        23 = (((BitVec.ofNat 256 (2 ^ 200), 3), cache), 23) := by
  rw [warm_weighted nextWord _ cache _ b h0 h7]
  rfl

end VCVioTest.OracleComp.CostedCacheReplay
