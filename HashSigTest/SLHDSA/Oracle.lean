/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import HashSig.SLHDSA.Oracle
public import HashSig.SLHDSA.Concrete.Instance

/-!
# Producer canaries for the SLH-DSA public-hash collection

These examples pin the collection identity, canonical address encoding, deterministic bridge,
and lazy-cache hit/miss behavior.  In particular, `F`, `H = T₂`, and `T_ℓ` share one cache.
-/

public section

open OracleComp OracleSpec

namespace SLHDSA.PublicHashTest

abbrev Q := PublicHashQuery Nat Nat Nat

example :
    (PublicHashQuery.thash 0 0 [7] : Q) ≠ PublicHashQuery.thash 1 0 [7] := by
  decide

example :
    (PublicHashQuery.thash 0 0 [3, 5] : Q) ≠
      PublicHashQuery.thash 0 0 [5, 3] := by
  decide

example :
    (PublicHashQuery.thash 0 0 [3] : Q) ≠ PublicHashQuery.thash 0 0 [3, 0] := by
  decide

example :
    (PublicHashQuery.thash 0 0 [7] : Q) ≠ PublicHashQuery.hmsg 7 0 9 [] := by
  decide

example :
    (PublicHashQuery.hmsg 7 0 9 [] : Q) ≠ PublicHashQuery.hmsg 8 0 9 [] := by
  decide

example :
    (PublicHashQuery.hmsg 7 0 9 [] : Q) ≠ PublicHashQuery.hmsg 7 1 9 [] := by
  decide

example :
    (PublicHashQuery.hmsg 7 0 9 [] : Q) ≠ PublicHashQuery.hmsg 7 0 10 [] := by
  decide

example :
    (PublicHashQuery.hmsg 7 0 9 [] : Q) ≠ PublicHashQuery.hmsg 7 0 9 [0] := by
  decide

section Generic

variable {p : Params} (core : CorePrimitives p)

/-- `F` is definitionally the singleton-input member of the same collection as `T_ℓ`. -/
example (pkSeed : core.PkSeed) (adrs : Adrs) (x : core.Y) :
    (PublicHash.f core pkSeed adrs x : OracleComp (publicHashSpec core) core.Y) =
      PublicHash.tl core pkSeed adrs [x] := rfl

/-- `H` is definitionally `T₂`, including the same cache identity. -/
example (pkSeed : core.PkSeed) (adrs : Adrs) (left right : core.Y) :
    (PublicHash.h core pkSeed adrs left right : OracleComp (publicHashSpec core) core.Y) =
      PublicHash.tl core pkSeed adrs [left, right] := rfl

/-- Addresses that serialize identically issue exactly the same oracle query. -/
example (pkSeed : core.PkSeed) (a b : Adrs) (x : core.Y)
    (h : core.adrsToKey a = core.adrsToKey b) :
    (PublicHash.f core pkSeed a x : OracleComp (publicHashSpec core) core.Y) =
      PublicHash.f core pkSeed b x := by
  unfold PublicHash.f
  rw [h]

variable [DecidableEq core.PkSeed] [DecidableEq core.AdrsKey] [DecidableEq core.Y]
  [SampleableType core.Y] [SampleableType (Bytes p.m)]

local instance publicHashRangeSampleable :
    ∀ q : PublicHashQuery core.PkSeed core.AdrsKey core.Y,
      SampleableType ((publicHashSpec core).Range q) := fun q => by
  cases q <;> infer_instance

/-- A populated cell is a cache hit: it returns the stored value without changing state. -/
example (q : PublicHashQuery core.PkSeed core.AdrsKey core.Y)
    (u : (publicHashSpec core).Range q) :
    (PublicHash.randomOracle core q).run
        ((∅ : PublicHash.Cache core).cacheQuery q u) =
      pure (u, (∅ : PublicHash.Cache core).cacheQuery q u) := by
  rw [randomOracle.run_eq, QueryCache.cacheQuery_self]

/-- An empty cell is a cache miss: it samples once and stores the sampled value. -/
example (q : PublicHashQuery core.PkSeed core.AdrsKey core.Y) :
    (PublicHash.randomOracle core q).run (∅ : PublicHash.Cache core) =
      ($ᵗ (publicHashSpec core).Range q) >>= fun u =>
        pure (u, (∅ : PublicHash.Cache core).cacheQuery q u) := by
  rw [randomOracle.run_eq, QueryCache.empty_apply]

end Generic

section Deterministic

variable {p : Params} (prims : Primitives p)

/-- The deterministic handler recovers the bundle's common tweakable hash. -/
example (pkSeed : prims.PkSeed) (adrs : Adrs) (left right : prims.Y) :
    simulateQ (PublicHash.impl prims)
        (PublicHash.h prims.core pkSeed adrs left right :
          OracleComp (publicHashSpec prims.core) prims.Y) =
      prims.H pkSeed adrs left right := by
  simp

/-- Replacing the deterministic public handler leaves the implementation-independent context
definitionally unchanged. -/
example (answer : QueryImpl (publicHashSpec prims.core) Id) :
    (PublicHash.withPublicHash prims.core answer).core = prims.core := rfl

end Deterministic

/-! The SHA-2 instance keys by the exact 22-byte `ADRSc`. -/

open Concrete

example : shaPrimitives.AdrsKey = Bytes 22 := rfl

example (adrs : Adrs) : shaPrimitives.adrsToKey adrs = shaAdrsKey adrs := rfl

example (adrs : Adrs) : (shaPrimitives.adrsToKey adrs).toList = adrs.compressSha2 := by
  change (shaAdrsKey adrs).toList = adrs.compressSha2
  exact shaAdrsKey_toList adrs

example : shaPrimitives.adrsToKey Adrs.zero =
    shaPrimitives.adrsToKey (Adrs.zero.setLayerAddress 256) := by
  change shaAdrsKey Adrs.zero = shaAdrsKey (Adrs.zero.setLayerAddress 256)
  apply Vector.toArray_inj.mp
  simpa [shaAdrsKey] using
    (show Adrs.zero.compressSha2 = (Adrs.zero.setLayerAddress 256).compressSha2 by decide)

example : shaPrimitives.adrsToKey Adrs.zero =
    shaPrimitives.adrsToKey (Adrs.zero.setTreeAddress (2 ^ 64)) := by
  change shaAdrsKey Adrs.zero = shaAdrsKey (Adrs.zero.setTreeAddress (2 ^ 64))
  apply Vector.toArray_inj.mp
  simpa [shaAdrsKey] using
    (show Adrs.zero.compressSha2 =
      (Adrs.zero.setTreeAddress (2 ^ 64)).compressSha2 by decide)

example : Adrs.zero.compressSha2 ≠ (Adrs.zero.setLayerAddress 1).compressSha2 := by
  decide

example : Adrs.zero.compressSha2 ≠ (Adrs.zero.setTreeAddress 1).compressSha2 := by
  decide

example : Adrs.zero.compressSha2 ≠ (Adrs.zero.setTypeAndClear .wotsPk).compressSha2 := by
  decide

example : Adrs.zero.compressSha2 ≠ (Adrs.zero.setKeyPairAddress 1).compressSha2 := by
  decide

example : Adrs.zero.compressSha2 ≠ (Adrs.zero.setChainAddress 1).compressSha2 := by
  decide

example : Adrs.zero.compressSha2 ≠ (Adrs.zero.setHashAddress 1).compressSha2 := by
  decide

end SLHDSA.PublicHashTest
