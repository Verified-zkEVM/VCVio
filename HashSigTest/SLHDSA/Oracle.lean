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

abbrev Q := PublicHashQuery Nat Nat

example :
    (PublicHashQuery.thash 0 [] [7] : Q) ≠ PublicHashQuery.thash 1 [] [7] := by
  decide

example :
    (PublicHashQuery.thash 0 [] [3, 5] : Q) ≠
      PublicHashQuery.thash 0 [] [5, 3] := by
  decide

example :
    (PublicHashQuery.thash 0 [] [3] : Q) ≠ PublicHashQuery.thash 0 [] [3, 0] := by
  decide

example :
    (PublicHashQuery.thash 0 [] [7] : Q) ≠ PublicHashQuery.hmsg 7 0 9 [] := by
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

variable {p : Params} (prims : Primitives p)

/-- `F` is definitionally the singleton-input member of the same collection as `T_ℓ`. -/
example (pkSeed : prims.PkSeed) (adrs : Adrs) (x : prims.Y) :
    (PublicHash.f prims pkSeed adrs x : OracleComp (publicHashSpec prims) prims.Y) =
      PublicHash.tl prims pkSeed adrs [x] := rfl

/-- `H` is definitionally `T₂`, including the same cache identity. -/
example (pkSeed : prims.PkSeed) (adrs : Adrs) (left right : prims.Y) :
    (PublicHash.h prims pkSeed adrs left right : OracleComp (publicHashSpec prims) prims.Y) =
      PublicHash.tl prims pkSeed adrs [left, right] := rfl

/-- Addresses that serialize identically issue exactly the same oracle query. -/
example (pkSeed : prims.PkSeed) (a b : Adrs) (x : prims.Y)
    (h : prims.adrsToBytes a = prims.adrsToBytes b) :
    (PublicHash.f prims pkSeed a x : OracleComp (publicHashSpec prims) prims.Y) =
      PublicHash.f prims pkSeed b x := by
  unfold PublicHash.f
  rw [h]

/-- The deterministic handler recovers the bundle's common tweakable hash. -/
example (pkSeed : prims.PkSeed) (adrs : Adrs) (left right : prims.Y) :
    simulateQ (PublicHash.impl prims)
        (PublicHash.h prims pkSeed adrs left right :
          OracleComp (publicHashSpec prims) prims.Y) =
      prims.H pkSeed adrs left right := by
  simp

variable [DecidableEq prims.PkSeed] [DecidableEq prims.Y]
  [SampleableType prims.Y] [SampleableType (Bytes p.m)]

local instance publicHashRangeSampleable :
    ∀ q : PublicHashQuery prims.PkSeed prims.Y,
      SampleableType ((publicHashSpec prims).Range q) := fun q => by
  cases q <;> infer_instance

/-- A populated cell is a cache hit: it returns the stored value without changing state. -/
example (q : PublicHashQuery prims.PkSeed prims.Y)
    (u : (publicHashSpec prims).Range q) :
    (PublicHash.randomOracle prims q).run
        ((∅ : PublicHash.Cache prims).cacheQuery q u) =
      pure (u, (∅ : PublicHash.Cache prims).cacheQuery q u) := by
  rw [randomOracle.run_eq, QueryCache.cacheQuery_self]

/-- An empty cell is a cache miss: it samples once and stores the sampled value. -/
example (q : PublicHashQuery prims.PkSeed prims.Y) :
    (PublicHash.randomOracle prims q).run (∅ : PublicHash.Cache prims) =
      ($ᵗ (publicHashSpec prims).Range q) >>= fun u =>
        pure (u, (∅ : PublicHash.Cache prims).cacheQuery q u) := by
  rw [randomOracle.run_eq, QueryCache.empty_apply]

end Generic

/-! The SHA-2 instance keys by the exact 22-byte `ADRSc`. -/

open Concrete

example : shaPrimitives.adrsToBytes Adrs.zero =
    shaPrimitives.adrsToBytes (Adrs.zero.setLayerAddress 256) := by
  decide

example : shaPrimitives.adrsToBytes Adrs.zero =
    shaPrimitives.adrsToBytes (Adrs.zero.setTreeAddress (2 ^ 64)) := by
  decide

example : shaPrimitives.adrsToBytes Adrs.zero ≠
    shaPrimitives.adrsToBytes (Adrs.zero.setLayerAddress 1) := by
  decide

example : shaPrimitives.adrsToBytes Adrs.zero ≠
    shaPrimitives.adrsToBytes (Adrs.zero.setTreeAddress 1) := by
  decide

example : shaPrimitives.adrsToBytes Adrs.zero ≠
    shaPrimitives.adrsToBytes (Adrs.zero.setTypeAndClear .wotsPk) := by
  decide

example : shaPrimitives.adrsToBytes Adrs.zero ≠
    shaPrimitives.adrsToBytes (Adrs.zero.setKeyPairAddress 1) := by
  decide

example : shaPrimitives.adrsToBytes Adrs.zero ≠
    shaPrimitives.adrsToBytes (Adrs.zero.setChainAddress 1) := by
  decide

example : shaPrimitives.adrsToBytes Adrs.zero ≠
    shaPrimitives.adrsToBytes (Adrs.zero.setHashAddress 1) := by
  decide

end SLHDSA.PublicHashTest
