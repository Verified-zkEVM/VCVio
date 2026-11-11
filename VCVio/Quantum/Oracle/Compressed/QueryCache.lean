/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.OracleComp.QueryTracking.Structures
public import VCVio.Quantum.Oracle.Compressed.Basic

/-!
# Compressed-oracle databases as query caches

A database `Quantum.Database X Y` of the compressed oracle is a partial table `X → Option Y`
(`VCVio.Quantum.Oracle.Compressed.Basic`). This is the same data as VCVio's query cache
`OracleSpec.QueryCache (X →ₒ Y)` for the single oracle `X →ₒ Y`, the partial answer table of the
classical lazy random oracle.

## Main definitions

* `Quantum.Database.equivQueryCache`: the equivalence between databases and query caches, with
  `Quantum.Database.equivQueryCache_apply` and `Quantum.Database.equivQueryCache_empty`.
-/

public section

namespace Quantum

namespace Database

/-- Databases are VCVio's query caches for the oracle `X →ₒ Y`, the partial answer tables of the
classical lazy random oracle. -/
@[expose]
def equivQueryCache {X Y : Type} : Database X Y ≃ OracleSpec.QueryCache (X →ₒ Y) :=
  OracleSpec.QueryCache.equivFn.symm

@[simp]
theorem equivQueryCache_apply {X Y : Type} (D : Database X Y) (x : X) :
    equivQueryCache D x = D x :=
  rfl

/-- The empty database is the empty cache. -/
@[simp]
theorem equivQueryCache_empty {X Y : Type} :
    equivQueryCache (empty : Database X Y) = ∅ :=
  rfl

end Database

end Quantum
