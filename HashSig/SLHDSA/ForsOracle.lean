/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import HashSig.SLHDSA.Fors
public import HashSig.SLHDSA.XmssOracle

/-!
# Oracle-parametric FORS

The FORS forest is evaluated with the callback-parametric perfect-Merkle engine.  Every public
`F`, `H`, and `T_l` application is an explicit `PublicHash` query, while authentication paths are
length-indexed by the FORS height `a`.  As with the XMSS layer, cache initialization is deliberately
left to the surrounding experiment.
-/

@[expose] public section

namespace SLHDSA

open PerfectMerkleTree

variable {p : Params}

namespace ForsOracle

/-- A FORS signature contains one secret value and an exactly `a`-node path per FORS tree. -/
abbrev Signature (p : Params) (prims : Primitives p) :=
  Vector (prims.Y × AuthenticationPath prims.Y p.a) p.k

/-- Evaluate a FORS leaf with one explicit `F` query. -/
def leafM (prims : Primitives p) {m : Type → Type*} [Monad m]
    [HasQuery (publicHashSpec prims) m] (sk : prims.SkSeed) (pk : prims.PkSeed) (adrs : Adrs)
    (index : ℕ) : m prims.Y :=
  PublicHash.f prims pk (forsNodeAdrs adrs 0 index) (forsSkGen prims sk pk adrs index)

/-- Evaluate a FORS internal node with an address-preserving `H` query. -/
def nodeHashM (prims : Primitives p) {m : Type → Type*} [HasQuery (publicHashSpec prims) m]
    (pk : prims.PkSeed) (adrs : Adrs) (address : Address) (left right : prims.Y) : m prims.Y :=
  PublicHash.h prims pk (forsNodeAdrs adrs address.height address.index) left right

/-- Compute one FORS tree root without allocating a full tree. -/
def rootM (prims : Primitives p) {m : Type → Type*} [Monad m]
    [HasQuery (publicHashSpec prims) m] (sk : prims.SkSeed) (pk : prims.PkSeed) (adrs : Adrs)
    (tree : Fin p.k) : m prims.Y :=
  treeHashM (leafM prims sk pk adrs) (nodeHashM prims pk adrs) p.a tree.val

/-- Generate the FORS public key using explicit tree and compression queries. -/
def pkGenM (prims : Primitives p) {m : Type → Type*} [Monad m]
    [HasQuery (publicHashSpec prims) m] (sk : prims.SkSeed) (pk : prims.PkSeed) (adrs : Adrs) :
    m prims.Y := do
  let roots ← (WotsOracle.indices p.k).mapM (rootM prims sk pk adrs)
  PublicHash.tl prims pk (forsPkAdrs adrs) roots.toList

/-- Sign a FORS digest with sized authentication paths and explicit public-hash queries. -/
def signM (prims : Primitives p) {m : Type → Type*} [Monad m]
    [HasQuery (publicHashSpec prims) m] (md : List Byte) (sk : prims.SkSeed) (pk : prims.PkSeed)
    (adrs : Adrs) : m (Signature p prims) :=
  (WotsOracle.indices p.k).mapM fun tree => do
    let index := tree.val * 2 ^ p.a + forsIdx p md tree.val
    let path ← authenticationPathM (leafM prims sk pk adrs) (nodeHashM prims pk adrs)
      0 index p.a
    pure (forsSkGen prims sk pk adrs index, path)

/-- Recover the FORS public key from a typed signature. -/
def pkFromSigM (prims : Primitives p) {m : Type → Type*} [Monad m]
    [HasQuery (publicHashSpec prims) m] (sig : Signature p prims) (md : List Byte)
    (pk : prims.PkSeed) (adrs : Adrs) : m prims.Y := do
  let roots ← (WotsOracle.indices p.k).mapM fun tree => do
    let index := tree.val * 2 ^ p.a + forsIdx p md tree.val
    let leaf ← PublicHash.f prims pk (forsNodeAdrs adrs 0 index) (sig[tree.val]).1
    climbM (nodeHashM prims pk adrs) 0 index p.a leaf (sig[tree.val]).2
  PublicHash.tl prims pk (forsPkAdrs adrs) roots.toList

@[simp]
theorem simulateQ_leafM (prims : Primitives p) (sk : prims.SkSeed) (pk : prims.PkSeed)
    (adrs : Adrs) (index : ℕ) :
    simulateQ (PublicHash.impl prims)
        (leafM prims sk pk adrs index : OracleComp (publicHashSpec prims) prims.Y) =
      forsLeaf prims sk pk adrs index := by
  simp [leafM, forsLeaf]

@[simp]
theorem simulateQ_nodeHashM (prims : Primitives p) (pk : prims.PkSeed) (adrs : Adrs)
    (address : Address) (left right : prims.Y) :
    simulateQ (PublicHash.impl prims)
        (nodeHashM prims pk adrs address left right :
          OracleComp (publicHashSpec prims) prims.Y) =
      forsNodeHash prims pk adrs address.height address.index left right := by
  simp [nodeHashM, forsNodeHash]

end ForsOracle

end SLHDSA
