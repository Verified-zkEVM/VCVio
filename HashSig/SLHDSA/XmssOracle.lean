/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import HashSig.SLHDSA.WotsOracle
public import HashSig.SLHDSA.Xmss
public import VCVio.CryptoFoundations.MerkleTree.Perfect

/-!
# Oracle-parametric XMSS

This module connects the explicit SLH-DSA public-hash syntax to the streaming perfect-Merkle
engine.  WOTS+ leaves are effectful, every internal node is an address-preserving `H` query, leaf
indices are bounded by `2^h'`, and authentication paths have exactly `h'` entries.

None of the definitions initializes an oracle cache.  Key generation, signing, verification, and
an adversary can therefore be placed inside one caller-owned execution of
`PublicHash.randomOracle`, which is the consistency boundary required by the random-oracle model.
-/

@[expose] public section

namespace SLHDSA

open PerfectMerkleTree

variable {p : Params}

namespace XmssOracle

/-- An XMSS signature with its Merkle-path invariant enforced by the type. -/
abbrev Signature (p : Params) (prims : Primitives p) :=
  WotsSig p prims × AuthenticationPath prims.Y p.hp

/-- Generate the WOTS+ public key at leaf `index` using explicit `F` and `T_l` queries. -/
def leafM (prims : Primitives p) {m : Type → Type*} [Monad m]
    [HasQuery (publicHashSpec prims) m] (sk : prims.SkSeed) (pk : prims.PkSeed) (adrs : Adrs)
    (index : ℕ) : m prims.Y :=
  WotsOracle.wotsPkGenM prims sk pk (wotsLeafAdrs adrs index)

/-- Hash an XMSS internal node.  Both perfect-tree coordinates are embedded in the FIPS address. -/
def nodeHashM (prims : Primitives p) {m : Type → Type*} [HasQuery (publicHashSpec prims) m]
    (pk : prims.PkSeed) (adrs : Adrs) (address : Address) (left right : prims.Y) : m prims.Y :=
  PublicHash.h prims pk
    (((adrs.setTypeAndClear .tree).setTreeHeight address.height).setTreeIndex address.index)
    left right

/-- Compute an XMSS root without materializing its `2^(h'+1)-1`-node tree. -/
def rootM (prims : Primitives p) {m : Type → Type*} [Monad m]
    [HasQuery (publicHashSpec prims) m] (sk : prims.SkSeed) (pk : prims.PkSeed) (adrs : Adrs) :
    m prims.Y :=
  PerfectMerkleTree.rootM (leafM prims sk pk adrs) (nodeHashM prims pk adrs) p.hp

/-- XMSS signing with explicit public-hash calls and a statically sized authentication path. -/
def signM (prims : Primitives p) {m : Type → Type*} [Monad m]
    [HasQuery (publicHashSpec prims) m] (msg : prims.Y) (sk : prims.SkSeed) (pk : prims.PkSeed)
    (adrs : Adrs) (index : LeafIndex p.hp) : m (Signature p prims) := do
  let wots ← WotsOracle.wotsSignM prims msg sk pk (wotsLeafAdrs adrs index.val)
  let authenticationPath ←
    rootAuthenticationPathM (leafM prims sk pk adrs) (nodeHashM prims pk adrs) index
  pure (wots, authenticationPath)

/-- Recover the putative XMSS root from a typed signature. -/
def pkFromSigM (prims : Primitives p) {m : Type → Type*} [Monad m]
    [HasQuery (publicHashSpec prims) m] (index : LeafIndex p.hp) (sig : Signature p prims)
    (msg : prims.Y) (pk : prims.PkSeed) (adrs : Adrs) : m prims.Y := do
  let leaf ← WotsOracle.wotsPkFromSigM prims sig.1 msg pk (wotsLeafAdrs adrs index.val)
  reconstructRootM (nodeHashM prims pk adrs) index leaf sig.2

/-- Deterministic interpretation of one explicit XMSS node query is the original node hash. -/
@[simp]
theorem simulateQ_nodeHashM (prims : Primitives p) (pk : prims.PkSeed) (adrs : Adrs)
    (address : Address) (left right : prims.Y) :
    simulateQ (PublicHash.impl prims)
        (nodeHashM prims pk adrs address left right :
          OracleComp (publicHashSpec prims) prims.Y) =
      xmssNodeHash prims pk adrs address.height address.index left right := by
  simp [nodeHashM, xmssNodeHash]

end XmssOracle

end SLHDSA
