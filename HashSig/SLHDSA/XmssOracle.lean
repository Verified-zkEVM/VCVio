/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import HashSig.SLHDSA.WotsOracle
public import HashSig.SLHDSA.MerkleParity

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

/-! ## Deterministic typed semantics -/

/-- Erase only the authentication-path length proof, producing the legacy XMSS signature type. -/
def toLegacy {prims : Primitives p} (sig : Signature p prims) : XmssSig p prims :=
  (sig.1, sig.2.toList)

/-- Deterministic typed XMSS root computation. -/
def root (prims : Primitives p) (sk : prims.SkSeed) (pk : prims.PkSeed) (adrs : Adrs) :
    prims.Y :=
  PerfectMerkleTree.root (xmssLeaf prims sk pk adrs)
    (fun address => xmssNodeHash prims pk adrs address.height address.index) p.hp

/-- Deterministic XMSS signing with a statically sized authentication path. -/
def sign (prims : Primitives p) (msg : prims.Y) (sk : prims.SkSeed) (pk : prims.PkSeed)
    (adrs : Adrs) (index : LeafIndex p.hp) : Signature p prims :=
  (wotsSign prims msg sk pk (wotsLeafAdrs adrs index.val),
    rootAuthenticationPath (xmssLeaf prims sk pk adrs)
      (fun address => xmssNodeHash prims pk adrs address.height address.index) index)

/-- Deterministic root recovery from a typed XMSS signature. -/
def pkFromSig (prims : Primitives p) (index : LeafIndex p.hp) (sig : Signature p prims)
    (msg : prims.Y) (pk : prims.PkSeed) (adrs : Adrs) : prims.Y :=
  reconstructRoot (fun address => xmssNodeHash prims pk adrs address.height address.index)
    index (wotsPkFromSig prims sig.1 msg pk (wotsLeafAdrs adrs index.val)) sig.2

/-- The deterministic typed root is the legacy XMSS root. -/
@[simp]
theorem root_eq_xmssRoot (prims : Primitives p) (sk : prims.SkSeed) (pk : prims.PkSeed)
    (adrs : Adrs) :
    root prims sk pk adrs = xmssRoot prims sk pk adrs := by
  unfold root xmssRoot xmssNode PerfectMerkleTree.root
  exact Merkle.treeHash_eq_merkleRoot
    (xmssLeaf prims sk pk adrs) (xmssNodeHash prims pk adrs) p.hp 0

/-- Erasing a deterministic typed signature gives the legacy XMSS signature. -/
@[simp]
theorem toLegacy_sign (prims : Primitives p) (msg : prims.Y) (sk : prims.SkSeed)
    (pk : prims.PkSeed) (adrs : Adrs) (index : LeafIndex p.hp) :
    toLegacy (sign prims msg sk pk adrs index) =
      xmssSign prims msg sk pk adrs index.val := by
  unfold toLegacy sign xmssSign rootAuthenticationPath
  simp only [Prod.mk.injEq, true_and]
  exact Merkle.authenticationPath_toList_eq_authPath
    (xmssLeaf prims sk pk adrs) (xmssNodeHash prims pk adrs) p.hp 0 index.val

/-- Deterministic typed recovery agrees with legacy XMSS recovery after path erasure. -/
@[simp]
theorem pkFromSig_eq_xmssPkFromSig (prims : Primitives p) (index : LeafIndex p.hp)
    (sig : Signature p prims) (msg : prims.Y) (pk : prims.PkSeed) (adrs : Adrs) :
    pkFromSig prims index sig msg pk adrs =
      xmssPkFromSig prims index.val (toLegacy sig) msg pk adrs := by
  unfold pkFromSig xmssPkFromSig toLegacy reconstructRoot
  exact Merkle.climb_eq_climb (xmssNodeHash prims pk adrs) p.hp 0 index.val _ sig.2

/-- Honest deterministic typed XMSS signing and recovery reconstruct the legacy root. -/
theorem pkFromSig_sign (prims : Primitives p) (msg : prims.Y) (sk : prims.SkSeed)
    (pk : prims.PkSeed) (adrs : Adrs) (index : LeafIndex p.hp) :
    pkFromSig prims index (sign prims msg sk pk adrs index) msg pk adrs =
      xmssRoot prims sk pk adrs := by
  rw [pkFromSig_eq_xmssPkFromSig, toLegacy_sign]
  exact xmssPkFromSig_xmssSign prims msg sk pk adrs index.val index.isLt

/-! ## Deterministic-handler structure -/

/-- Interpreting an XMSS node query with any answer function gives the corresponding node hash
of the reinterpreted primitive bundle. -/
@[simp]
theorem simulateQ_nodeHashM_with (prims : Primitives p)
    (answer : QueryImpl (publicHashSpec prims) Id) (pk : prims.PkSeed) (adrs : Adrs)
    (address : Address) (left right : prims.Y) :
    simulateQ answer
        (nodeHashM prims pk adrs address left right :
          OracleComp (publicHashSpec prims) prims.Y) =
      xmssNodeHash (PublicHash.withPublicHash prims answer) pk adrs
        address.height address.index left right := by
  simp [nodeHashM, xmssNodeHash, PublicHash.h]

/-- Structural root parity for any fixed deterministic public-hash answer function. -/
theorem simulateQ_rootM_structural (prims : Primitives p)
    (answer : QueryImpl (publicHashSpec prims) Id) (sk : prims.SkSeed) (pk : prims.PkSeed)
    (adrs : Adrs) :
    simulateQ answer
        (rootM prims sk pk adrs : OracleComp (publicHashSpec prims) prims.Y) =
      PerfectMerkleTree.root
        (fun index => simulateQ answer
          (leafM prims sk pk adrs index : OracleComp (publicHashSpec prims) prims.Y))
        (fun address => xmssNodeHash (PublicHash.withPublicHash prims answer) pk adrs
          address.height address.index) p.hp := by
  simp [rootM, PerfectMerkleTree.simulateQ_rootM]

/-- Structural signing parity for any fixed deterministic public-hash answer function. -/
theorem simulateQ_signM_structural (prims : Primitives p)
    (answer : QueryImpl (publicHashSpec prims) Id) (msg : prims.Y) (sk : prims.SkSeed)
    (pk : prims.PkSeed) (adrs : Adrs) (index : LeafIndex p.hp) :
    simulateQ answer
        (signM prims msg sk pk adrs index :
          OracleComp (publicHashSpec prims) (Signature p prims)) =
      (simulateQ answer
          (WotsOracle.wotsSignM prims msg sk pk (wotsLeafAdrs adrs index.val) :
            OracleComp (publicHashSpec prims) (WotsSig p prims)),
        rootAuthenticationPath
          (fun i => simulateQ answer
            (leafM prims sk pk adrs i : OracleComp (publicHashSpec prims) prims.Y))
          (fun address => xmssNodeHash (PublicHash.withPublicHash prims answer) pk adrs
            address.height address.index) index) := by
  simp [signM, PerfectMerkleTree.simulateQ_rootAuthenticationPathM]
  rfl

/-- Structural recovery parity for any fixed deterministic public-hash answer function. -/
theorem simulateQ_pkFromSigM_structural (prims : Primitives p)
    (answer : QueryImpl (publicHashSpec prims) Id) (index : LeafIndex p.hp)
    (sig : Signature p prims) (msg : prims.Y) (pk : prims.PkSeed) (adrs : Adrs) :
    simulateQ answer
        (pkFromSigM prims index sig msg pk adrs :
          OracleComp (publicHashSpec prims) prims.Y) =
      reconstructRoot
        (fun address => xmssNodeHash (PublicHash.withPublicHash prims answer) pk adrs
          address.height address.index) index
        (simulateQ answer
          (WotsOracle.wotsPkFromSigM prims sig.1 msg pk (wotsLeafAdrs adrs index.val) :
            OracleComp (publicHashSpec prims) prims.Y)) sig.2 := by
  simp [pkFromSigM, PerfectMerkleTree.simulateQ_reconstructRootM]
  rfl

/-! ## Functional completeness -/

/-- Under any fixed deterministic public-hash answer function, the oracle leaf computation is
the legacy WOTS+ leaf for the induced functional primitive bundle. -/
@[simp]
theorem simulateQ_leafM_withPublicHash (prims : Primitives p)
    (answer : QueryImpl (publicHashSpec prims) Id) (sk : prims.SkSeed) (pk : prims.PkSeed)
    (adrs : Adrs) (index : ℕ) :
    simulateQ answer
        (leafM prims sk pk adrs index : OracleComp (publicHashSpec prims) prims.Y) =
      xmssLeaf (PublicHash.withPublicHash prims answer) sk pk adrs index := by
  exact WotsOracle.simulateQ_wotsPkGenM_withPublicHash prims answer sk pk
    (wotsLeafAdrs adrs index)

/-- XMSS root generation is functionally complete for every deterministic public-hash answer
function, expressed through the typed perfect-tree semantics. -/
theorem simulateQ_rootM_withPublicHash (prims : Primitives p)
    (answer : QueryImpl (publicHashSpec prims) Id) (sk : prims.SkSeed) (pk : prims.PkSeed)
    (adrs : Adrs) :
    simulateQ answer
        (rootM prims sk pk adrs : OracleComp (publicHashSpec prims) prims.Y) =
      root (PublicHash.withPublicHash prims answer) sk pk adrs := by
  rw [simulateQ_rootM_structural]
  simp only [root, simulateQ_leafM_withPublicHash]

/-- XMSS signing is functionally complete for every deterministic public-hash answer function. -/
theorem simulateQ_signM_withPublicHash (prims : Primitives p)
    (answer : QueryImpl (publicHashSpec prims) Id) (msg : prims.Y) (sk : prims.SkSeed)
    (pk : prims.PkSeed) (adrs : Adrs) (index : LeafIndex p.hp) :
    simulateQ answer
        (signM prims msg sk pk adrs index :
          OracleComp (publicHashSpec prims) (Signature p prims)) =
      sign (PublicHash.withPublicHash prims answer) msg sk pk adrs index := by
  rw [simulateQ_signM_structural,
    WotsOracle.simulateQ_wotsSignM_withPublicHash]
  simp only [sign, simulateQ_leafM_withPublicHash]

/-- XMSS root recovery is functionally complete for every deterministic public-hash answer
function. -/
theorem simulateQ_pkFromSigM_withPublicHash (prims : Primitives p)
    (answer : QueryImpl (publicHashSpec prims) Id) (index : LeafIndex p.hp)
    (sig : Signature p prims) (msg : prims.Y) (pk : prims.PkSeed) (adrs : Adrs) :
    simulateQ answer
        (pkFromSigM prims index sig msg pk adrs :
          OracleComp (publicHashSpec prims) prims.Y) =
      pkFromSig (PublicHash.withPublicHash prims answer) index sig msg pk adrs := by
  rw [simulateQ_pkFromSigM_structural,
    WotsOracle.simulateQ_wotsPkFromSigM_withPublicHash]
  rfl

/-- Honest XMSS signing and recovery remain complete after fixing any deterministic public-hash
answer function. -/
theorem simulateQ_pkFromSigM_signM_withPublicHash (prims : Primitives p)
    (answer : QueryImpl (publicHashSpec prims) Id) (msg : prims.Y) (sk : prims.SkSeed)
    (pk : prims.PkSeed) (adrs : Adrs) (index : LeafIndex p.hp) :
    simulateQ answer (do
      let sig ← (signM prims msg sk pk adrs index :
        OracleComp (publicHashSpec prims) (Signature p prims))
      pkFromSigM prims index sig msg pk adrs) =
      xmssRoot (PublicHash.withPublicHash prims answer) sk pk adrs := by
  simp only [simulateQ_bind]
  change simulateQ answer
    (pkFromSigM prims index
      (simulateQ answer
        (signM prims msg sk pk adrs index :
          OracleComp (publicHashSpec prims) (Signature p prims)))
      msg pk adrs) = _
  rw [simulateQ_signM_withPublicHash, simulateQ_pkFromSigM_withPublicHash]
  exact pkFromSig_sign (PublicHash.withPublicHash prims answer) msg sk pk adrs index

/-- Canonical deterministic-handler parity for XMSS roots. -/
@[simp]
theorem simulateQ_rootM (prims : Primitives p) (sk : prims.SkSeed) (pk : prims.PkSeed)
    (adrs : Adrs) :
    simulateQ (PublicHash.impl prims)
        (rootM prims sk pk adrs : OracleComp (publicHashSpec prims) prims.Y) =
      root prims sk pk adrs := by
  convert simulateQ_rootM_withPublicHash prims (PublicHash.impl prims) sk pk adrs using 1
  all_goals rfl

/-- Canonical deterministic-handler parity for XMSS signing. -/
@[simp]
theorem simulateQ_signM (prims : Primitives p) (msg : prims.Y) (sk : prims.SkSeed)
    (pk : prims.PkSeed) (adrs : Adrs) (index : LeafIndex p.hp) :
    simulateQ (PublicHash.impl prims)
        (signM prims msg sk pk adrs index :
          OracleComp (publicHashSpec prims) (Signature p prims)) =
      sign prims msg sk pk adrs index := by
  convert simulateQ_signM_withPublicHash prims (PublicHash.impl prims) msg sk pk adrs index using 1
  all_goals rfl

/-- Canonical deterministic-handler parity for XMSS root recovery. -/
@[simp]
theorem simulateQ_pkFromSigM (prims : Primitives p) (index : LeafIndex p.hp)
    (sig : Signature p prims) (msg : prims.Y) (pk : prims.PkSeed) (adrs : Adrs) :
    simulateQ (PublicHash.impl prims)
        (pkFromSigM prims index sig msg pk adrs :
          OracleComp (publicHashSpec prims) prims.Y) =
      pkFromSig prims index sig msg pk adrs := by
  convert simulateQ_pkFromSigM_withPublicHash prims (PublicHash.impl prims) index sig msg pk adrs
    using 1
  all_goals rfl

/-- Canonical honest signing/recovery equality for XMSS. -/
theorem simulateQ_pkFromSigM_signM (prims : Primitives p) (msg : prims.Y)
    (sk : prims.SkSeed) (pk : prims.PkSeed) (adrs : Adrs) (index : LeafIndex p.hp) :
    simulateQ (PublicHash.impl prims) (do
      let sig ← (signM prims msg sk pk adrs index :
        OracleComp (publicHashSpec prims) (Signature p prims))
      pkFromSigM prims index sig msg pk adrs) = xmssRoot prims sk pk adrs := by
  convert simulateQ_pkFromSigM_signM_withPublicHash prims (PublicHash.impl prims) msg sk pk adrs
    index using 1
  all_goals rfl

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
