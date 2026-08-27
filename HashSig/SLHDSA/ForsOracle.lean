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

/-! ## Deterministic typed semantics -/

/-- Erase the authentication-path length proofs from a typed FORS signature. -/
def toLegacy {prims : Primitives p} (sig : Signature p prims) : ForsSig p prims :=
  sig.map fun entry => (entry.1, entry.2.toList)

/-- Deterministic typed computation of one FORS tree root. -/
def root (prims : Primitives p) (sk : prims.SkSeed) (pk : prims.PkSeed) (adrs : Adrs)
    (tree : Fin p.k) : prims.Y :=
  treeHash (forsLeaf prims sk pk adrs)
    (fun address => forsNodeHash prims pk adrs address.height address.index) p.a tree.val

/-- Deterministic FORS public-key generation through the typed perfect-tree engine. -/
def pkGen (prims : Primitives p) (sk : prims.SkSeed) (pk : prims.PkSeed) (adrs : Adrs) :
    prims.Y :=
  prims.Tl pk (forsPkAdrs adrs) ((List.finRange p.k).map fun tree =>
    root prims sk pk adrs tree)

/-- Deterministic FORS signing with exactly `a` siblings in every authentication path. -/
def sign (prims : Primitives p) (md : List Byte) (sk : prims.SkSeed) (pk : prims.PkSeed)
    (adrs : Adrs) : Signature p prims :=
  Vector.ofFn fun tree : Fin p.k =>
    let index := tree.val * 2 ^ p.a + forsIdx p md tree.val
    (forsSkGen prims sk pk adrs index,
      authenticationPath (forsLeaf prims sk pk adrs) (fun address =>
        forsNodeHash prims pk adrs address.height address.index) 0 index p.a)

/-- Deterministic FORS public-key recovery from a typed signature. -/
def pkFromSig (prims : Primitives p) (sig : Signature p prims) (md : List Byte)
    (pk : prims.PkSeed) (adrs : Adrs) : prims.Y :=
  prims.Tl pk (forsPkAdrs adrs) ((List.finRange p.k).map fun tree =>
    let index := tree.val * 2 ^ p.a + forsIdx p md tree.val
    climb (fun address => forsNodeHash prims pk adrs address.height address.index)
      0 index p.a (prims.F pk (forsNodeAdrs adrs 0 index) (sig[tree.val]).1)
      (sig[tree.val]).2)

/-- The deterministic typed tree root is the legacy FORS root. -/
@[simp]
theorem root_eq_forsRoot (prims : Primitives p) (sk : prims.SkSeed) (pk : prims.PkSeed)
    (adrs : Adrs) (tree : Fin p.k) :
    root prims sk pk adrs tree = forsRoot prims sk pk adrs tree.val := by
  unfold root forsRoot
  exact Merkle.treeHash_eq_merkleRoot
    (forsLeaf prims sk pk adrs) (forsNodeHash prims pk adrs) p.a tree.val

/-- Typed deterministic FORS public-key generation agrees with the legacy definition. -/
@[simp]
theorem pkGen_eq_forsPkGen (prims : Primitives p) (sk : prims.SkSeed) (pk : prims.PkSeed)
    (adrs : Adrs) :
    pkGen prims sk pk adrs = forsPkGen prims sk pk adrs := by
  unfold pkGen forsPkGen
  refine congrArg (prims.Tl pk (forsPkAdrs adrs)) (List.map_congr_left fun tree _ => ?_)
  exact root_eq_forsRoot prims sk pk adrs tree

/-- Erasing a deterministic typed signature gives the legacy FORS signature. -/
@[simp]
theorem toLegacy_sign (prims : Primitives p) (md : List Byte) (sk : prims.SkSeed)
    (pk : prims.PkSeed) (adrs : Adrs) :
    toLegacy (sign prims md sk pk adrs) = forsSign prims md sk pk adrs := by
  apply Vector.ext
  intro tree htree
  simp only [toLegacy, sign, forsSign, Vector.getElem_map, Vector.getElem_ofFn]
  apply Prod.ext
  · rfl
  · exact Merkle.authenticationPath_toList_eq_authPath
      (forsLeaf prims sk pk adrs) (forsNodeHash prims pk adrs) p.a 0
      (tree * 2 ^ p.a + forsIdx p md tree)

/-- Typed deterministic FORS recovery agrees with legacy recovery after erasure. -/
@[simp]
theorem pkFromSig_eq_forsPkFromSig (prims : Primitives p) (sig : Signature p prims)
    (md : List Byte) (pk : prims.PkSeed) (adrs : Adrs) :
    pkFromSig prims sig md pk adrs = forsPkFromSig prims (toLegacy sig) md pk adrs := by
  unfold pkFromSig forsPkFromSig
  refine congrArg (prims.Tl pk (forsPkAdrs adrs)) (List.map_congr_left fun tree _ => ?_)
  simp only [toLegacy, Vector.getElem_map]
  exact Merkle.climb_eq_climb (forsNodeHash prims pk adrs) p.a 0
    (tree.val * 2 ^ p.a + forsIdx p md tree.val) _ (sig[tree.val]).2

/-- Honest deterministic typed FORS signing and recovery reconstruct the legacy public key. -/
theorem pkFromSig_sign (prims : Primitives p) (md : List Byte) (sk : prims.SkSeed)
    (pk : prims.PkSeed) (adrs : Adrs) :
    pkFromSig prims (sign prims md sk pk adrs) md pk adrs =
      forsPkGen prims sk pk adrs := by
  rw [pkFromSig_eq_forsPkFromSig, toLegacy_sign]
  exact forsPkFromSig_forsSign prims md sk pk adrs

/-! ## Deterministic-handler structure -/

@[simp]
theorem simulateQ_leafM_with (prims : Primitives p)
    (answer : QueryImpl (publicHashSpec prims) Id) (sk : prims.SkSeed) (pk : prims.PkSeed)
    (adrs : Adrs) (index : ℕ) :
    simulateQ answer
        (leafM prims sk pk adrs index : OracleComp (publicHashSpec prims) prims.Y) =
      forsLeaf (PublicHash.withPublicHash prims answer) sk pk adrs index := by
  simp [leafM, forsLeaf, forsSkGen, PublicHash.f, PublicHash.withPublicHash]

@[simp]
theorem simulateQ_nodeHashM_with (prims : Primitives p)
    (answer : QueryImpl (publicHashSpec prims) Id) (pk : prims.PkSeed) (adrs : Adrs)
    (address : Address) (left right : prims.Y) :
    simulateQ answer
        (nodeHashM prims pk adrs address left right :
          OracleComp (publicHashSpec prims) prims.Y) =
      forsNodeHash (PublicHash.withPublicHash prims answer) pk adrs
        address.height address.index left right := by
  simp [nodeHashM, forsNodeHash, PublicHash.h]

/-- One FORS root interpreted by any fixed answer function is the legacy root for the
reinterpreted primitive bundle. -/
theorem simulateQ_rootM_with (prims : Primitives p)
    (answer : QueryImpl (publicHashSpec prims) Id) (sk : prims.SkSeed) (pk : prims.PkSeed)
    (adrs : Adrs) (tree : Fin p.k) :
    simulateQ answer
        (rootM prims sk pk adrs tree : OracleComp (publicHashSpec prims) prims.Y) =
      forsRoot (PublicHash.withPublicHash prims answer) sk pk adrs tree.val := by
  unfold rootM forsRoot
  rw [PerfectMerkleTree.simulateQ_treeHashM]
  simp_rw [simulateQ_leafM_with, simulateQ_nodeHashM_with]
  exact Merkle.treeHash_eq_merkleRoot
    (forsLeaf (PublicHash.withPublicHash prims answer) sk pk adrs)
    (forsNodeHash (PublicHash.withPublicHash prims answer) pk adrs) p.a tree.val

private theorem indices_map_toList {n : ℕ} {α : Type} (f : Fin n → α) :
    ((WotsOracle.indices n).map f).toList = (List.finRange n).map f := by
  simpa [WotsOracle.indices, List.finRange, Function.comp_def] using
    (Vector.toList_ofFn (f := f))

/-- FORS public-key generation interpreted by any fixed answer function is legacy public-key
generation for the reinterpreted primitive bundle. -/
theorem simulateQ_pkGenM_with (prims : Primitives p)
    (answer : QueryImpl (publicHashSpec prims) Id) (sk : prims.SkSeed) (pk : prims.PkSeed)
    (adrs : Adrs) :
    simulateQ answer
        (pkGenM prims sk pk adrs : OracleComp (publicHashSpec prims) prims.Y) =
      forsPkGen (PublicHash.withPublicHash prims answer) sk pk adrs := by
  unfold pkGenM forsPkGen
  simp only [simulateQ_bind, PerfectMerkleTree.simulateQ_vector_mapM]
  simp_rw [simulateQ_rootM_with]
  change answer (.tl pk (forsPkAdrs adrs)
      (((WotsOracle.indices p.k).map fun tree =>
        forsRoot (PublicHash.withPublicHash prims answer) sk pk adrs tree.val).toList)) =
    answer (.tl pk (forsPkAdrs adrs)
      ((List.finRange p.k).map fun tree =>
        forsRoot (PublicHash.withPublicHash prims answer) sk pk adrs tree.val))
  congr 2
  exact indices_map_toList fun tree =>
    forsRoot (PublicHash.withPublicHash prims answer) sk pk adrs tree.val

/-- FORS signing interpreted by any fixed answer function is deterministic typed signing for the
reinterpreted primitive bundle. -/
theorem simulateQ_signM_with (prims : Primitives p)
    (answer : QueryImpl (publicHashSpec prims) Id) (md : List Byte) (sk : prims.SkSeed)
    (pk : prims.PkSeed) (adrs : Adrs) :
    simulateQ answer
        (signM prims md sk pk adrs : OracleComp (publicHashSpec prims) (Signature p prims)) =
      sign (PublicHash.withPublicHash prims answer) md sk pk adrs := by
  simp [signM, sign, PerfectMerkleTree.simulateQ_vector_mapM,
    PerfectMerkleTree.simulateQ_authenticationPathM, simulateQ_leafM_with,
    simulateQ_nodeHashM_with, WotsOracle.indices, PublicHash.withPublicHash]
  rfl

/-- FORS recovery interpreted by any fixed answer function is deterministic typed recovery for
the reinterpreted primitive bundle. -/
theorem simulateQ_pkFromSigM_with (prims : Primitives p)
    (answer : QueryImpl (publicHashSpec prims) Id) (sig : Signature p prims) (md : List Byte)
    (pk : prims.PkSeed) (adrs : Adrs) :
    simulateQ answer
        (pkFromSigM prims sig md pk adrs : OracleComp (publicHashSpec prims) prims.Y) =
      pkFromSig (PublicHash.withPublicHash prims answer) sig md pk adrs := by
  have hbody (tree : Fin p.k) :
      simulateQ answer (do
        let index := tree.val * 2 ^ p.a + forsIdx p md tree.val
        let leaf ← PublicHash.f prims pk (forsNodeAdrs adrs 0 index) (sig[tree.val]).1
        climbM (nodeHashM prims pk adrs) 0 index p.a leaf (sig[tree.val]).2) =
      let index := tree.val * 2 ^ p.a + forsIdx p md tree.val
      climb (fun address =>
        forsNodeHash (PublicHash.withPublicHash prims answer) pk adrs
          address.height address.index) 0 index p.a
        (answer (.f pk (forsNodeAdrs adrs 0 index) (sig[tree.val]).1)) (sig[tree.val]).2 := by
    simp [PerfectMerkleTree.simulateQ_climbM, simulateQ_nodeHashM_with, PublicHash.f]
    rfl
  unfold pkFromSigM pkFromSig
  rw [simulateQ_bind, PerfectMerkleTree.simulateQ_vector_mapM]
  simp_rw [hbody]
  change answer (.tl pk (forsPkAdrs adrs)
      (((WotsOracle.indices p.k).map fun tree =>
        let index := tree.val * 2 ^ p.a + forsIdx p md tree.val
        climb (fun address =>
          forsNodeHash (PublicHash.withPublicHash prims answer) pk adrs
            address.height address.index) 0 index p.a
          (answer (.f pk (forsNodeAdrs adrs 0 index) (sig[tree.val]).1))
          (sig[tree.val]).2).toList)) =
    answer (.tl pk (forsPkAdrs adrs)
      ((List.finRange p.k).map fun tree =>
        let index := tree.val * 2 ^ p.a + forsIdx p md tree.val
        climb (fun address =>
          forsNodeHash (PublicHash.withPublicHash prims answer) pk adrs
            address.height address.index) 0 index p.a
          (answer (.f pk (forsNodeAdrs adrs 0 index) (sig[tree.val]).1))
          (sig[tree.val]).2))
  congr 2
  exact indices_map_toList fun tree =>
    let index := tree.val * 2 ^ p.a + forsIdx p md tree.val
    climb (fun address =>
      forsNodeHash (PublicHash.withPublicHash prims answer) pk adrs
        address.height address.index) 0 index p.a
      (answer (.f pk (forsNodeAdrs adrs 0 index) (sig[tree.val]).1)) (sig[tree.val]).2

/-- Honest FORS signing and recovery are functionally complete after fixing any deterministic
public-hash answer function. -/
theorem simulateQ_pkFromSigM_signM_with (prims : Primitives p)
    (answer : QueryImpl (publicHashSpec prims) Id) (md : List Byte) (sk : prims.SkSeed)
    (pk : prims.PkSeed) (adrs : Adrs) :
    simulateQ answer (do
      let sig ← (signM prims md sk pk adrs :
        OracleComp (publicHashSpec prims) (Signature p prims))
      pkFromSigM prims sig md pk adrs) =
      forsPkGen (PublicHash.withPublicHash prims answer) sk pk adrs := by
  simp only [simulateQ_bind]
  change simulateQ answer
    (pkFromSigM prims
      (simulateQ answer
        (signM prims md sk pk adrs : OracleComp (publicHashSpec prims) (Signature p prims)))
      md pk adrs) = _
  rw [simulateQ_signM_with, simulateQ_pkFromSigM_with]
  exact pkFromSig_sign (PublicHash.withPublicHash prims answer) md sk pk adrs

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
