/-
Copyright (c) 2026 VCVio Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Richard Goodman
-/

import VCVio.CryptoFoundations.MerkleTree.Inductive.Binding
import VCVio.CryptoFoundations.TweakableHash

/-! # Node-Addressed Merkle Trees: the one engine

Merkle trees whose node hash may depend on the **full address** of the node being
hashed — the typed root-path position `NodeAddress s` — via
`nodeHash : NodeAddress s → α → α → α`.

This is the single engine of which the ordinary tree (constant `nodeHash`), the
level-separated tree (`nodeHash` through the depth of the addressed subtree), and
XMSS/SLH-DSA-style fully-addressed trees (`nodeHash` through an arbitrary
address-to-tweak map) are instances: tree building, putative-root recomputation,
completeness, and constructive collision tracing are defined and proven **once**,
and every instance inherits them by specializing `nodeHash`.

Design: at each recursion step into a child, the engine passes the *reindexed* hash
`fun a => nodeHash (.inL a)` (resp. `.inR`) — the address is threaded by
precomposition, so no explicit path accumulator or embedding parameter appears.

Contents:

* `NodeAddress` — typed addresses of **internal** nodes (only internal nodes hash);
  `NodeAddress.subtreeDepth` recovers the height of the addressed subtree (the
  level-separation data), and the full constructor path is the XMSS address.
* `populateUpAddressed` / `buildMerkleTreeAddressedWithHash` — cache construction.
* `getPutativeRootAddressedWithHash` — putative-root recomputation from a leaf, an
  authentication path (`generateProof` is reused unchanged — proofs carry no
  addresses), and a leaf index.
* `addressed_functional_completeness` — honest paths verify, for **every** `nodeHash`.
* `AddressedCollision`, `findCollisionAddressed`, `findCollisionAddressed_sound` —
  the constructive collision kernel, returning the collision **as data, tagged with
  the address** at which it occurs: two distinct pairs with equal hash *under that
  address's hash function*.
* `getPutativeRootAddressedWithHash_binding_collision` — the user-facing binding
  statement: distinct leaf values verifying to the same root at the same index yield
  an address-tagged collision.

The symmetric collision statement here is deliberately **not** phrased as a
target-collision-resistance win: TCR is directional (one endpoint fixed at
target-registration time). The oriented reduction against a sampled-target game is
the follow-up consumer of the address tag.
-/

namespace AddressedMerkleTree

open List OracleSpec OracleComp BinaryTree InductiveMerkleTree

variable {α : Type _} [DecidableEq α]

/-- A typed address of an **internal** node of a skeleton: the path from the root.
Leaf skeletons have no addresses — only internal nodes hash. -/
inductive NodeAddress : Skeleton → Type
  /-- The root of an internal skeleton. -/
  | here {l r : Skeleton} : NodeAddress (.internal l r)
  /-- An address inside the left child. -/
  | inL {l r : Skeleton} (a : NodeAddress l) : NodeAddress (.internal l r)
  /-- An address inside the right child. -/
  | inR {l r : Skeleton} (a : NodeAddress r) : NodeAddress (.internal l r)
  deriving DecidableEq

namespace NodeAddress

/-- Distance of the addressed node from the root. -/
@[simp]
def pathDepth : {s : Skeleton} → NodeAddress s → ℕ
  | _, .here => 0
  | _, .inL a => a.pathDepth + 1
  | _, .inR a => a.pathDepth + 1

/-- The height (`Skeleton.depth`) of the subtree rooted at the addressed node.
This is the datum a *level-separated* hash depends on. -/
@[simp]
def subtreeDepth : {s : Skeleton} → NodeAddress s → ℕ
  | .internal l r, .here => (Skeleton.internal l r).depth
  | _, .inL a => a.subtreeDepth
  | _, .inR a => a.subtreeDepth

end NodeAddress

/-- Build the full cache of a Merkle tree under an address-dependent hash: each
internal node stores `nodeHash addr leftRoot rightRoot` where `addr` is that node's
address. The address is threaded by reindexing `nodeHash` along `.inL` / `.inR`. -/
@[simp, grind]
def populateUpAddressed : {s : Skeleton} → (nodeHash : NodeAddress s → α → α → α) →
    LeafData α s → FullData α s
  | .leaf, _, .leaf v => .leaf v
  | .internal _ _, nh, .internal dl dr =>
    let L := populateUpAddressed (fun a => nh (.inL a)) dl
    let R := populateUpAddressed (fun a => nh (.inR a)) dr
    .internal (nh .here L.getRootValue R.getRootValue) L R

/-- Alias matching the naming of the unaddressed engine. -/
@[simp, grind]
def buildMerkleTreeAddressedWithHash {s : Skeleton} (leaf_tree : LeafData α s)
    (nodeHash : NodeAddress s → α → α → α) : FullData α s :=
  populateUpAddressed nodeHash leaf_tree

/-- Recompute the putative root from a leaf value, its index, and an authentication
path, hashing each step under the address of the node being reconstituted. The
node reconstituted by the *last* step is the root (`.here`); descending into the
index reindexes the hash along the path. -/
@[simp, grind]
def getPutativeRootAddressedWithHash :
    {s : Skeleton} → (nodeHash : NodeAddress s → α → α → α) →
      (idx : SkeletonLeafIndex s) → (leafValue : α) → List.Vector α idx.depth → α
  | _, _, .ofLeaf, leafValue, _ => leafValue
  | _, nh, .ofLeft idxLeft, leafValue, proof =>
    nh .here (getPutativeRootAddressedWithHash (fun a => nh (.inL a)) idxLeft
      leafValue proof.tail) proof.head
  | _, nh, .ofRight idxRight, leafValue, proof =>
    nh .here proof.head (getPutativeRootAddressedWithHash (fun a => nh (.inR a)) idxRight
      leafValue proof.tail)

/-- **Completeness of the engine**: an honestly generated authentication path
recomputes the honest root, for every address-dependent hash. -/
theorem addressed_functional_completeness {s : Skeleton}
    (idx : SkeletonLeafIndex s) (leaf_data_tree : LeafData α s)
    (nodeHash : NodeAddress s → α → α → α) :
    getPutativeRootAddressedWithHash nodeHash idx (leaf_data_tree.get idx)
      (generateProof (buildMerkleTreeAddressedWithHash leaf_data_tree nodeHash) idx)
    = (buildMerkleTreeAddressedWithHash leaf_data_tree nodeHash).getRootValue := by
  induction idx with
  | ofLeaf => cases leaf_data_tree; rfl
  | ofLeft idxLeft ih =>
    cases leaf_data_tree with
    | internal dl dr =>
      simp only [buildMerkleTreeAddressedWithHash, populateUpAddressed,
        getPutativeRootAddressedWithHash, InductiveMerkleTree.generateProof,
        List.Vector.tail_cons, List.Vector.head_cons, BinaryTree.LeafData.get,
        BinaryTree.FullData.getRootValue]
      exact congrArg (fun z => nodeHash .here z _) (ih dl (fun a => nodeHash (.inL a)))
  | ofRight idxRight ih =>
    cases leaf_data_tree with
    | internal dl dr =>
      simp only [buildMerkleTreeAddressedWithHash, populateUpAddressed,
        getPutativeRootAddressedWithHash, InductiveMerkleTree.generateProof,
        List.Vector.tail_cons, List.Vector.head_cons, BinaryTree.LeafData.get,
        BinaryTree.FullData.getRootValue]
      exact congrArg (nodeHash .here _) (ih dr (fun a => nodeHash (.inR a)))

/-- An address-tagged collision: two *distinct* input pairs with equal digest under
the hash **at that address**. -/
def AddressedCollision {s : Skeleton} (nodeHash : NodeAddress s → α → α → α)
    (w : NodeAddress s × α × α × α × α) : Prop :=
  (w.2.1, w.2.2.1) ≠ (w.2.2.2.1, w.2.2.2.2) ∧
    nodeHash w.1 w.2.1 w.2.2.1 = nodeHash w.1 w.2.2.2.1 w.2.2.2.2

/-- Walk two verifying branches at the same leaf index looking for the level at
which they merge; return the collision **as data, tagged with its address**. -/
def findCollisionAddressed : {s : Skeleton} → (nodeHash : NodeAddress s → α → α → α) →
    (idx : SkeletonLeafIndex s) → (proof₁ proof₂ : List.Vector α idx.depth) →
    (x y : α) → Option (NodeAddress s × α × α × α × α)
  | _, _, .ofLeaf, _, _, _, _ => none
  | _, nh, .ofLeft idxLeft, proof₁, proof₂, x, y =>
    let subL1 := getPutativeRootAddressedWithHash (fun a => nh (.inL a)) idxLeft x proof₁.tail
    let subL2 := getPutativeRootAddressedWithHash (fun a => nh (.inL a)) idxLeft y proof₂.tail
    if (subL1, proof₁.head) = (subL2, proof₂.head) then
      (findCollisionAddressed (fun a => nh (.inL a)) idxLeft proof₁.tail proof₂.tail x y).map
        (fun w => (.inL w.1, w.2))
    else if nh .here subL1 proof₁.head = nh .here subL2 proof₂.head then
      some (.here, subL1, proof₁.head, subL2, proof₂.head)
    else
      none
  | _, nh, .ofRight idxRight, proof₁, proof₂, x, y =>
    let subR1 := getPutativeRootAddressedWithHash (fun a => nh (.inR a)) idxRight x proof₁.tail
    let subR2 := getPutativeRootAddressedWithHash (fun a => nh (.inR a)) idxRight y proof₂.tail
    if (proof₁.head, subR1) = (proof₂.head, subR2) then
      (findCollisionAddressed (fun a => nh (.inR a)) idxRight proof₁.tail proof₂.tail x y).map
        (fun w => (.inR w.1, w.2))
    else if nh .here proof₁.head subR1 = nh .here proof₂.head subR2 then
      some (.here, proof₁.head, subR1, proof₂.head, subR2)
    else
      none

/-- **Soundness of the kernel**: anything returned is an address-tagged collision. -/
theorem findCollisionAddressed_sound {s : Skeleton}
    (nodeHash : NodeAddress s → α → α → α) (idx : SkeletonLeafIndex s)
    (proof₁ proof₂ : List.Vector α idx.depth) (x y : α)
    (w : NodeAddress s × α × α × α × α)
    (hw : findCollisionAddressed nodeHash idx proof₁ proof₂ x y = some w) :
    AddressedCollision nodeHash w := by
  induction idx with
  | ofLeaf => simp [findCollisionAddressed] at hw
  | ofLeft idxLeft ih =>
    rw [findCollisionAddressed] at hw
    split at hw
    · simp only [Option.map_eq_some_iff] at hw
      obtain ⟨w', hw', rfl⟩ := hw
      exact ih (fun a => nodeHash (.inL a)) proof₁.tail proof₂.tail w' hw'
    · rename_i hneq
      split at hw
      · rename_i heq
        simp only [Option.some.injEq] at hw
        subst hw
        exact ⟨hneq, heq⟩
      · simp at hw
  | ofRight idxRight ih =>
    rw [findCollisionAddressed] at hw
    split at hw
    · simp only [Option.map_eq_some_iff] at hw
      obtain ⟨w', hw', rfl⟩ := hw
      exact ih (fun a => nodeHash (.inR a)) proof₁.tail proof₂.tail w' hw'
    · rename_i hneq
      split at hw
      · rename_i heq
        simp only [Option.some.injEq] at hw
        subst hw
        exact ⟨hneq, heq⟩
      · simp at hw

/-- If two openings at the same index recompute the same root but the branches differ
somewhere (in leaf value or path), `findCollisionAddressed` finds a collision: the
walk only returns `none` when the two branches agree at every compared level, which
forces the leaf values to agree. -/
theorem findCollisionAddressed_isSome {s : Skeleton}
    (nodeHash : NodeAddress s → α → α → α) (idx : SkeletonLeafIndex s)
    (proof₁ proof₂ : List.Vector α idx.depth) (x y : α)
    (hroot : getPutativeRootAddressedWithHash nodeHash idx x proof₁
      = getPutativeRootAddressedWithHash nodeHash idx y proof₂)
    (hne : x ≠ y) :
    (findCollisionAddressed nodeHash idx proof₁ proof₂ x y).isSome := by
  induction idx with
  | ofLeaf => simp [getPutativeRootAddressedWithHash] at hroot; exact absurd hroot hne
  | ofLeft idxLeft ih =>
    rw [findCollisionAddressed]
    split
    · rename_i hagree
      simp only [Prod.mk.injEq] at hagree
      simp only [Option.isSome_map]
      exact ih (fun a => nodeHash (.inL a)) proof₁.tail proof₂.tail hagree.1
    · split
      · simp
      · rename_i hne'
        exact absurd (by simpa [getPutativeRootAddressedWithHash] using hroot) hne'
  | ofRight idxRight ih =>
    rw [findCollisionAddressed]
    split
    · rename_i hagree
      simp only [Prod.mk.injEq] at hagree
      simp only [Option.isSome_map]
      exact ih (fun a => nodeHash (.inR a)) proof₁.tail proof₂.tail hagree.2
    · split
      · simp
      · rename_i hne'
        exact absurd (by simpa [getPutativeRootAddressedWithHash] using hroot) hne'

/-- **Binding, user-facing**: two openings of the same index recomputing the same
root with distinct leaf values yield an address-tagged collision, as data. -/
theorem getPutativeRootAddressedWithHash_binding_collision {s : Skeleton}
    (nodeHash : NodeAddress s → α → α → α) (idx : SkeletonLeafIndex s)
    (proof₁ proof₂ : List.Vector α idx.depth) (x y : α)
    (hroot : getPutativeRootAddressedWithHash nodeHash idx x proof₁
      = getPutativeRootAddressedWithHash nodeHash idx y proof₂)
    (hne : x ≠ y) :
    ∃ w, findCollisionAddressed nodeHash idx proof₁ proof₂ x y = some w ∧
      AddressedCollision nodeHash w := by
  obtain ⟨w, hw⟩ := Option.isSome_iff_exists.mp
    (findCollisionAddressed_isSome nodeHash idx proof₁ proof₂ x y hroot hne)
  exact ⟨w, hw, findCollisionAddressed_sound nodeHash idx proof₁ proof₂ x y w hw⟩

/-! ## Instances: one engine, three trees

The three hash disciplines are specializations of `nodeHash`; the theorems above
specialize with them. The recovery theorems below are the dedup certificates: the
unaddressed engine's core functions are *definitionally subsumed* (constant
instance), and the level-separated (`Tweaked`) development factors through
`NodeAddress.subtreeDepth`. -/

section Instances

/-- **Ordinary instance**: a constant `nodeHash` recovers the unaddressed
putative-root computation. -/
theorem getPutativeRootAddressed_const (h : α → α → α) {s : Skeleton}
    (idx : SkeletonLeafIndex s) (x : α) (proof : List.Vector α idx.depth) :
    getPutativeRootAddressedWithHash (s := s) (fun _ => h) idx x proof
      = InductiveMerkleTree.getPutativeRootWithHash idx x proof h := by
  induction idx with
  | ofLeaf => rfl
  | ofLeft idxLeft ih => simp [getPutativeRootAddressedWithHash, ih]
  | ofRight idxRight ih => simp [getPutativeRootAddressedWithHash, ih]

/-- **Ordinary instance**: a constant `nodeHash` recovers the unaddressed cache
construction. -/
theorem populateUpAddressed_const (h : α → α → α) {s : Skeleton}
    (ld : LeafData α s) :
    populateUpAddressed (fun _ => h) ld = BinaryTree.populateUp ld h := by
  induction ld with
  | leaf v => rfl
  | internal dl dr ihl ihr => simp [populateUpAddressed, BinaryTree.populateUp, ihl, ihr]

/-- **Level-separated instance**: hash through the depth of the addressed subtree.
This is the discipline of the `Tweaked` development: per-level domain separation. -/
def levelNodeHash {PkSeed Tweak Y : Type} (th : TweakableHash PkSeed Tweak (Y × Y) Y)
    (pk : PkSeed) (tweakAt : ℕ → Tweak) {s : Skeleton} : NodeAddress s → Y → Y → Y :=
  fun a l r => th.eval pk (tweakAt a.subtreeDepth) (l, r)

/-- **Fully-addressed (XMSS-style) instance**: hash through an arbitrary map out of
the full typed address — per-node domain separation. Any concrete addressing scheme
(layer, horizontal index, domain tag) factors through `tweakOf`; nothing about the
address is discarded before the user's map is applied. -/
def addressedNodeHash {PkSeed Tweak Y : Type} (th : TweakableHash PkSeed Tweak (Y × Y) Y)
    (pk : PkSeed) {s : Skeleton} (tweakOf : NodeAddress s → Tweak) :
    NodeAddress s → Y → Y → Y :=
  fun a l r => th.eval pk (tweakOf a) (l, r)

/-- The level instance factors through the fully-addressed one — level separation is
the special case `tweakOf = tweakAt ∘ subtreeDepth`. -/
theorem levelNodeHash_eq_addressed {PkSeed Tweak Y : Type}
    (th : TweakableHash PkSeed Tweak (Y × Y) Y) (pk : PkSeed) (tweakAt : ℕ → Tweak)
    {s : Skeleton} :
    levelNodeHash th pk tweakAt (s := s)
      = addressedNodeHash th pk (fun a => tweakAt a.subtreeDepth) := rfl

end Instances

end AddressedMerkleTree
