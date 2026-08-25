/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/

module
public import VCVio.CryptoFoundations.MerkleTree.Addressed.Basic
public import ToMathlib.Data.IndexedBinaryTree.Perfect
public import ToMathlib.Data.IndexedBinaryTree.Equiv

/-!
# Perfect Merkle trees with heap-style natural-number addressing

The node-addressed Merkle engine (`AddressedMerkleTree`) specialised to **perfect** binary
trees whose nodes are addressed by `(height, horizontal index)` pairs of natural numbers, as in
XMSS and the FORS trees of SLH-DSA (FIPS 205 §6, §8). A leaf-value function `leaf : ℕ → Y` and a
position-indexed node hash `nodeHash height index left right` determine, for every height `z` and
horizontal index `t`, the subtree whose leaves are
`leaf (t * 2 ^ z), …, leaf (t * 2 ^ z + 2 ^ z - 1)`
and whose internal node at `(h, i)` is `nodeHash h i (left child) (right child)`.

* `tree leaf nodeHash z t` — the fully populated subtree at `(z, t)`, as
  `AddressedMerkleTree.buildMerkleTreeAddressedWithHash` over `Skeleton.perfect z`.
* `merkleRoot leaf nodeHash z t` — its root, satisfying the FIPS 205 Algorithm 9 / 15 recursion
  (`merkleRoot_zero`, `merkleRoot_succ`).
* `authPath leaf nodeHash idx z` — the authentication path of leaf `idx` over `z` levels, listed
  from the leaf level upwards (the FIPS 205 order); the reversal of the engine's
  `InductiveMerkleTree.generateProof`.
* `climb nodeHash idx node auth` — root recovery from a leaf value and an authentication path
  (Algorithms 11 / 17); the engine's `getPutativeRootAddressedWithHash`.
* `climb_authPath` — completeness, from `addressed_functional_completeness`.
* `climb_binding` — oriented binding, from `addressed_oriented_binding`: an adversarial opening
  that verifies against the honest root with a different leaf value yields, at some internal
  address `(h, i)`, a collision of `nodeHash h i` whose first endpoint is the honestly computed
  child pair at that address. This is the shape consumed by a multi-target target-collision
  reduction on the node hash.
-/

@[expose] public section

namespace PerfectMerkleTree

open BinaryTree AddressedMerkleTree InductiveMerkleTree

variable {Y : Type _}

/-- The leaf data of the perfect height-`z` subtree rooted at horizontal index `t`. -/
def leafData (leaf : ℕ → Y) (z t : ℕ) : LeafData Y (Skeleton.perfect z) :=
  LeafData.ofFun _ fun i => leaf (i.natIndex t)

/-- The address-dependent node hash of the subtree rooted at `(z, t)`, obtained from a
`(height, horizontal index)`-indexed hash by reading each internal node's address. -/
def nodeHashAt (nodeHash : ℕ → ℕ → Y → Y → Y) (z t : ℕ) :
    SkeletonInternalIndex (Skeleton.perfect z) → Y → Y → Y :=
  fun a => nodeHash (a.natAddr t).1 (a.natAddr t).2

/-- The fully populated perfect subtree at `(height z, horizontal index t)`. -/
def tree (leaf : ℕ → Y) (nodeHash : ℕ → ℕ → Y → Y → Y) (z t : ℕ) :
    FullData Y (Skeleton.perfect z) :=
  buildMerkleTreeAddressedWithHash (leafData leaf z t) (nodeHashAt nodeHash z t)

/-- The root of the perfect subtree at `(height z, horizontal index t)`. -/
def merkleRoot (leaf : ℕ → Y) (nodeHash : ℕ → ℕ → Y → Y → Y) (z t : ℕ) : Y :=
  (tree leaf nodeHash z t).getRootValue

@[simp]
theorem tree_zero (leaf : ℕ → Y) (nodeHash : ℕ → ℕ → Y → Y → Y) (t : ℕ) :
    tree leaf nodeHash 0 t = .leaf (leaf t) := rfl

/-- The subtree at `(z + 1, t)` hashes the subtrees at `(z, 2t)` and `(z, 2t + 1)`. -/
theorem tree_succ (leaf : ℕ → Y) (nodeHash : ℕ → ℕ → Y → Y → Y) (z t : ℕ) :
    tree leaf nodeHash (z + 1) t
      = .internal (nodeHash (z + 1) t (merkleRoot leaf nodeHash z (2 * t))
          (merkleRoot leaf nodeHash z (2 * t + 1)))
        (tree leaf nodeHash z (2 * t)) (tree leaf nodeHash z (2 * t + 1)) := rfl

@[simp]
theorem merkleRoot_zero (leaf : ℕ → Y) (nodeHash : ℕ → ℕ → Y → Y → Y) (t : ℕ) :
    merkleRoot leaf nodeHash 0 t = leaf t := rfl

/-- The FIPS 205 Algorithm 9 / 15 recursion for subtree roots. -/
theorem merkleRoot_succ (leaf : ℕ → Y) (nodeHash : ℕ → ℕ → Y → Y → Y) (z t : ℕ) :
    merkleRoot leaf nodeHash (z + 1) t
      = nodeHash (z + 1) t (merkleRoot leaf nodeHash z (2 * t))
          (merkleRoot leaf nodeHash z (2 * t + 1)) := rfl

/-- The authentication path of leaf `idx` over `z` levels, listed from the leaf level upwards:
entry `j` is the root of the sibling subtree at height `j`. -/
def authPath (leaf : ℕ → Y) (nodeHash : ℕ → ℕ → Y → Y → Y) (idx z : ℕ) : List Y :=
  (generateProof (tree leaf nodeHash z (idx / 2 ^ z))
    (SkeletonLeafIndex.ofNat z idx)).toList.reverse

@[simp]
theorem authPath_length (leaf : ℕ → Y) (nodeHash : ℕ → ℕ → Y → Y → Y) (idx z : ℕ) :
    (authPath leaf nodeHash idx z).length = z := by
  simp [authPath]

/-- Root recovery: starting from `node` at leaf position `idx`, fold in the sibling values of
`auth` (leaf level first), hashing each step under the address of the node being reconstructed.
The tree height is the length of `auth`. -/
def climb (nodeHash : ℕ → ℕ → Y → Y → Y) (idx : ℕ) (node : Y) (auth : List Y) : Y :=
  getPutativeRootAddressedWithHash (nodeHashAt nodeHash auth.length (idx / 2 ^ auth.length))
    (SkeletonLeafIndex.ofNat auth.length idx) node ⟨auth.reverse, by simp⟩

/-- `climb` on a path of known length `z`, unfolded to the engine's putative root. -/
theorem climb_eq (nodeHash : ℕ → ℕ → Y → Y → Y) (idx : ℕ) (node : Y) (auth : List Y)
    {z : ℕ} (hlen : auth.length = z) :
    climb nodeHash idx node auth
      = getPutativeRootAddressedWithHash (nodeHashAt nodeHash z (idx / 2 ^ z))
          (SkeletonLeafIndex.ofNat z idx) node ⟨auth.reverse, by simp [hlen]⟩ := by
  subst hlen; rfl

/-- The honest leaf value is the leaf of `leafData` at `ofNat z idx`. -/
theorem leafData_get_ofNat (leaf : ℕ → Y) (z idx : ℕ) :
    (leafData leaf z (idx / 2 ^ z)).get (SkeletonLeafIndex.ofNat z idx) = leaf idx := by
  simp [leafData]

/-- **Merkle auth-path consistency.** Climbing the honest authentication path of leaf `idx`
from the honest leaf value reconstructs the height-`z` ancestor root. -/
theorem climb_authPath (leaf : ℕ → Y) (nodeHash : ℕ → ℕ → Y → Y → Y) (idx z : ℕ) :
    climb nodeHash idx (leaf idx) (authPath leaf nodeHash idx z)
      = merkleRoot leaf nodeHash z (idx / 2 ^ z) := by
  rw [climb_eq nodeHash idx _ _ (authPath_length leaf nodeHash idx z)]
  have hvec : (⟨(authPath leaf nodeHash idx z).reverse, by simp⟩ :
      List.Vector Y (SkeletonLeafIndex.ofNat z idx).depth)
      = generateProof (tree leaf nodeHash z (idx / 2 ^ z)) (SkeletonLeafIndex.ofNat z idx) := by
    apply Subtype.ext
    simp only [authPath, List.reverse_reverse]
    rfl
  rw [hvec, ← leafData_get_ofNat leaf z idx]
  exact addressed_functional_completeness _ _ _

/-- The child pair stored at an internal address of the honest tree is the pair of honest child
roots at that `(height, index)` address. -/
theorem childPairAt_tree (leaf : ℕ → Y) (nodeHash : ℕ → ℕ → Y → Y → Y) {z : ℕ} (t : ℕ)
    (a : SkeletonInternalIndex (Skeleton.perfect z)) :
    childPairAt (tree leaf nodeHash z t) a
      = (merkleRoot leaf nodeHash ((a.natAddr t).1 - 1) (2 * (a.natAddr t).2),
          merkleRoot leaf nodeHash ((a.natAddr t).1 - 1) (2 * (a.natAddr t).2 + 1)) := by
  induction z generalizing t with
  | zero => nomatch a
  | succ z ih =>
    cases a with
    | ofInternal =>
      rw [tree_succ]
      rfl
    | ofLeft a => rw [tree_succ]; simpa [SkeletonInternalIndex.natAddr] using ih (2 * t) a
    | ofRight a => rw [tree_succ]; simpa [SkeletonInternalIndex.natAddr] using ih (2 * t + 1) a

/-- **Oriented Merkle binding.** An authentication path of length `z` that climbs from a leaf
value `y ≠ leaf idx` to the honest height-`z` root exhibits, at some internal address `(h, i)`
with `0 < h ≤ z`, a collision of `nodeHash h i` whose first endpoint is the honestly computed
child pair at `(h, i)` — a target fixed by the honest tree, before the adversarial opening. -/
theorem climb_binding (leaf : ℕ → Y) (nodeHash : ℕ → ℕ → Y → Y → Y) (z idx : ℕ) (y : Y)
    (auth : List Y) (hlen : auth.length = z)
    (hroot : climb nodeHash idx y auth = merkleRoot leaf nodeHash z (idx / 2 ^ z))
    (hne : leaf idx ≠ y) :
    ∃ (h i : ℕ) (c : Y × Y), 0 < h ∧ h ≤ z ∧
      (merkleRoot leaf nodeHash (h - 1) (2 * i), merkleRoot leaf nodeHash (h - 1) (2 * i + 1))
        ≠ c ∧
      nodeHash h i (merkleRoot leaf nodeHash (h - 1) (2 * i))
          (merkleRoot leaf nodeHash (h - 1) (2 * i + 1))
        = nodeHash h i c.1 c.2 := by
  rw [climb_eq nodeHash idx y auth hlen] at hroot
  have hne' : (leafData leaf z (idx / 2 ^ z)).get (SkeletonLeafIndex.ofNat z idx) ≠ y := by
    rwa [leafData_get_ofNat]
  obtain ⟨a, c, hc, hcol⟩ := addressed_oriented_binding (nodeHashAt nodeHash z (idx / 2 ^ z))
    (leafData leaf z (idx / 2 ^ z)) (SkeletonLeafIndex.ofNat z idx) y _ hroot hne'
  obtain ⟨hpos, hle⟩ := a.natAddr_fst_mem (idx / 2 ^ z)
  have key := childPairAt_tree leaf nodeHash (idx / 2 ^ z) a
  unfold tree at key
  rw [key] at hc hcol
  exact ⟨(a.natAddr (idx / 2 ^ z)).1, (a.natAddr (idx / 2 ^ z)).2, c, hpos, hle, hc, hcol⟩

end PerfectMerkleTree
