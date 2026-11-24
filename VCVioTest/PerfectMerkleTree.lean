/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import VCVio.CryptoFoundations.MerkleTree.Addressed.NatIndexed.Congruence
public import VCVio.CryptoFoundations.MerkleTree.Addressed.Congruence

/-!
# Perfect Addressed-Merkle Canaries

Concrete examples pin the public behavior of the natural-number adapter over
`AddressedMerkleTree`: global subtree indexing, left/right hash order, authentication-path order,
root reconstruction, and oriented collision extraction. The hashes are deliberately
noncommutative or collision-heavy so that an address, order, or endpoint regression is visible.
-/

public section

namespace VCVioTest.PerfectMerkleTreeCanary

open _root_.PerfectMerkleTree

def leaf (i : ℕ) : ℕ := i + 1

/-- Address-sensitive and noncommutative in its child inputs. -/
def orderedHash (height index left right : ℕ) : ℕ :=
  1000 * height + 100 * index + 10 * left + right

example : orderedHash 1 0 1 2 = 1012 := rfl

example : orderedHash 1 0 1 2 ≠ orderedHash 1 0 2 1 := by decide

/-- The height-two root uses leaves `0` through `3`, in left-to-right order. -/
example : merkleRoot leaf orderedHash 2 0 = 13254 := rfl

/-- A nonzero subtree index selects the global leaves `4` through `7`. -/
example : merkleRoot leaf orderedHash 2 1 = 16038 := rfl

/-- Authentication paths are leaf-first and preserve the sibling side. -/
example : authPath leaf orderedHash 0 2 = [2, 1134] := rfl

example : authPath leaf orderedHash 1 2 = [1, 1134] := rfl

example : authPath leaf orderedHash 2 2 = [4, 1012] := rfl

example : climb orderedHash 0 (leaf 0) (authPath leaf orderedHash 0 2) = 13254 := rfl

example : climb orderedHash 1 (leaf 1) (authPath leaf orderedHash 1 2) = 13254 := rfl

example : climb orderedHash 2 (leaf 2) (authPath leaf orderedHash 2 2) = 13254 := rfl

/-- Every input pair at one address collides, while different addresses remain distinguishable. -/
def addressOnlyHash (height index _left _right : ℕ) : ℕ :=
  100 * height + index

/-- The adversarial leaf first diverges at node `(height = 1, index = 0)`. The extractor keeps
the honest child pair as its first endpoint. -/
example :
    findCollision leaf addressOnlyHash 0 9 (authPath leaf addressOnlyHash 0 2)
      = some (1, (1, 2), (9, 2)) := by
  decide

/-- Height zero has no sibling hashes. -/
example : authPath leaf orderedHash 0 0 = [] := rfl

/-- The third level preserves the global sibling index and leaf-first order. -/
example : authPath leaf orderedHash 2 3 = [4, 1012, 16038] := rfl

example : (authPath leaf orderedHash 2 3)[2]'(by decide) = 16038 := by
  rw [authPath_getElem_eq_merkleRoot leaf orderedHash 2 3 2 (by decide)]
  rfl

example : climb orderedHash 2 (leaf 2) (authPath leaf orderedHash 2 3) = 151578 := rfl

open BinaryTree AddressedMerkleTree InductiveMerkleTree

/-- The two leaves of a depth-one tree. -/
def pairLeaves : LeafData ℕ (Skeleton.perfect 1) := .internal (.leaf 1) (.leaf 2)

/-- The left leaf has a single sibling in its path. -/
def leftIndex : SkeletonLeafIndex (Skeleton.perfect 1) := .ofLeft .ofLeaf

/-- All pairs at this address have the same root. -/
def constantHash (_address : SkeletonInternalIndex (Skeleton.perfect 1))
    (_left _right : ℕ) : ℕ := 0

/-- Only the sibling changes; the opened leaf stays equal to the honest leaf. -/
def changedPath : List.Vector ℕ leftIndex.depth := ⟨[3], by decide⟩

/-- The extractor returns the honest child pair before the changed pair. -/
def sameLeafWitness : SkeletonInternalIndex (Skeleton.perfect 1) × ℕ × ℕ × ℕ × ℕ :=
  (.ofInternal, 1, 2, 1, 3)

/-- Equal leaves with different paths can still yield an internal-node collision. -/
theorem same_leaf_collision :
    findCollisionAddressed constantHash leftIndex
      (generateProof (buildMerkleTreeAddressedWithHash pairLeaves constantHash) leftIndex)
      changedPath (pairLeaves.get leftIndex) (pairLeaves.get leftIndex) =
        some sameLeafWitness := by
  decide

example :
    childPairAt (buildMerkleTreeAddressedWithHash pairLeaves constantHash)
      sameLeafWitness.1 = (1, 2) :=
  (findCollisionAddressed_honest_pair constantHash pairLeaves leftIndex
    (pairLeaves.get leftIndex) changedPath sameLeafWitness same_leaf_collision).symm

/-- A natural-index extension can assign arbitrary values outside the eight leaves. -/
def junkLeaf (i : ℕ) : ℕ := if i < 8 then leaf i else 999999

/-- Even points inside the height/index rectangle may be unreachable by the tree. -/
def junkHash (height index left right : ℕ) : ℕ :=
  if 0 < height ∧ height ≤ 3 ∧ (index + 1) * 2 ^ height ≤ 8 then
    orderedHash height index left right
  else 999999

example : junkHash 0 0 1 2 ≠ orderedHash 0 0 1 2 := by decide

example : junkHash 2 3 1 2 ≠ orderedHash 2 3 1 2 := by decide

private theorem junkLeaf_agrees (i : ℕ) (hi : i < 2 ^ 3) : junkLeaf i = leaf i := by
  change i < 8 at hi
  simp [junkLeaf, hi]

private theorem junkHash_agrees (j : ℕ) (hj : 0 < j) (hle : j ≤ 3)
    (i : ℕ) (hi : (i + 1) * 2 ^ j ≤ 2 ^ 3) (l r : ℕ) :
    junkHash j i l r = orderedHash j i l r := by
  change (i + 1) * 2 ^ j ≤ 8 at hi
  simp [junkHash, hj, hle, hi]

/-- Agreement on reachable calls determines the root despite the other extension values. -/
example : merkleRoot junkLeaf junkHash 3 0 = 151578 := by
  have hroot := root_extension_independent junkLeaf leaf junkHash orderedHash 3 3 0
    le_rfl (by simp)
    junkLeaf_agrees
    junkHash_agrees
  exact hroot.trans rfl

example : authPath junkLeaf junkHash 2 3 = [4, 1012, 16038] := by
  have hpath := authPath_extension_independent junkLeaf leaf junkHash orderedHash
    3 ⟨2, by decide⟩
    junkLeaf_agrees
    junkHash_agrees
  exact hpath.trans rfl

/-- This finite function records the leaf-first path for the third leaf. -/
def thirdLeafPath (i : Fin 3) : ℕ :=
  if i.val = 0 then 4 else if i.val = 1 then 1012 else 16038

example : climb junkHash 2 3 [4, 1012, 16038] = 151578 := by
  have hclimb := climb_extension_independent junkHash orderedHash 3 ⟨2, by decide⟩
    3 thirdLeafPath
    junkHash_agrees
  exact hclimb.trans rfl

/-- The upper tree retains the original hash levels and global subtree indices. -/
example :
    merkleRoot (fun i => merkleRoot leaf orderedHash 1 i)
      (fun j i => orderedHash (1 + j) i) 2 0 = 151578 := by
  rw [← merkleRoot_add]
  rfl

example :
    merkleRoot (fun i => merkleRoot leaf orderedHash 1 i)
      (fun j i => orderedHash (1 + j) i) 1 1 = 16038 := by
  rw [← merkleRoot_add]
  rfl

example : (authPath leaf orderedHash 2 3).take 1 = [4] := by
  rw [authPath_take leaf orderedHash 2 3 1 (by decide)]
  rfl

/-- The leftmost opening visits the root and its left child. -/
def rekeyIndex : SkeletonLeafIndex (Skeleton.perfect 2) := .ofLeft (.ofLeft .ofLeaf)

/-- These two sibling values are listed from the root toward the leaf. -/
def rekeyProof : List.Vector ℕ rekeyIndex.depth := ⟨[3, 2], by decide⟩

/-- Visited nodes share a key; the unused right branch has a different key. -/
def oldKeys : SkeletonInternalIndex (Skeleton.perfect 2) → ℕ
  | .ofRight _ => 999
  | _ => 7

/-- The unused branch intentionally does not agree with the rekeyed old address. -/
def newKeys : SkeletonInternalIndex (Skeleton.perfect 2) → ℕ × Unit
  | .ofRight _ => (0, ())
  | _ => (17, ())

/-- Translate the actual oracle-key type without changing query payloads. -/
def shiftKey (key : ℕ) : ℕ × Unit := (key + 10, ())

/-- The child order affects the hash value. -/
def hashBefore (key left right : ℕ) : ℕ := 10 * left + right + key

/-- The translated hash agrees only where the two key maps name the same original key. -/
def hashAfter (key : ℕ × Unit) (left right : ℕ) : ℕ :=
  10 * left + right + (key.1 - 10)

example : shiftKey (oldKeys (.ofRight .ofInternal)) ≠ newKeys (.ofRight .ofInternal) := by
  decide

private theorem keys_agree_on_path (a : SkeletonInternalIndex (Skeleton.perfect 2))
    (ha : a.IsAncestorOf rekeyIndex) : shiftKey (oldKeys a) = newKeys a := by
  cases a with
  | ofInternal => rfl
  | ofLeft a => rfl
  | ofRight a => simp [rekeyIndex] at ha

private theorem hashes_agree_on_path (a : SkeletonInternalIndex (Skeleton.perfect 2))
    (ha : a.IsAncestorOf rekeyIndex) (l r : ℕ) :
    hashBefore (oldKeys a) l r = hashAfter (newKeys a) l r := by
  cases a with
  | ofInternal => rfl
  | ofLeft a => rfl
  | ofRight a => simp [rekeyIndex] at ha

example :
    getPutativeRootAddressedWithHash (fun a => hashAfter (newKeys a))
      rekeyIndex 1 rekeyProof = 200 := by
  rw [← getPutativeRootAddressedWithHash_congr_ancestors
    (fun a => hashBefore (oldKeys a)) (fun a => hashAfter (newKeys a))
    rekeyIndex 1 rekeyProof hashes_agree_on_path]
  rfl

/-- Rekeying keeps repeated addresses and root-first ordered child pairs in the exact log. -/
example :
    (openingQueries oldKeys hashBefore rekeyIndex 1 rekeyProof).map
        (fun q => (⟨shiftKey q.address, q.input⟩ : NodeQuery (ℕ × Unit) ℕ)) =
      [⟨(17, ()), (19, 3)⟩, ⟨(17, ()), (1, 2)⟩] := by
  rw [openingQueries_rekey oldKeys hashBefore newKeys hashAfter shiftKey
    rekeyIndex 1 rekeyProof keys_agree_on_path hashes_agree_on_path]
  rfl

example : PerfectMerkleTree.findCollisionBetween addressOnlyHash 3 2 3 3
    ⟨[201, 100, 4], by decide⟩ ⟨[201, 100, 99], by decide⟩ =
      some (1, (3, 4), (3, 99)) := by decide

example : PerfectMerkleTree.findCollisionBetween addressOnlyHash 0 2 3 3
    ⟨[], by decide⟩ ⟨[], by decide⟩ = none := by decide

example : (PerfectMerkleTree.findCollisionBetween addressOnlyHash 3 2 3 3
    ⟨[201, 100, 4], by decide⟩ ⟨[201, 100, 99], by decide⟩).isSome := by
  apply PerfectMerkleTree.findCollisionBetween_isSome_of_opening_ne
  · decide
  · decide

example : 0 < 1 ∧ 1 ≤ 3 ∧ (3, 4) ≠ (3, 99) ∧
    addressOnlyHash 1 (2 / 2 ^ 1) 3 4 = addressOnlyHash 1 (2 / 2 ^ 1) 3 99 := by
  exact PerfectMerkleTree.findCollisionBetween_sound addressOnlyHash 3 2 3 3
    ⟨[201, 100, 4], by decide⟩ ⟨[201, 100, 99], by decide⟩
    1 (3, 4) (3, 99) (by decide)

end VCVioTest.PerfectMerkleTreeCanary
