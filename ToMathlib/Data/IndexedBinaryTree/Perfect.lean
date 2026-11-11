/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/

module
public import ToMathlib.Data.IndexedBinaryTree.Basic

/-!
# Perfect binary skeletons and heap-style natural-number addressing

The perfect binary skeleton `Skeleton.perfect z` of height `z`, together with the bridge between
its typed indices and the heap-style `ℕ` addressing used by XMSS / FIPS 205: a node at height
`h` and horizontal index `t` has children at height `h - 1` and horizontal indices `2t`, `2t+1`.

* `SkeletonLeafIndex.ofNat z i` — the leaf of `Skeleton.perfect z` selected by the low `z` bits
  of `i` (bit `z - 1` chooses the child of the root).
* `SkeletonLeafIndex.natIndex t idx` — the horizontal index of a leaf of the height-`z` subtree
  whose root has horizontal index `t`; `natIndex_ofNat` shows it inverts `ofNat`.
* `NatAddr` — a `(height, horizontal index)` node address.
* `SkeletonInternalIndex.natAddr t a` — the `NatAddr` of an internal node of that subtree;
  `natAddr_index_of_isAncestorOf` shows that an ancestor of a leaf at horizontal index `i`
  sits at height `h` and horizontal index `i / 2 ^ h`.
-/

@[expose] public section

namespace BinaryTree

/-- The perfect binary skeleton of height `z`.

Reducible at implicit transparency so that the constructors of `SkeletonLeafIndex (perfect (z+1))`
and `SkeletonInternalIndex (perfect (z+1))` can be used and case-split on directly. -/
@[implicit_reducible]
def Skeleton.perfect : ℕ → Skeleton
  | 0 => .leaf
  | z + 1 => .internal (perfect z) (perfect z)

@[simp]
theorem Skeleton.perfect_zero : Skeleton.perfect 0 = .leaf := rfl

@[simp]
theorem Skeleton.perfect_succ (z : ℕ) :
    Skeleton.perfect (z + 1) = .internal (perfect z) (perfect z) := rfl

/-- The leaf of the perfect height-`z` skeleton selected by the low `z` bits of `i`, read from
the most significant bit downwards: at the root of a height-`(z+1)` tree, bit `z` of `i` chooses
between the left (`0`) and right (`1`) child. Bits above position `z - 1` are ignored. -/
def SkeletonLeafIndex.ofNat : (z : ℕ) → ℕ → SkeletonLeafIndex (Skeleton.perfect z)
  | 0, _ => .ofLeaf
  | z + 1, i => if i / 2 ^ z % 2 = 0 then .ofLeft (ofNat z i) else .ofRight (ofNat z i)

/-- The horizontal index of a leaf of the perfect height-`z` subtree whose root has horizontal
index `t`, in the heap-style layout where the children of `t` are `2t` and `2t + 1`. -/
def SkeletonLeafIndex.natIndex : {z : ℕ} → ℕ → SkeletonLeafIndex (Skeleton.perfect z) → ℕ
  | 0, t, .ofLeaf => t
  | _ + 1, t, .ofLeft i => natIndex (2 * t) i
  | _ + 1, t, .ofRight i => natIndex (2 * t + 1) i

/-- The heap-style address of a node of a perfect binary tree: its height above the leaves and
its horizontal index within that level. The children of `⟨h + 1, t⟩` are `⟨h, 2t⟩` and
`⟨h, 2t + 1⟩`. -/
@[ext]
structure NatAddr where
  /-- Height above the leaf level. -/
  height : ℕ
  /-- Horizontal index within the level, counted from the left. -/
  index : ℕ
  deriving DecidableEq, Repr

/-- The `(height, horizontal index)` address of an internal node of the perfect height-`z`
subtree whose root has horizontal index `t`. The root itself has address `⟨z, t⟩`. -/
def SkeletonInternalIndex.natAddr :
    {z : ℕ} → ℕ → SkeletonInternalIndex (Skeleton.perfect z) → NatAddr
  | z + 1, t, .ofInternal => ⟨z + 1, t⟩
  | _ + 1, t, .ofLeft a => natAddr (2 * t) a
  | _ + 1, t, .ofRight a => natAddr (2 * t + 1) a

theorem SkeletonLeafIndex.depth_ofNat (z i : ℕ) : (SkeletonLeafIndex.ofNat z i).depth = z := by
  induction z with
  | zero => rfl
  | succ z ih =>
    unfold SkeletonLeafIndex.ofNat
    by_cases h : i / 2 ^ z % 2 = 0
    · rw [ite_eq_left h]; simp [SkeletonLeafIndex.depth, ih]
    · rw [ite_eq_right h]; simp [SkeletonLeafIndex.depth, ih]

/-- `natIndex` inverts `ofNat`: reading the low `z` bits of `i` into a leaf of the subtree whose
root has horizontal index `i / 2 ^ z` lands back at horizontal index `i`. -/
@[simp]
theorem SkeletonLeafIndex.natIndex_ofNat (z i : ℕ) :
    (SkeletonLeafIndex.ofNat z i).natIndex (i / 2 ^ z) = i := by
  induction z with
  | zero => simp [SkeletonLeafIndex.ofNat, SkeletonLeafIndex.natIndex]
  | succ z ih =>
    have hdiv : i / 2 ^ (z + 1) = i / 2 ^ z / 2 := by
      rw [Nat.pow_succ, Nat.div_div_eq_div_mul]
    have hdm := Nat.div_add_mod (i / 2 ^ z) 2
    unfold SkeletonLeafIndex.ofNat
    by_cases h : i / 2 ^ z % 2 = 0
    · rw [ite_eq_left h]
      have : 2 * (i / 2 ^ (z + 1)) = i / 2 ^ z := by omega
      simp only [SkeletonLeafIndex.natIndex, this, ih]
    · rw [ite_eq_right h]
      have : 2 * (i / 2 ^ (z + 1)) + 1 = i / 2 ^ z := by omega
      simp only [SkeletonLeafIndex.natIndex, this, ih]

/-- The height component of an internal address is positive and at most the tree height. -/
theorem SkeletonInternalIndex.natAddr_height_pos_le {z : ℕ} (t : ℕ)
    (a : SkeletonInternalIndex (Skeleton.perfect z)) :
    0 < (a.natAddr t).height ∧ (a.natAddr t).height ≤ z := by
  induction z generalizing t with
  | zero => nomatch a
  | succ z ih =>
    cases a with
    | ofInternal => simp [SkeletonInternalIndex.natAddr]
    | ofLeft a => simp only [SkeletonInternalIndex.natAddr]; have := ih (2 * t) a; omega
    | ofRight a => simp only [SkeletonInternalIndex.natAddr]; have := ih (2 * t + 1) a; omega

/-- Every leaf of the height-`z` subtree rooted at horizontal index `t` has horizontal index
`t` once its low `z` bits are discarded. -/
theorem SkeletonLeafIndex.natIndex_div_pow {z : ℕ} (t : ℕ)
    (l : SkeletonLeafIndex (Skeleton.perfect z)) :
    l.natIndex t / 2 ^ z = t := by
  induction z generalizing t with
  | zero => cases l; simp [SkeletonLeafIndex.natIndex]
  | succ z ih =>
    cases l with
    | ofLeft l =>
      simp only [SkeletonLeafIndex.natIndex]
      rw [Nat.pow_succ, ← Nat.div_div_eq_div_mul, ih]; omega
    | ofRight l =>
      simp only [SkeletonLeafIndex.natIndex]
      rw [Nat.pow_succ, ← Nat.div_div_eq_div_mul, ih]; omega

/-- Reading a leaf's horizontal index recovers its typed position. -/
@[simp]
theorem SkeletonLeafIndex.ofNat_natIndex {z : ℕ} (t : ℕ)
    (l : SkeletonLeafIndex (Skeleton.perfect z)) : ofNat z (l.natIndex t) = l := by
  induction z generalizing t with
  | zero => cases l; rfl
  | succ z ih =>
    cases l with
    | ofLeft l =>
      simp [ofNat, natIndex, natIndex_div_pow, ih]
    | ofRight l =>
      simp [ofNat, natIndex, natIndex_div_pow, ih]

/-- Left-to-right leaf numbering of a perfect tree, with the most significant bit first. -/
def SkeletonLeafIndex.perfectEquiv (z : ℕ) :
    Fin (2 ^ z) ≃ SkeletonLeafIndex (Skeleton.perfect z) where
  toFun i := ofNat z i
  invFun l := ⟨l.natIndex 0, by
    have := natIndex_div_pow 0 l
    exact (Nat.div_eq_zero_iff.mp this).resolve_left (Nat.ne_of_gt (Nat.two_pow_pos z))⟩
  left_inv i := by
    apply Fin.ext
    have h := natIndex_ofNat z i
    simpa [Nat.div_eq_of_lt i.isLt] using h
  right_inv l := ofNat_natIndex 0 l

theorem SkeletonLeafIndex.perfectEquiv_apply (z : ℕ) (i : Fin (2 ^ z)) :
    perfectEquiv z i = ofNat z i := rfl

@[simp]
theorem SkeletonLeafIndex.depth_perfect {z : ℕ} (l : SkeletonLeafIndex (Skeleton.perfect z)) :
    l.depth = z := by
  rw [← ofNat_natIndex 0 l, depth_ofNat]

@[simp]
theorem Skeleton.leafCount_perfect (z : ℕ) : (perfect z).leafCount = 2 ^ z := by
  induction z with
  | zero => rfl
  | succ z ih => simp [leafCount, ih, Nat.pow_succ, Nat.mul_two]

/-- The horizontal index of an internal node lying on the root path of a leaf is the leaf's
horizontal index shifted down by the node's height: ancestors are determined by `(leaf, height)`
in the heap layout. -/
theorem SkeletonInternalIndex.natAddr_index_of_isAncestorOf {z : ℕ} (t : ℕ)
    {a : SkeletonInternalIndex (Skeleton.perfect z)} {l : SkeletonLeafIndex (Skeleton.perfect z)}
    (h : a.IsAncestorOf l) :
    (a.natAddr t).index = l.natIndex t / 2 ^ (a.natAddr t).height := by
  induction z generalizing t with
  | zero => nomatch a
  | succ z ih =>
    cases a with
    | ofInternal =>
      simp only [SkeletonInternalIndex.natAddr]
      exact (SkeletonLeafIndex.natIndex_div_pow t l).symm
    | ofLeft a =>
      cases l with
      | ofLeft l => exact ih (2 * t) h
      | ofRight l => exact absurd h (by simp)
    | ofRight a =>
      cases l with
      | ofRight l => exact ih (2 * t + 1) h
      | ofLeft l => exact absurd h (by simp)

end BinaryTree
