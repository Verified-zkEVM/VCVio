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
* `SkeletonInternalIndex.natAddr t a` — the `(height, horizontal index)` address of an internal
  node of that subtree.
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

/-- The `(height, horizontal index)` address of an internal node of the perfect height-`z`
subtree whose root has horizontal index `t`. The root itself has address `(z, t)`. -/
def SkeletonInternalIndex.natAddr :
    {z : ℕ} → ℕ → SkeletonInternalIndex (Skeleton.perfect z) → ℕ × ℕ
  | z + 1, t, .ofInternal => (z + 1, t)
  | _ + 1, t, .ofLeft a => natAddr (2 * t) a
  | _ + 1, t, .ofRight a => natAddr (2 * t + 1) a

@[simp]
theorem SkeletonLeafIndex.depth_ofNat (z i : ℕ) : (SkeletonLeafIndex.ofNat z i).depth = z := by
  induction z with
  | zero => rfl
  | succ z ih =>
    unfold SkeletonLeafIndex.ofNat
    by_cases h : i / 2 ^ z % 2 = 0
    · rw [if_pos h]; simp [SkeletonLeafIndex.depth, ih]
    · rw [if_neg h]; simp [SkeletonLeafIndex.depth, ih]

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
    · rw [if_pos h]
      have : 2 * (i / 2 ^ (z + 1)) = i / 2 ^ z := by omega
      simp only [SkeletonLeafIndex.natIndex, this, ih]
    · rw [if_neg h]
      have : 2 * (i / 2 ^ (z + 1)) + 1 = i / 2 ^ z := by omega
      simp only [SkeletonLeafIndex.natIndex, this, ih]

/-- The height component of an internal address lies in `(0, z]`. -/
theorem SkeletonInternalIndex.natAddr_fst_mem {z : ℕ} (t : ℕ)
    (a : SkeletonInternalIndex (Skeleton.perfect z)) :
    0 < (a.natAddr t).1 ∧ (a.natAddr t).1 ≤ z := by
  induction z generalizing t with
  | zero => nomatch a
  | succ z ih =>
    cases a with
    | ofInternal => simp [SkeletonInternalIndex.natAddr]
    | ofLeft a => simp only [SkeletonInternalIndex.natAddr]; have := ih (2 * t) a; omega
    | ofRight a => simp only [SkeletonInternalIndex.natAddr]; have := ih (2 * t + 1) a; omega

end BinaryTree
