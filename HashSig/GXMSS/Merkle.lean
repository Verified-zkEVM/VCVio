/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import HashSig.GXMSS.HashInstance
public import VCVio.CryptoFoundations.MerkleTree.Addressed.NatIndexed

/-!
# Hashed-leaf Merkle adapters

Construction 1 of ePrint 2025/055 hashes endpoint vectors at level zero and pairs left to right.
The pinned perfect-tree engine supplies the root and leaf-first authentication paths.
Fixed-length paths use functions on `Fin h`; list conversion is confined to the engine boundary.
-/

public section

namespace GXMSS

variable {PP T X H : Type} {h w v : ℕ}

namespace HashInstance

/-- The endpoint vector is hashed under the level-zero tree tweak, even at height zero. -/
@[expose] def leafHash (P : HashInstance PP T X H h w v) (pp : PP)
    (e : Fin (2 ^ h)) (xs : Fin v → H) : H :=
  (HashInstance.thf P).eval pp (P.treeTweak (0, e)) (P.vectorInput xs)

/-- Left/right pair hashing at a finite tree address. -/
@[expose] def nodeHash (P : HashInstance PP T X H h w v) (pp : PP)
    (z : Fin (h + 1)) (t : Fin (2 ^ h)) (left right : H) : H :=
  (HashInstance.thf P).eval pp (P.treeTweak (z, t)) (P.pairInput (left, right))

/-- Natural-index extension of finite leaves. The default is used only outside the leaf domain. -/
private def leafExtension (P : HashInstance PP T X H h w v) (pp : PP)
    (xs : Fin (2 ^ h) → Fin v → H) (t : ℕ) : H :=
  if ht : t < 2 ^ h then P.leafHash pp ⟨t, ht⟩ (xs ⟨t, ht⟩) else P.leafHash pp 0 (xs 0)

/-- Natural-index extension of the full finite tree rectangle. Outside the rectangle it returns
its left argument; legal computations are independent of those values. -/
private def nodeExtension (P : HashInstance PP T X H h w v) (pp : PP)
    (z t : ℕ) (left right : H) : H :=
  if hz : z < h + 1 then
    if ht : t < 2 ^ h then P.nodeHash pp ⟨z, hz⟩ ⟨t, ht⟩ left right else left
  else left

/-- Finite-to-natural leaf conversion agrees with the hashed endpoint vector. -/
@[simp] private theorem leafExtension_fin (P : HashInstance PP T X H h w v) (pp : PP)
    (xs : Fin (2 ^ h) → Fin v → H) (e : Fin (2 ^ h)) :
    P.leafExtension pp xs e = P.leafHash pp e (xs e) := by
  simp [leafExtension]

/-- Finite-to-natural node conversion preserves the full rectangle and left/right order. -/
@[simp] private theorem nodeExtension_fin (P : HashInstance PP T X H h w v) (pp : PP)
    (z : Fin (h + 1)) (t : Fin (2 ^ h)) (left right : H) :
    P.nodeExtension pp z t left right = P.nodeHash pp z t left right := by
  simp [nodeExtension, z.isLt]

/-- The root constructed from hashed endpoint vectors. -/
def merkleRoot (P : HashInstance PP T X H h w v) (pp : PP)
    (xs : Fin (2 ^ h) → Fin v → H) : H :=
  PerfectMerkleTree.merkleRoot (P.leafExtension pp xs) (P.nodeExtension pp) h 0

/-- Canonical authentication path, ordered from the leaf level upward. -/
def authPath (P : HashInstance PP T X H h w v) (pp : PP)
    (xs : Fin (2 ^ h) → Fin v → H) (e : Fin (2 ^ h)) : Fin h → H :=
  fun z => (PerfectMerkleTree.authPath (P.leafExtension pp xs)
    (P.nodeExtension pp) e h)[z.val]'(by simp)

/-- Converting the finite path to the engine representation preserves leaf-first order. -/
@[simp] private theorem ofFn_authPath (P : HashInstance PP T X H h w v) (pp : PP)
    (xs : Fin (2 ^ h) → Fin v → H) (e : Fin (2 ^ h)) :
    List.ofFn (P.authPath pp xs e) =
      PerfectMerkleTree.authPath (P.leafExtension pp xs) (P.nodeExtension pp) e h := by
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp [authPath]

/-- Recover a root from a hashed endpoint vector and one sibling per level, leaf first. -/
def recoverRoot (P : HashInstance PP T X H h w v) (pp : PP)
    (e : Fin (2 ^ h)) (xs : Fin v → H) (auth : Fin h → H) : H :=
  PerfectMerkleTree.climb (P.nodeExtension pp) e (P.leafHash pp e xs) (List.ofFn auth)

/-- The honest path reconstructs the constructed root at natural index zero. -/
theorem recoverRoot_authPath (P : HashInstance PP T X H h w v) (pp : PP)
    (xs : Fin (2 ^ h) → Fin v → H) (e : Fin (2 ^ h)) :
    P.recoverRoot pp e (xs e) (P.authPath pp xs e) = P.merkleRoot pp xs := by
  have he : (e : ℕ) / 2 ^ h = 0 := Nat.div_eq_of_lt e.isLt
  simpa [recoverRoot, merkleRoot, he] using
    PerfectMerkleTree.climb_authPath (P.leafExtension pp xs) (P.nodeExtension pp) e h

/-- Height zero still hashes the sole endpoint vector. -/
theorem merkleRoot_zero (P : HashInstance PP T X H 0 w v) (pp : PP)
    (xs : Fin (2 ^ 0) → Fin v → H) :
    P.merkleRoot pp xs = P.leafHash pp 0 (xs 0) := by
  simp [merkleRoot, leafExtension]

/-- At height zero the authentication path is empty. -/
theorem authPath_zero (P : HashInstance PP T X H 0 w v) (pp : PP)
    (xs : Fin (2 ^ 0) → Fin v → H) (e : Fin (2 ^ 0)) :
    P.authPath pp xs e = Fin.elim0 := by
  funext z
  exact Fin.elim0 z

end HashInstance

namespace Merkle

/-- Pair hashing occurs at positive levels whose subtrees fit inside the complete tree. -/
@[expose] def ReachableNode (h z t : ℕ) : Prop :=
  0 < z ∧ z ≤ h ∧ (t + 1) * 2 ^ z ≤ 2 ^ h

/-- Node hashes need agree only at reachable finite addresses, for arbitrary child values. -/
@[expose] def NodeHashAgreement {Y : Type*} (h : ℕ)
    (node₁ node₂ : Fin (h + 1) → Fin (2 ^ h) → Y → Y → Y) : Prop :=
  ∀ z t, ReachableNode h z.val t.val → ∀ l r, node₁ z t l r = node₂ z t l r

/-- An ancestor above the leaf occupies a reachable internal node. -/
theorem ancestor_reachable {h : ℕ} (e : Fin (2 ^ h)) (z : ℕ)
    (hpos : 0 < z) (hz : z ≤ h) : ReachableNode h z (e.val / 2 ^ z) := by
  refine ⟨hpos, hz, ?_⟩
  have he : e.val < 2 ^ (h - z) * 2 ^ z := by
    rw [← Nat.pow_add, Nat.sub_add_cancel hz]
    exact e.isLt
  have hdiv := (Nat.div_lt_iff_lt_mul (by positivity : 0 < 2 ^ z)).2 he
  have hmul := Nat.mul_le_mul_right (2 ^ z) (Nat.succ_le_of_lt hdiv)
  simpa [← Nat.pow_add, Nat.sub_add_cancel hz] using hmul

/-- The finite parent address used at a given leaf-first verification step. -/
@[expose] def parentAddress {h : ℕ} (e : Fin (2 ^ h)) (z : Fin h) :
    Fin (h + 1) × Fin (2 ^ h) :=
  (⟨z.val + 1, by omega⟩,
    ⟨e.val / 2 ^ (z.val + 1), lt_of_le_of_lt (Nat.div_le_self _ _) e.isLt⟩)

/-- Every finite verification step supplies a reachable parent without a caller-side bound. -/
theorem parentAddress_reachable {h : ℕ} (e : Fin (2 ^ h)) (z : Fin h) :
    let address := parentAddress e z
    let level := address.1
    let index := address.2
    ReachableNode h level.val index.val := by
  exact ancestor_reachable e (z.val + 1) (by omega) (by omega)

/-- Agreement on the reachable nodes suffices for every legal subtree root, irrespective
of either natural-index extension at unreachable addresses, including inside the rectangle. -/
theorem root_extension_independent {Y : Type*} (leaf₁ leaf₂ : ℕ → Y)
    (node₁ node₂ : ℕ → ℕ → Y → Y → Y) (h z t : ℕ) (hz : z ≤ h)
    (ht : (t + 1) * 2 ^ z ≤ 2 ^ h)
    (hl : ∀ i < 2 ^ h, leaf₁ i = leaf₂ i)
    (hn : ∀ j, 0 < j → j ≤ h → ∀ i, (i + 1) * 2 ^ j ≤ 2 ^ h →
      ∀ l r, node₁ j i l r = node₂ j i l r) :
    PerfectMerkleTree.merkleRoot leaf₁ node₁ z t =
      PerfectMerkleTree.merkleRoot leaf₂ node₂ z t := by
  induction z generalizing t with
  | zero =>
    simp only [pow_zero, Nat.mul_one] at ht
    exact hl t (by omega)
  | succ z ih =>
    have hp : 0 < 2 ^ z := by positivity
    have hpow : 2 ^ (z + 1) = 2 ^ z * 2 := Nat.pow_succ _ _
    have hleft : (2 * t + 1) * 2 ^ z ≤ 2 ^ h := by
      rw [hpow] at ht
      nlinarith
    have hright : (2 * t + 1 + 1) * 2 ^ z ≤ 2 ^ h := by
      rw [hpow] at ht
      nlinarith
    rw [PerfectMerkleTree.merkleRoot_succ, PerfectMerkleTree.merkleRoot_succ,
      ih (2 * t) (by omega) hleft, ih (2 * t + 1) (by omega) hright]
    exact hn (z + 1) (by omega) hz t ht _ _

/-- Full honest tree data depend only on reachable leaf and node calls. -/
theorem tree_extension_independent {Y : Type*} (leaf₁ leaf₂ : ℕ → Y)
    (node₁ node₂ : ℕ → ℕ → Y → Y → Y) (h z t : ℕ) (hz : z ≤ h)
    (ht : (t + 1) * 2 ^ z ≤ 2 ^ h)
    (hl : ∀ i < 2 ^ h, leaf₁ i = leaf₂ i)
    (hn : ∀ j, 0 < j → j ≤ h → ∀ i, (i + 1) * 2 ^ j ≤ 2 ^ h →
      ∀ l r, node₁ j i l r = node₂ j i l r) :
    PerfectMerkleTree.tree leaf₁ node₁ z t = PerfectMerkleTree.tree leaf₂ node₂ z t := by
  induction z generalizing t with
  | zero =>
    simp only [pow_zero, Nat.mul_one] at ht
    simp [hl t (by omega)]
  | succ z ih =>
    have hp : 0 < 2 ^ z := by positivity
    have hpow : 2 ^ (z + 1) = 2 ^ z * 2 := Nat.pow_succ _ _
    have hleft : (2 * t + 1) * 2 ^ z ≤ 2 ^ h := by
      rw [hpow] at ht
      nlinarith
    have hright : (2 * t + 1 + 1) * 2 ^ z ≤ 2 ^ h := by
      rw [hpow] at ht
      nlinarith
    have hr := root_extension_independent leaf₁ leaf₂ node₁ node₂ h (z + 1) t hz ht hl hn
    rw [PerfectMerkleTree.merkleRoot_succ, PerfectMerkleTree.merkleRoot_succ] at hr
    rw [PerfectMerkleTree.tree_succ, PerfectMerkleTree.tree_succ, hr,
      ih (2 * t) (by omega) hleft, ih (2 * t + 1) (by omega) hright]

/-- Canonical authentication paths are independent of unreachable natural-index extensions. -/
theorem authPath_extension_independent {Y : Type*} (leaf₁ leaf₂ : ℕ → Y)
    (node₁ node₂ : ℕ → ℕ → Y → Y → Y) (h : ℕ) (e : Fin (2 ^ h))
    (hl : ∀ i < 2 ^ h, leaf₁ i = leaf₂ i)
    (hn : ∀ j, 0 < j → j ≤ h → ∀ i, (i + 1) * 2 ^ j ≤ 2 ^ h →
      ∀ l r, node₁ j i l r = node₂ j i l r) :
    PerfectMerkleTree.authPath leaf₁ node₁ e h = PerfectMerkleTree.authPath leaf₂ node₂ e h := by
  have he : (e : ℕ) / 2 ^ h = 0 := Nat.div_eq_of_lt e.isLt
  simp only [PerfectMerkleTree.authPath, he,
    tree_extension_independent leaf₁ leaf₂ node₁ node₂ h h 0 le_rfl (by simp) hl hn]

/-- A reachable subtree index lies in the full paper rectangle. -/
theorem subtree_legal {h z t : ℕ} (hz : z ≤ h) (ht : (t + 1) * 2 ^ z ≤ 2 ^ h) :
    z < h + 1 ∧ t < 2 ^ h := by
  have hp : 0 < 2 ^ z := by positivity
  constructor
  · omega
  · nlinarith

/-- Every ancestor address lies in the full paper rectangle. -/
theorem ancestor_legal {h : ℕ} (e : Fin (2 ^ h)) (z : ℕ) (hz : z ≤ h) :
    z < h + 1 ∧ (e : ℕ) / 2 ^ z < 2 ^ h := by
  constructor
  · omega
  · exact lt_of_le_of_lt (Nat.div_le_self _ _) e.isLt

/-- Every internal address of a legal subtree has positive level and lies in the reachable
subset of the paper rectangle. This covers the address function passed to root recovery. -/
theorem internalAddress_legal (h z t : ℕ) (hz : z ≤ h)
    (ht : (t + 1) * 2 ^ z ≤ 2 ^ h)
    (a : BinaryTree.SkeletonInternalIndex (BinaryTree.Skeleton.perfect z)) :
    0 < (a.natAddr t).height ∧ (a.natAddr t).height ≤ h ∧
      ((a.natAddr t).index + 1) * 2 ^ (a.natAddr t).height ≤ 2 ^ h := by
  induction z generalizing t with
  | zero => nomatch a
  | succ z ih =>
    have hp : 0 < 2 ^ z := by positivity
    have hpow : 2 ^ (z + 1) = 2 ^ z * 2 := Nat.pow_succ _ _
    cases a with
    | ofInternal => exact ⟨by simp [BinaryTree.SkeletonInternalIndex.natAddr], hz, ht⟩
    | ofLeft a =>
      apply ih (2 * t) (by omega) _ a
      rw [hpow] at ht
      nlinarith
    | ofRight a =>
      apply ih (2 * t + 1) (by omega) _ a
      rw [hpow] at ht
      nlinarith

/-- The engine's internal addresses satisfy the reusable pair-hash invariant. -/
theorem internalAddress_reachable (h z t : ℕ) (hz : z ≤ h)
    (ht : (t + 1) * 2 ^ z ≤ 2 ^ h)
    (a : BinaryTree.SkeletonInternalIndex (BinaryTree.Skeleton.perfect z)) :
    ReachableNode h (a.natAddr t).height (a.natAddr t).index :=
  internalAddress_legal h z t hz ht a

/-- Root recovery on a path of paper length is independent of all unreachable node values,
including level zero and natural indices outside the full rectangle. -/
theorem climb_extension_independent {Y : Type*}
    (node₁ node₂ : ℕ → ℕ → Y → Y → Y) (h : ℕ) (e : Fin (2 ^ h))
    (x : Y) (auth : Fin h → Y)
    (hn : ∀ j, 0 < j → j ≤ h → ∀ i, (i + 1) * 2 ^ j ≤ 2 ^ h →
      ∀ l r, node₁ j i l r = node₂ j i l r) :
    PerfectMerkleTree.climb node₁ e x (List.ofFn auth) =
      PerfectMerkleTree.climb node₂ e x (List.ofFn auth) := by
  have he : (e : ℕ) / 2 ^ h = 0 := Nat.div_eq_of_lt e.isLt
  have heq : PerfectMerkleTree.nodeHashAt node₁ h 0 =
      PerfectMerkleTree.nodeHashAt node₂ h 0 := by
    funext a l r
    obtain ⟨hpos, hle, hbound⟩ := internalAddress_legal h h 0 le_rfl (by simp) a
    exact hn _ hpos hle _ hbound l r
  rw [PerfectMerkleTree.climb_eq node₁ e x (List.ofFn auth) (z := h) (by simp),
    PerfectMerkleTree.climb_eq node₂ e x (List.ofFn auth) (z := h) (by simp), he, heq]

/-- Sibling coordinates are listed in increasing height, starting at the leaf level. -/
@[expose] def siblingAddresses (idx height : ℕ) : Fin height → ℕ × ℕ :=
  fun z => (z.val, PerfectMerkleTree.sibling (idx / 2 ^ z.val))

/-- Parent coordinates are listed in the order in which verification hashes. -/
@[expose] def parentAddresses (idx height : ℕ) : Fin height → ℕ × ℕ :=
  fun z => (z.val + 1, idx / 2 ^ (z.val + 1))

/-- The engine appends each next sibling subtree at the end of the leaf-first path. -/
theorem authPath_succ {Y : Type*} (leaf : ℕ → Y) (node : ℕ → ℕ → Y → Y → Y)
    (idx z : ℕ) : PerfectMerkleTree.authPath leaf node idx (z + 1) =
      PerfectMerkleTree.authPath leaf node idx z ++
        [PerfectMerkleTree.merkleRoot leaf node z (PerfectMerkleTree.sibling (idx / 2 ^ z))] :=
  PerfectMerkleTree.authPath_succ _ _ _ _

end Merkle

namespace HashInstance

/-- Finite hashed-leaf agreement supplies the private natural-index adapter agreement. -/
private theorem leafExtension_congr (P Q : HashInstance PP T X H h w v) (pp qq : PP)
    (xs ys : Fin (2 ^ h) → Fin v → H)
    (hl : ∀ e, P.leafHash pp e (xs e) = Q.leafHash qq e (ys e)) (t : ℕ) (ht : t < 2 ^ h) :
    P.leafExtension pp xs t = Q.leafExtension qq ys t := by
  simpa [leafExtension, ht] using hl ⟨t, ht⟩

/-- Reachable finite hash agreement supplies all natural-index engine obligations. -/
private theorem nodeExtension_congr (P Q : HashInstance PP T X H h w v) (pp qq : PP)
    (hn : Merkle.NodeHashAgreement h (P.nodeHash pp) (Q.nodeHash qq))
    (z : ℕ) (hpos : 0 < z) (hz : z ≤ h) (t : ℕ) (ht : (t + 1) * 2 ^ z ≤ 2 ^ h)
    (l r : H) : P.nodeExtension pp z t l r = Q.nodeExtension qq z t l r := by
  obtain ⟨hz', ht'⟩ := Merkle.subtree_legal hz ht
  simpa [nodeExtension, hz', ht'] using hn ⟨z, hz'⟩ ⟨t, ht'⟩ ⟨hpos, hz, ht⟩ l r

/-- Root construction depends on the supplied hashed leaves and reachable pair hashes. -/
theorem merkleRoot_congr (P Q : HashInstance PP T X H h w v) (pp qq : PP)
    (xs ys : Fin (2 ^ h) → Fin v → H)
    (hl : ∀ e, P.leafHash pp e (xs e) = Q.leafHash qq e (ys e))
    (hn : Merkle.NodeHashAgreement h (P.nodeHash pp) (Q.nodeHash qq)) :
    P.merkleRoot pp xs = Q.merkleRoot qq ys :=
  Merkle.root_extension_independent _ _ _ _ h h 0 le_rfl (by simp)
    (leafExtension_congr P Q pp qq xs ys hl) (nodeExtension_congr P Q pp qq hn)

/-- Canonical finite paths depend on the supplied hashed leaves and reachable pair hashes. -/
theorem authPath_congr (P Q : HashInstance PP T X H h w v) (pp qq : PP)
    (xs ys : Fin (2 ^ h) → Fin v → H) (e : Fin (2 ^ h))
    (hl : ∀ i, P.leafHash pp i (xs i) = Q.leafHash qq i (ys i))
    (hn : Merkle.NodeHashAgreement h (P.nodeHash pp) (Q.nodeHash qq)) :
    P.authPath pp xs e = Q.authPath qq ys e := by
  apply List.ofFn_injective
  rw [ofFn_authPath, ofFn_authPath]
  exact Merkle.authPath_extension_independent _ _ _ _ h e
    (leafExtension_congr P Q pp qq xs ys hl) (nodeExtension_congr P Q pp qq hn)

/-- Recovery depends only on its starting hashed leaf and reachable pair hashes. -/
theorem recoverRoot_congr (P Q : HashInstance PP T X H h w v) (pp qq : PP)
    (e : Fin (2 ^ h)) (xs ys : Fin v → H) (auth : Fin h → H)
    (hl : P.leafHash pp e xs = Q.leafHash qq e ys)
    (hn : Merkle.NodeHashAgreement h (P.nodeHash pp) (Q.nodeHash qq)) :
    P.recoverRoot pp e xs auth = Q.recoverRoot qq e ys auth := by
  simpa only [recoverRoot, hl] using
    Merkle.climb_extension_independent (P.nodeExtension pp) (Q.nodeExtension qq) h e
      (P.leafHash pp e xs) auth (nodeExtension_congr P Q pp qq hn)

/-- A height-zero path performs only its starting vector hash, for every endpoint vector. -/
theorem recoverRoot_zero (P : HashInstance PP T X H 0 w v) (pp : PP)
    (e : Fin (2 ^ 0)) (xs : Fin v → H) (auth : Fin 0 → H) :
    P.recoverRoot pp e xs auth = P.leafHash pp e xs := by
  have ha : auth = Fin.elim0 := by
    funext z
    exact Fin.elim0 z
  rw [ha]
  rfl

end HashInstance

end GXMSS
