/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import VCVio.CryptoFoundations.MerkleTree.Addressed.NatIndexed
import VCVio.CryptoFoundations.MerkleTree.Addressed.Congruence
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Reachable-node congruence for perfect Merkle trees

Roots, full tree data, authentication paths and recovery depend only on leaf and node calls
reachable inside the specified finite tree. Values of a natural-index extension elsewhere are
irrelevant. Subtree composition retains the original levels in its shifted node hash.
-/

public section

namespace PerfectMerkleTree

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

/-- A reachable subtree index lies in the finite height/index rectangle. -/
theorem subtree_legal {h z t : ℕ} (hz : z ≤ h) (ht : (t + 1) * 2 ^ z ≤ 2 ^ h) :
    z < h + 1 ∧ t < 2 ^ h := by
  have hp : 0 < 2 ^ z := by positivity
  constructor
  · omega
  · nlinarith

/-- Every ancestor address lies in the finite height/index rectangle. -/
theorem ancestor_legal {h : ℕ} (e : Fin (2 ^ h)) (z : ℕ) (hz : z ≤ h) :
    z < h + 1 ∧ (e : ℕ) / 2 ^ z < 2 ^ h := by
  constructor
  · omega
  · exact lt_of_le_of_lt (Nat.div_le_self _ _) e.isLt

/-- Every internal address of a legal subtree has positive level and lies in the reachable
subset of the finite height/index rectangle. This covers the address function passed to
root recovery. -/
theorem internalAddress_reachable (h z t : ℕ) (hz : z ≤ h)
    (ht : (t + 1) * 2 ^ z ≤ 2 ^ h)
    (a : BinaryTree.SkeletonInternalIndex (BinaryTree.Skeleton.perfect z)) :
    ReachableNode h (a.natAddr t).height (a.natAddr t).index := by
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

/-- Root recovery depends only on hashes at the opened leaf's ancestors. -/
theorem climb_congr_ancestors {Y : Type*} (node₁ node₂ : ℕ → ℕ → Y → Y → Y)
    (e : ℕ) (value : Y) (path : List Y)
    (hn : ∀ subtreeHeight, 0 < subtreeHeight → subtreeHeight ≤ path.length → ∀ l r,
      node₁ subtreeHeight (e / 2 ^ subtreeHeight) l r =
        node₂ subtreeHeight (e / 2 ^ subtreeHeight) l r) :
    PerfectMerkleTree.climb node₁ e value path =
      PerfectMerkleTree.climb node₂ e value path := by
  rw [PerfectMerkleTree.climb_eq node₁ e value path rfl,
    PerfectMerkleTree.climb_eq node₂ e value path rfl]
  apply AddressedMerkleTree.getPutativeRootAddressedWithHash_congr_ancestors
  intro a ha l r
  obtain ⟨hpos, hle⟩ := a.natAddr_height_pos_le (e / 2 ^ path.length)
  simpa [PerfectMerkleTree.nodeHashAt,
    PerfectMerkleTree.natAddr_index_of_isAncestorOf_ofNat ha] using
    hn _ hpos hle l r

/-- Root recovery on a path of length `h` is independent of all unreachable node values,
including level zero and natural indices outside the full rectangle. -/
theorem climb_extension_independent {Y : Type*}
    (node₁ node₂ : ℕ → ℕ → Y → Y → Y) (h : ℕ) (e : Fin (2 ^ h))
    (x : Y) (auth : Fin h → Y)
    (hn : ∀ j, 0 < j → j ≤ h → ∀ i, (i + 1) * 2 ^ j ≤ 2 ^ h →
      ∀ l r, node₁ j i l r = node₂ j i l r) :
    PerfectMerkleTree.climb node₁ e x (List.ofFn auth) =
      PerfectMerkleTree.climb node₂ e x (List.ofFn auth) := by
  apply climb_congr_ancestors
  intro j hj hlen l r
  have hjh : j ≤ h := by simpa only [List.length_ofFn] using hlen
  have hreachable := ancestor_reachable e j hj hjh
  exact hn j hj hjh (e.val / 2 ^ j) hreachable.2.2 l r

/-- Sibling coordinates are listed in increasing height, starting at the leaf level. -/
@[expose] def siblingAddresses (idx height : ℕ) : Fin height → ℕ × ℕ :=
  fun z => (z.val, PerfectMerkleTree.sibling (idx / 2 ^ z.val))

/-- Parent coordinates are listed in the order in which root recovery hashes. -/
@[expose] def parentAddresses (idx height : ℕ) : Fin height → ℕ × ℕ :=
  fun z => (z.val + 1, idx / 2 ^ (z.val + 1))

/-- The lower prefix of a canonical authentication path is the canonical shorter path. -/
theorem authPath_take {Y : Type*} (leaf : ℕ → Y) (node : ℕ → ℕ → Y → Y → Y)
    (idx height cut : ℕ) (hcut : cut ≤ height) :
    (authPath leaf node idx height).take cut = authPath leaf node idx cut := by
  apply List.ext_getElem
  · simp [hcut]
  · intro i _ hi
    have hic : i < cut := by simpa only [authPath_length] using hi
    have hih : i < height := hic.trans_le hcut
    simp only [List.getElem_take]
    rw [authPath_getElem_eq_merkleRoot _ _ _ _ _ hih,
      authPath_getElem_eq_merkleRoot _ _ _ _ _ hic]

/-- Grouping every height-`z` subtree into a leaf preserves the root, with node levels
shifted by `z` in the upper tree. -/
theorem merkleRoot_add {Y : Type*} (leaf : ℕ → Y)
    (node : ℕ → ℕ → Y → Y → Y) (z k t : ℕ) :
    merkleRoot leaf node (z + k) t =
      merkleRoot (fun i => merkleRoot leaf node z i)
        (fun j i => node (z + j) i) k t := by
  induction k generalizing t with
  | zero => simp
  | succ k ih =>
    rw [Nat.add_succ, merkleRoot_succ, merkleRoot_succ, ih (2 * t), ih (2 * t + 1)]
    rfl

end PerfectMerkleTree
