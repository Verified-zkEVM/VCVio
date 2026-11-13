/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import HashSig.GXMSS.Interval.Scheme
import all HashSig.GXMSS.Interval.Scheme
public import HashSig.GXMSS.Security.Auxiliary.MerkleWitnesses
import all HashSig.GXMSS.Security.Auxiliary.MerkleWitnesses

/-!
# Inactive interval Merkle opening witnesses

An accepted opening below an inactive frontier is decomposed at that frontier. The
ordered hash inputs and any later collision use the original addressed THF domain.
-/

public section

namespace GXMSS.Interval.MerkleWitnesses

open GXMSS GXMSS.IntervalMerkle BinaryTree AddressedMerkleTree PerfectMerkleTree

/-- Transport an addressed putative root across equal skeleton indices
without changing the path list. -/
private theorem putativeRoot_index_cast_list {Y : Type} {s : Skeleton}
    (nodeHash : SkeletonInternalIndex s → Y → Y → Y)
    {i j : SkeletonLeafIndex s} (h : i = j) (node : Y) (path : List Y)
    (hi : path.length = i.depth) (hj : path.length = j.depth) :
    getPutativeRootAddressedWithHash nodeHash i node ⟨path, hi⟩ =
      getPutativeRootAddressedWithHash nodeHash j node ⟨path, hj⟩ := by
  cases h
  rfl

/-- The next skeleton height selects its left or right subtree from the next epoch bit. -/
private theorem leafIndex_succ (z idx : ℕ) :
    SkeletonLeafIndex.ofNat (z + 1) idx =
      if idx / 2 ^ z % 2 = 0 then
        .ofLeft (SkeletonLeafIndex.ofNat z idx)
      else .ofRight (SkeletonLeafIndex.ofNat z idx) := rfl

/-- Addressed root recovery at an explicit height with the path stored in reverse order. -/
private def climbAtRev {Y : Type} (nodeHash : ℕ → ℕ → Y → Y → Y)
    (idx : ℕ) (z : ℕ) (node : Y)
    (revPath : List.Vector Y z) : Y :=
  getPutativeRootAddressedWithHash (nodeHashAt nodeHash z (idx / 2 ^ z))
    (SkeletonLeafIndex.ofNat z idx) node
    ⟨revPath.toList, by simp⟩

/-- Equal list lengths give the same addressed recovery despite dependent path witnesses. -/
private theorem climbAtRev_list_len {Y : Type}
    (nodeHash : ℕ → ℕ → Y → Y → Y) (idx : ℕ) (node : Y)
    (path : List Y) (m n : ℕ) (hm : path.length = m) (hn : path.length = n) :
    climbAtRev nodeHash idx m node ⟨path, hm⟩ =
      climbAtRev nodeHash idx n node ⟨path, hn⟩ := by
  have heq : m = n := Eq.trans (Eq.symm hm) hn
  cases heq
  rfl

/-- Add the next sibling to the front of a reversed authentication path. -/
private def revCons {Y : Type} {z : ℕ} (sibling : Y)
    (path : List.Vector Y z) : List.Vector Y (z + 1) :=
  ⟨sibling :: path.toList, by simp⟩

/-- Unfold one addressed engine step before normalizing its child address. -/
private theorem climbAtRev_succ_raw {Y : Type}
    (nodeHash : ℕ → ℕ → Y → Y → Y) (idx z : ℕ)
    (node sibling : Y) (revPath : List.Vector Y z) :
    climbAtRev nodeHash idx (z + 1) node (revCons sibling revPath) =
      if idx / 2 ^ z % 2 = 0 then
        nodeHash (z + 1) (idx / 2 ^ (z + 1))
          (getPutativeRootAddressedWithHash
            (nodeHashAt nodeHash z (2 * (idx / 2 ^ (z + 1))))
            (SkeletonLeafIndex.ofNat z idx) node
            ⟨revPath.toList, by simp⟩) sibling
      else
        nodeHash (z + 1) (idx / 2 ^ (z + 1)) sibling
          (getPutativeRootAddressedWithHash
            (nodeHashAt nodeHash z (2 * (idx / 2 ^ (z + 1)) + 1))
            (SkeletonLeafIndex.ofNat z idx) node
            ⟨revPath.toList, by simp⟩) := by
  let bigHash := nodeHashAt nodeHash (z + 1) (idx / 2 ^ (z + 1))
  let bigIndex := SkeletonLeafIndex.ofNat (z + 1) idx
  let bigPath : List.Vector Y bigIndex.depth := ⟨sibling :: revPath.toList, by simp [bigIndex]⟩
  change getPutativeRootAddressedWithHash bigHash bigIndex node bigPath = _
  by_cases hbit : idx / 2 ^ z % 2 = 0
  · have hindex : bigIndex = .ofLeft (SkeletonLeafIndex.ofNat z idx) := by
      simp [bigIndex, leafIndex_succ, hbit]
    rw [ite_eq_left hbit]
    calc
      _ = getPutativeRootAddressedWithHash bigHash
            (.ofLeft (SkeletonLeafIndex.ofNat z idx)) node
            ⟨sibling :: revPath.toList, by simp [SkeletonLeafIndex.depth]⟩ :=
          putativeRoot_index_cast_list bigHash hindex node _ _ _
      _ = _ := by
        rfl
  · have hindex : bigIndex = .ofRight (SkeletonLeafIndex.ofNat z idx) := by
      simp [bigIndex, leafIndex_succ, hbit]
    rw [ite_eq_right hbit]
    calc
      _ = getPutativeRootAddressedWithHash bigHash
            (.ofRight (SkeletonLeafIndex.ofNat z idx)) node
            ⟨sibling :: revPath.toList, by simp [SkeletonLeafIndex.depth]⟩ :=
          putativeRoot_index_cast_list bigHash hindex node _ _ _
      _ = _ := by
        rfl

/-- The child address of either branch is the current epoch ancestor. -/
private theorem climbAtRev_succ {Y : Type} (nodeHash : ℕ → ℕ → Y → Y → Y) (idx z : ℕ)
    (node sibling : Y) (revPath : List.Vector Y z) :
    climbAtRev nodeHash idx (z + 1) node (revCons sibling revPath) =
      if idx / 2 ^ z % 2 = 0 then
        nodeHash (z + 1) (idx / 2 ^ (z + 1))
          (climbAtRev nodeHash idx z node revPath) sibling
      else
        nodeHash (z + 1) (idx / 2 ^ (z + 1))
          sibling (climbAtRev nodeHash idx z node revPath) := by
  rw [climbAtRev_succ_raw]
  have hdiv : idx / 2 ^ (z + 1) = (idx / 2 ^ z) / 2 := by
    rw [pow_succ, Nat.div_div_eq_div_mul]
  by_cases hbit : idx / 2 ^ z % 2 = 0
  · simp only [ite_eq_left hbit]
    have heven : 2 * (idx / 2 ^ (z + 1)) = idx / 2 ^ z := by
      rw [hdiv]
      have hq := Nat.div_add_mod (idx / 2 ^ z) 2
      omega
    rw [heven]
    rfl
  · simp only [ite_eq_right hbit]
    have hodd : 2 * (idx / 2 ^ (z + 1)) + 1 = idx / 2 ^ z := by
      rw [hdiv]
      have hq := Nat.div_add_mod (idx / 2 ^ z) 2
      omega
    rw [hodd]
    rfl

/-- An arbitrary leaf-first path climbs one further addressed height by hashing
its current root with the appended sibling. -/
private theorem genericClimb_snoc {Y : Type} (nodeHash : ℕ → ℕ → Y → Y → Y)
    (idx : ℕ) (leaf sibling : Y) (auth : List Y) :
    climb nodeHash idx leaf (auth ++ [sibling]) =
      if idx / 2 ^ auth.length % 2 = 0 then
        nodeHash (auth.length + 1) (idx / 2 ^ (auth.length + 1))
          (climb nodeHash idx leaf auth) sibling
      else
        nodeHash (auth.length + 1) (idx / 2 ^ (auth.length + 1))
          sibling (climb nodeHash idx leaf auth) := by
  let revPath : List.Vector Y auth.length := ⟨auth.reverse, by simp⟩
  let reversedPath := (auth ++ [sibling]).reverse
  have hlen : reversedPath.length = auth.length + 1 := by simp [reversedPath]
  calc
    climb nodeHash idx leaf (auth ++ [sibling]) =
        climbAtRev nodeHash idx (auth ++ [sibling]).length leaf
          ⟨(auth ++ [sibling]).reverse, by simp⟩ := rfl
    _ = climbAtRev nodeHash idx (auth.length + 1) leaf
          ⟨(auth ++ [sibling]).reverse, hlen⟩ :=
        climbAtRev_list_len nodeHash idx leaf (auth ++ [sibling]).reverse
          (auth ++ [sibling]).length (auth.length + 1) (by simp) hlen
    _ = climbAtRev nodeHash idx (auth.length + 1) leaf (revCons sibling revPath) := by
        congr 1
        apply Subtype.ext
        simp [revCons, revPath]
    _ = if idx / 2 ^ auth.length % 2 = 0 then
          nodeHash (auth.length + 1) (idx / 2 ^ (auth.length + 1))
            (climbAtRev nodeHash idx auth.length leaf revPath) sibling
        else
          nodeHash (auth.length + 1) (idx / 2 ^ (auth.length + 1))
            sibling (climbAtRev nodeHash idx auth.length leaf revPath) :=
        climbAtRev_succ nodeHash idx auth.length leaf sibling revPath
    _ = _ := by rfl

/-- A leaf-first path splits at any chosen height, retaining original parent addresses
in the upper perfect tree. -/
theorem climb_append {Y : Type} (nodeHash : ℕ → ℕ → Y → Y → Y)
    (idx : ℕ) (leaf : Y) (lower upper : List Y) :
    climb nodeHash idx leaf (lower ++ upper) =
      climb (fun j i => nodeHash (lower.length + j) i)
        (idx / 2 ^ lower.length) (climb nodeHash idx leaf lower) upper := by
  induction upper using List.reverseRecOn with
  | nil => simp only [List.append_nil]; rfl
  | append_singleton upper sibling ih =>
    rw [← List.append_assoc, genericClimb_snoc, genericClimb_snoc, ih]
    have hdiv (j : ℕ) : (idx / 2 ^ lower.length) / 2 ^ j =
        idx / 2 ^ (lower.length + j) := by
      rw [pow_add, Nat.div_div_eq_div_mul]
    simp only [List.length_append, Nat.add_assoc, hdiv]

variable {PP T X H : Type} {h w v : ℕ}

/-- Digest computed from the opening leaf and the path below the unique maximal inactive
frontier node. This is a finite, deterministic computation on the supplied opening. -/
@[expose] def openingFrontierDigest (P : HashInstance PP T X H h w v)
    (I : GXMSS.IntervalMerkle.Interval h) (pp : PP) (e : Fin (2 ^ h))
    (ys : Fin v → H) (auth : Fin h → H) : H :=
  climb (GXMSS.IntervalMerkle.ordinaryNode P pp) e.val (P.leafHash pp e ys)
    ((List.ofFn auth).take (GXMSS.IntervalMerkle.frontierLevel I e))

/-- Root equality reduces an inactive opening to a height-`h-z` opening above its unique
frontier, where `z` is the computed maximal inactive height. -/
theorem climb_above_frontier (P : HashInstance PP T X H h w v)
    (I : GXMSS.IntervalMerkle.Interval h) (pp : PP)
    (xs : Fin (2 ^ h) → Fin v → H) (fillers : GXMSS.IntervalMerkle.Fillers I H)
    (e : Fin (2 ^ h)) (he : ¬ GXMSS.IntervalMerkle.Epoch.IsActive I e)
    (ys : Fin v → H) (auth : Fin h → H)
    (hroot : P.recoverRoot pp e ys auth = GXMSS.IntervalMerkle.root P I pp xs fillers) :
    let z := GXMSS.IntervalMerkle.frontierLevel I e
    climb (fun j i => GXMSS.IntervalMerkle.node P I pp fillers (z + j) i)
      (e.val / 2 ^ z) (openingFrontierDigest P I pp e ys auth)
      ((List.ofFn auth).drop z) = GXMSS.IntervalMerkle.root P I pp xs fillers := by
  dsimp only
  let z := GXMSS.IntervalMerkle.frontierLevel I e
  have hzle : z ≤ h := (GXMSS.IntervalMerkle.frontierLevel_isInactiveFrontier I e he).height_le
  have hlen : (List.ofFn auth).length = h := by simp
  have htake : ((List.ofFn auth).take z).length = z := by simp [hzle]
  let upperPath := (List.ofFn auth).drop z
  have hdrop : upperPath.length = h - z := by simp [upperPath]
  have hsplit := climb_append (GXMSS.IntervalMerkle.ordinaryNode P pp) e.val
    (P.leafHash pp e ys) ((List.ofFn auth).take z) ((List.ofFn auth).drop z)
  have hordinary : P.recoverRoot pp e ys auth =
      climb (fun j i => GXMSS.IntervalMerkle.ordinaryNode P pp (z + j) i)
        (e.val / 2 ^ z) (openingFrontierDigest P I pp e ys auth)
        ((List.ofFn auth).drop z) := by
    calc
      P.recoverRoot pp e ys auth =
          climb (GXMSS.IntervalMerkle.ordinaryNode P pp) e.val (P.leafHash pp e ys)
            (List.ofFn auth) := GXMSS.IntervalMerkle.recoverRoot_eq_climb P pp e ys auth
      _ = climb (GXMSS.IntervalMerkle.ordinaryNode P pp) e.val (P.leafHash pp e ys)
            ((List.ofFn auth).take z ++ (List.ofFn auth).drop z) := by
              rw [List.take_append_drop]
      _ = _ := by simpa only [htake, openingFrontierDigest] using hsplit
  have hnodes : ∀ j, 0 < j → j ≤ upperPath.length → ∀ l r,
      GXMSS.IntervalMerkle.ordinaryNode P pp (z + j) ((e.val / 2 ^ z) / 2 ^ j) l r =
        GXMSS.IntervalMerkle.node P I pp fillers (z + j) ((e.val / 2 ^ z) / 2 ^ j) l r := by
    intro j hj hjle l r
    have hlevel : z + j ≤ h := by omega
    have hstrict : z < z + j := by omega
    have hidx : (e.val / 2 ^ z) / 2 ^ j = e.val / 2 ^ (z + j) := by
      rw [pow_add, Nat.div_div_eq_div_mul]
    rw [hidx]
    have hordinaryNode : GXMSS.IntervalMerkle.ordinaryNode P pp (z + j)
        (e.val / 2 ^ (z + j)) l r =
          P.nodeHash pp ⟨z + j, by omega⟩
            ⟨e.val / 2 ^ (z + j), (Merkle.ancestor_legal e (z + j) hlevel).2⟩
            l r := by
      unfold GXMSS.IntervalMerkle.ordinaryNode
      rw [dite_eq_left (by omega : z + j < h + 1)]
      rw [dite_eq_left (Merkle.ancestor_legal e (z + j) hlevel).2]
    rw [hordinaryNode, GXMSS.IntervalMerkle.node_above_frontier P I pp fillers e
      (z + j) hstrict hlevel]
  have hcongr := GXMSS.IntervalMerkle.climb_congr_ancestors
    (fun j i => GXMSS.IntervalMerkle.ordinaryNode P pp (z + j) i)
    (fun j i => GXMSS.IntervalMerkle.node P I pp fillers (z + j) i)
    (e.val / 2 ^ z) (openingFrontierDigest P I pp e ys auth)
    ((List.ofFn auth).drop z) hnodes
  exact Eq.trans hcongr.symm (Eq.trans hordinary.symm hroot)

/-- The quotient perfect tree above height `z` has the same root as the mixed interval
tree. -/
theorem upperRoot_eq_root (P : HashInstance PP T X H h w v)
    (I : GXMSS.IntervalMerkle.Interval h) (pp : PP)
    (xs : Fin (2 ^ h) → Fin v → H) (fillers : GXMSS.IntervalMerkle.Fillers I H)
    (z : ℕ) (hz : z ≤ h) :
    PerfectMerkleTree.merkleRoot
      (fun i => GXMSS.IntervalMerkle.subtreeRoot P I pp xs fillers z i)
      (fun j i => GXMSS.IntervalMerkle.node P I pp fillers (z + j) i)
      (h - z) 0 = GXMSS.IntervalMerkle.root P I pp xs fillers := by
  have hs := GXMSS.IntervalMerkle.subtreeRoot_shift P I pp xs fillers z (h - z) 0
  simpa only [Nat.add_sub_of_le hz, GXMSS.IntervalMerkle.root] using hs.symm

/-- The prefix of an inactive opening is compared with the unique sampled frontier digest. -/
theorem honestFrontierDigest_eq_filler (P : HashInstance PP T X H h w v)
    (I : GXMSS.IntervalMerkle.Interval h) (pp : PP)
    (xs : Fin (2 ^ h) → Fin v → H) (fillers : GXMSS.IntervalMerkle.Fillers I H)
    (e : Fin (2 ^ h)) (he : ¬ GXMSS.IntervalMerkle.Epoch.IsActive I e) :
    let z := GXMSS.IntervalMerkle.frontierLevel I e
    GXMSS.IntervalMerkle.subtreeRoot P I pp xs fillers z (e.val / 2 ^ z) =
      GXMSS.IntervalMerkle.frontierValue I fillers z (e.val / 2 ^ z)
        (GXMSS.IntervalMerkle.frontierLevel_isInactiveFrontier I e he) := by
  dsimp only
  exact GXMSS.IntervalMerkle.subtreeRoot_isInactiveFrontier P I pp xs fillers _ _
    (GXMSS.IntervalMerkle.frontierLevel_isInactiveFrontier I e he)

/-- The finite addressed collision search on the quotient tree above the frontier.
Its result retains the quotient height and the honest-first ordered child pair. -/
@[expose] def findAboveFrontier [DecidableEq H] (P : HashInstance PP T X H h w v)
    (I : GXMSS.IntervalMerkle.Interval h) (pp : PP)
    (xs : Fin (2 ^ h) → Fin v → H) (fillers : GXMSS.IntervalMerkle.Fillers I H)
    (e : Fin (2 ^ h)) (ys : Fin v → H) (auth : Fin h → H) :
    Option (ℕ × (H × H) × (H × H)) :=
  let z := GXMSS.IntervalMerkle.frontierLevel I e
  PerfectMerkleTree.findCollision
    (fun i => GXMSS.IntervalMerkle.subtreeRoot P I pp xs fillers z i)
    (fun j i => GXMSS.IntervalMerkle.node P I pp fillers (z + j) i)
    (e.val / 2 ^ z) (openingFrontierDigest P I pp e ys auth)
    ((List.ofFn auth).drop z)

/-- A different opening digest at the frontier, reaching the honest root, yields an
oriented collision strictly above the frontier in the quotient tree. -/
theorem findAboveFrontier_oriented [DecidableEq H]
    (P : HashInstance PP T X H h w v) (I : GXMSS.IntervalMerkle.Interval h)
    (pp : PP) (xs : Fin (2 ^ h) → Fin v → H)
    (fillers : GXMSS.IntervalMerkle.Fillers I H) (e : Fin (2 ^ h))
    (he : ¬ GXMSS.IntervalMerkle.Epoch.IsActive I e) (ys : Fin v → H) (auth : Fin h → H)
    (hroot : P.recoverRoot pp e ys auth = GXMSS.IntervalMerkle.root P I pp xs fillers)
    (hne : GXMSS.IntervalMerkle.frontierValue I fillers
      (GXMSS.IntervalMerkle.frontierLevel I e)
      (e.val / 2 ^ GXMSS.IntervalMerkle.frontierLevel I e)
      (GXMSS.IntervalMerkle.frontierLevel_isInactiveFrontier I e he) ≠
        openingFrontierDigest P I pp e ys auth) :
    ∃ q pair, findAboveFrontier P I pp xs fillers e ys auth =
      some (q, PerfectMerkleTree.honestChildren
        (fun i => GXMSS.IntervalMerkle.subtreeRoot P I pp xs fillers
          (GXMSS.IntervalMerkle.frontierLevel I e) i)
        (fun j i => GXMSS.IntervalMerkle.node P I pp fillers
          (GXMSS.IntervalMerkle.frontierLevel I e + j) i)
        q ((e.val / 2 ^ GXMSS.IntervalMerkle.frontierLevel I e) / 2 ^ q), pair) := by
  let z := GXMSS.IntervalMerkle.frontierLevel I e
  have hz : z ≤ h := (GXMSS.IntervalMerkle.frontierLevel_isInactiveFrontier I e he).height_le
  let upperPath := (List.ofFn auth).drop z
  have hlen : upperPath.length = h - z := by simp [upperPath]
  have hindex : (e.val / 2 ^ z) / 2 ^ (h - z) = 0 := by
    apply Nat.div_eq_of_lt
    have hpow : 2 ^ h = 2 ^ z * 2 ^ (h - z) := by
      rw [← pow_add, Nat.add_sub_of_le hz]
    exact (Nat.div_lt_iff_lt_mul (by positivity)).2 (by simpa [hpow, Nat.mul_comm] using e.isLt)
  have hroot' : PerfectMerkleTree.climb
      (fun j i => GXMSS.IntervalMerkle.node P I pp fillers (z + j) i)
      (e.val / 2 ^ z) (openingFrontierDigest P I pp e ys auth)
      ((List.ofFn auth).drop z) =
      PerfectMerkleTree.merkleRoot
        (fun i => GXMSS.IntervalMerkle.subtreeRoot P I pp xs fillers z i)
        (fun j i => GXMSS.IntervalMerkle.node P I pp fillers (z + j) i)
        (h - z) ((e.val / 2 ^ z) / 2 ^ (h - z)) := by
    rw [hindex, upperRoot_eq_root P I pp xs fillers z hz]
    exact climb_above_frontier P I pp xs fillers e he ys auth hroot
  have hne' : GXMSS.IntervalMerkle.subtreeRoot P I pp xs fillers z (e.val / 2 ^ z) ≠
      openingFrontierDigest P I pp e ys auth := by
    rw [honestFrontierDigest_eq_filler P I pp xs fillers e he]
    exact hne
  simpa only [findAboveFrontier] using
    (PerfectMerkleTree.findCollision_oriented
      (fun i => GXMSS.IntervalMerkle.subtreeRoot P I pp xs fillers z i)
      (fun j i => GXMSS.IntervalMerkle.node P I pp fillers (z + j) i)
      (h - z) (e.val / 2 ^ z) (openingFrontierDigest P I pp e ys auth)
      ((List.ofFn auth).drop z) hlen hroot' hne')

/-- Deterministic list of all reachable active-intersecting pair-hash inputs in the honest mixed
tree. The list does not claim the complete-tree game schedule's order or cardinality. -/
@[expose] def honestTargetQueries (P : HashInstance PP T X H h w v)
    (I : GXMSS.IntervalMerkle.Interval h) (pp : PP)
    (xs : Fin (2 ^ h) → Fin v → H) (fillers : GXMSS.IntervalMerkle.Fillers I H) :
    List (T × X) :=
  let heights := List.finRange (h + 1)
  heights.flatMap fun subtreeHeight =>
    let indices := List.finRange (2 ^ h)
    let reachable := indices.filter fun subtreeIndex =>
      decide (0 < subtreeHeight.val ∧ (subtreeIndex.val + 1) * 2 ^ subtreeHeight.val ≤ 2 ^ h ∧
        ¬ GXMSS.IntervalMerkle.Subtree.DisjointFromInterval I subtreeHeight.val subtreeIndex.val)
    reachable.map fun subtreeIndex =>
      (P.treeTweak (subtreeHeight, subtreeIndex),
        P.pairInput
          (GXMSS.IntervalMerkle.subtreeRoot P I pp xs fillers
              (subtreeHeight.val - 1) (2 * subtreeIndex.val),
            GXMSS.IntervalMerkle.subtreeRoot P I pp xs fillers
              (subtreeHeight.val - 1) (2 * subtreeIndex.val + 1)))

/-- Every legal active-intersecting internal node contributes its original ordered child pair to
the deterministic reachable honest target list. -/
theorem honestTargetQueries_mem (P : HashInstance PP T X H h w v)
    (I : GXMSS.IntervalMerkle.Interval h) (pp : PP)
    (xs : Fin (2 ^ h) → Fin v → H) (fillers : GXMSS.IntervalMerkle.Fillers I H)
    (subtreeHeight subtreeIndex : ℕ) (hpos : 0 < subtreeHeight) (hle : subtreeHeight ≤ h)
    (hlegal : (subtreeIndex + 1) * 2 ^ subtreeHeight ≤ 2 ^ h)
    (hnot : ¬ GXMSS.IntervalMerkle.Subtree.DisjointFromInterval I subtreeHeight subtreeIndex) :
    (P.treeTweak (⟨subtreeHeight, by omega⟩,
        ⟨subtreeIndex, (Merkle.subtree_legal hle hlegal).2⟩),
      P.pairInput
        (GXMSS.IntervalMerkle.subtreeRoot P I pp xs fillers (subtreeHeight - 1) (2 * subtreeIndex),
          GXMSS.IntervalMerkle.subtreeRoot P I pp xs fillers (subtreeHeight - 1) (2 * subtreeIndex +
            1))) ∈
        honestTargetQueries P I pp xs fillers := by
  unfold honestTargetQueries
  apply List.mem_flatMap.mpr
  refine ⟨⟨subtreeHeight, by omega⟩, by simp, ?_⟩
  apply List.mem_map.mpr
  refine ⟨⟨subtreeIndex, (Merkle.subtree_legal hle hlegal).2⟩, ?_, rfl⟩
  apply List.mem_filter.mpr
  refine ⟨by simp, ?_⟩
  simp only [decide_eq_true_eq]
  exact ⟨hpos, hlegal, hnot⟩

/-- Quotient-tree honest children are the actual mixed-tree children at the original
global address. -/
theorem upperHonestChildren_eq (P : HashInstance PP T X H h w v)
    (I : GXMSS.IntervalMerkle.Interval h) (pp : PP)
    (xs : Fin (2 ^ h) → Fin v → H) (fillers : GXMSS.IntervalMerkle.Fillers I H)
    (z q subtreeIndex : ℕ) (hq : 0 < q) :
    PerfectMerkleTree.honestChildren
      (fun i => GXMSS.IntervalMerkle.subtreeRoot P I pp xs fillers z i)
      (fun j i => GXMSS.IntervalMerkle.node P I pp fillers (z + j) i)
      q subtreeIndex =
      (GXMSS.IntervalMerkle.subtreeRoot P I pp xs fillers (z + q - 1) (2 * subtreeIndex),
        GXMSS.IntervalMerkle.subtreeRoot P I pp xs fillers (z + q - 1) (2 * subtreeIndex + 1)) := by
  cases q with
  | zero => omega
  | succ q =>
    simp only [PerfectMerkleTree.honestChildren, Nat.succ_sub_one]
    rw [← GXMSS.IntervalMerkle.subtreeRoot_shift P I pp xs fillers z q (2 * subtreeIndex),
      ← GXMSS.IntervalMerkle.subtreeRoot_shift P I pp xs fillers z q (2 * subtreeIndex + 1)]
    simp only [Nat.add_succ, Nat.succ_sub_one]

/-- A returned quotient collision has unequal ordered inputs under one original addressed
pair hash, strictly above the frontier, and its honest first input belongs to the fixed
reachable target list. -/
theorem findAboveFrontier_sound [DecidableEq H]
    (P : HashInstance PP T X H h w v) (I : GXMSS.IntervalMerkle.Interval h)
    (pp : PP) (xs : Fin (2 ^ h) → Fin v → H)
    (fillers : GXMSS.IntervalMerkle.Fillers I H) (e : Fin (2 ^ h))
    (he : ¬ GXMSS.IntervalMerkle.Epoch.IsActive I e) (ys : Fin v → H) (auth : Fin h → H)
    (q : ℕ) (first second : H × H)
    (hw : findAboveFrontier P I pp xs fillers e ys auth = some (q, first, second))
    (hroot : P.recoverRoot pp e ys auth = GXMSS.IntervalMerkle.root P I pp xs fillers)
    (hne : GXMSS.IntervalMerkle.frontierValue I fillers
      (GXMSS.IntervalMerkle.frontierLevel I e)
      (e.val / 2 ^ GXMSS.IntervalMerkle.frontierLevel I e)
      (GXMSS.IntervalMerkle.frontierLevel_isInactiveFrontier I e he) ≠
        openingFrontierDigest P I pp e ys auth) :
    ∃ address : Fin (h + 1) × Fin (2 ^ h),
      let (subtreeHeight, subtreeIndex) := address
      subtreeHeight.val = GXMSS.IntervalMerkle.frontierLevel I e + q ∧
      subtreeIndex.val = e.val / 2 ^ (GXMSS.IntervalMerkle.frontierLevel I e + q) ∧
      GXMSS.IntervalMerkle.frontierLevel I e < subtreeHeight.val ∧
      first = PerfectMerkleTree.honestChildren
        (fun i => GXMSS.IntervalMerkle.subtreeRoot P I pp xs fillers
          (GXMSS.IntervalMerkle.frontierLevel I e) i)
        (fun j i => GXMSS.IntervalMerkle.node P I pp fillers
          (GXMSS.IntervalMerkle.frontierLevel I e + j) i)
        q ((e.val / 2 ^ GXMSS.IntervalMerkle.frontierLevel I e) / 2 ^ q) ∧
      first ≠ second ∧
      P.nodeHash pp address.1 address.2 first.1 first.2 =
        P.nodeHash pp address.1 address.2 second.1 second.2 ∧
      (P.treeTweak address, P.pairInput first) ∈
        honestTargetQueries P I pp xs fillers := by
  let z := GXMSS.IntervalMerkle.frontierLevel I e
  have hzle : z ≤ h := (GXMSS.IntervalMerkle.frontierLevel_isInactiveFrontier I e he).height_le
  let upperPath := (List.ofFn auth).drop z
  have hlen : upperPath.length = h - z := by simp [upperPath]
  have hs := PerfectMerkleTree.findCollision_sound
    (fun i => GXMSS.IntervalMerkle.subtreeRoot P I pp xs fillers z i)
    (fun j i => GXMSS.IntervalMerkle.node P I pp fillers (z + j) i)
    (h - z) (e.val / 2 ^ z) (openingFrontierDigest P I pp e ys auth)
    ((List.ofFn auth).drop z) hlen q first second hw
  obtain ⟨hqpos, hqle, hpairs, hhash⟩ := hs
  have hgle : z + q ≤ h := by omega
  have hgpos : 0 < z + q := by omega
  have hidx : (e.val / 2 ^ z) / 2 ^ q = e.val / 2 ^ (z + q) := by
    rw [pow_add, Nat.div_div_eq_div_mul]
  obtain ⟨q', pair', hor⟩ := findAboveFrontier_oriented P I pp xs fillers
    e he ys auth hroot hne
  rw [hw] at hor
  have htuple := Option.some.inj hor
  obtain ⟨hqq, hrest⟩ := Prod.mk.inj htuple
  obtain ⟨hfirstOriented, _⟩ := Prod.mk.inj hrest
  have hfirstUpper : first = PerfectMerkleTree.honestChildren
      (fun i => GXMSS.IntervalMerkle.subtreeRoot P I pp xs fillers z i)
      (fun j i => GXMSS.IntervalMerkle.node P I pp fillers (z + j) i)
      q ((e.val / 2 ^ z) / 2 ^ q) := by
    simpa only [← hqq] using hfirstOriented
  have hfirst : first =
      (GXMSS.IntervalMerkle.subtreeRoot P I pp xs fillers (z + q - 1)
          (2 * (e.val / 2 ^ (z + q))),
        GXMSS.IntervalMerkle.subtreeRoot P I pp xs fillers (z + q - 1)
          (2 * (e.val / 2 ^ (z + q)) + 1)) := by
    rw [← hidx]
    exact hfirstUpper.trans (upperHonestChildren_eq P I pp xs fillers z q
      ((e.val / 2 ^ z) / 2 ^ q) hqpos)
  have hnot : ¬ GXMSS.IntervalMerkle.Subtree.DisjointFromInterval I (z + q) (e.val / 2 ^ (z + q)) :=
    GXMSS.IntervalMerkle.frontier_above_not_disjointFromInterval I e (z + q) (by omega) hgle
  obtain ⟨_, _, hlegal⟩ := Merkle.ancestor_reachable e (z + q) hgpos hgle
  have htarget := honestTargetQueries_mem P I pp xs fillers (z + q)
    (e.val / 2 ^ (z + q)) hgpos hgle hlegal hnot
  have hnode (l r : H) :
      GXMSS.IntervalMerkle.node P I pp fillers (z + q) (e.val / 2 ^ (z + q)) l r =
        P.nodeHash pp ⟨z + q, by omega⟩
          ⟨e.val / 2 ^ (z + q), (Merkle.ancestor_legal e (z + q) hgle).2⟩
          l r := GXMSS.IntervalMerkle.node_above_frontier P I pp fillers e (z + q)
            (by omega) hgle l r
  rw [hidx, hnode, hnode] at hhash
  let address : Fin (h + 1) × Fin (2 ^ h) :=
    (⟨z + q, by omega⟩,
      ⟨e.val / 2 ^ (z + q), (Merkle.ancestor_legal e (z + q) hgle).2⟩)
  refine ⟨address, rfl, rfl, ?_, ?_, hpairs, ?_, ?_⟩
  · change z < z + q
    omega
  · exact hfirstUpper
  · exact hhash
  · simpa only [address, hfirst] using htarget

/-- Ordered raw pair supplied to the original pair hash at a positive frontier height.
The nonempty path prefix is guaranteed by the positive height. -/
@[expose] def openingFrontierPair (P : HashInstance PP T X H h w v)
    (I : GXMSS.IntervalMerkle.Interval h) (pp : PP) (e : Fin (2 ^ h))
    (he : ¬ GXMSS.IntervalMerkle.Epoch.IsActive I e)
    (hz : 0 < GXMSS.IntervalMerkle.frontierLevel I e)
    (ys : Fin v → H) (auth : Fin h → H) : H × H := by
  let z := GXMSS.IntervalMerkle.frontierLevel I e
  let lower := (List.ofFn auth).take z
  have hzle : z ≤ h := (GXMSS.IntervalMerkle.frontierLevel_isInactiveFrontier I e he).height_le
  have hlen : lower.length = z := by simp [lower, hzle]
  have hn : lower ≠ [] := by
    intro hnil
    have : z = 0 := by simpa [hnil] using hlen.symm
    omega
  let first := PerfectMerkleTree.climb (GXMSS.IntervalMerkle.ordinaryNode P pp) e.val
    (P.leafHash pp e ys) lower.dropLast
  let sibling := lower.getLast hn
  exact if e.val / 2 ^ (z - 1) % 2 = 0 then (first, sibling) else (sibling, first)

/-- Positive frontier digests are original addressed pair-hash outputs of the exact
ordered opening input computed above. -/
theorem openingFrontierDigest_eq_pair (P : HashInstance PP T X H h w v)
    (I : GXMSS.IntervalMerkle.Interval h) (pp : PP) (e : Fin (2 ^ h))
    (he : ¬ GXMSS.IntervalMerkle.Epoch.IsActive I e)
    (hz : 0 < GXMSS.IntervalMerkle.frontierLevel I e)
    (ys : Fin v → H) (auth : Fin h → H) :
    let z := GXMSS.IntervalMerkle.frontierLevel I e
    openingFrontierDigest P I pp e ys auth =
      P.nodeHash pp
        ⟨z, Nat.lt_succ_of_le (GXMSS.IntervalMerkle.frontierLevel_isInactiveFrontier I e
            he).height_le⟩
        ⟨e.val / 2 ^ z,
          (Merkle.ancestor_legal e z
            (GXMSS.IntervalMerkle.frontierLevel_isInactiveFrontier I e he).height_le).2⟩
        (openingFrontierPair P I pp e he hz ys auth).1
        (openingFrontierPair P I pp e he hz ys auth).2 := by
  dsimp only
  let z := GXMSS.IntervalMerkle.frontierLevel I e
  let lower := (List.ofFn auth).take z
  have hzle : z ≤ h := (GXMSS.IntervalMerkle.frontierLevel_isInactiveFrontier I e he).height_le
  have hlen : lower.length = z := by simp [lower, hzle]
  have hn : lower ≠ [] := by
    intro hnil
    have : z = 0 := by simpa [hnil] using hlen.symm
    omega
  have hlast : lower.dropLast ++ [lower.getLast hn] = lower :=
    List.dropLast_append_getLast hn
  let lowerPath := lower.dropLast
  have hprefix : lowerPath.length = z - 1 := by
    dsimp only [lowerPath]
    have hlen' := congrArg List.length hlast
    simp only [List.length_append, List.length_singleton] at hlen'
    omega
  have hstep := genericClimb_snoc (GXMSS.IntervalMerkle.ordinaryNode P pp) e.val
    (P.leafHash pp e ys) (lower.getLast hn) lower.dropLast
  have hraw : openingFrontierDigest P I pp e ys auth =
      if e.val / 2 ^ (z - 1) % 2 = 0 then
        GXMSS.IntervalMerkle.ordinaryNode P pp z (e.val / 2 ^ z)
          (climb (GXMSS.IntervalMerkle.ordinaryNode P pp) e.val (P.leafHash pp e ys)
            lower.dropLast) (lower.getLast hn)
      else GXMSS.IntervalMerkle.ordinaryNode P pp z (e.val / 2 ^ z)
          (lower.getLast hn)
          (climb (GXMSS.IntervalMerkle.ordinaryNode P pp) e.val (P.leafHash pp e ys)
            lower.dropLast) := by
    unfold openingFrontierDigest
    change climb (GXMSS.IntervalMerkle.ordinaryNode P pp) e.val (P.leafHash pp e ys) lower = _
    calc
      _ = climb (GXMSS.IntervalMerkle.ordinaryNode P pp) e.val (P.leafHash pp e ys)
            (lower.dropLast ++ [lower.getLast hn]) := by rw [hlast]
      _ = _ := by
        rw [hstep, hprefix]
        simp only [Nat.sub_add_cancel (by omega : 1 ≤ z)]
  have hnode (l r : H) : GXMSS.IntervalMerkle.ordinaryNode P pp z (e.val / 2 ^ z) l r =
      P.nodeHash pp ⟨z, by omega⟩
        ⟨e.val / 2 ^ z, (Merkle.ancestor_legal e z hzle).2⟩ l r := by
    unfold GXMSS.IntervalMerkle.ordinaryNode
    rw [dite_eq_left (by omega : z < h + 1)]
    rw [dite_eq_left (Merkle.ancestor_legal e z hzle).2]
  have hpair : openingFrontierPair P I pp e he hz ys auth =
      if e.val / 2 ^ (z - 1) % 2 = 0 then
        (climb (GXMSS.IntervalMerkle.ordinaryNode P pp) e.val (P.leafHash pp e ys)
          lower.dropLast, lower.getLast hn)
      else (lower.getLast hn,
        climb (GXMSS.IntervalMerkle.ordinaryNode P pp) e.val (P.leafHash pp e ys)
          lower.dropLast) := by
    rfl
  rw [hpair, hraw]
  by_cases hbit : e.val / 2 ^ (z - 1) % 2 = 0
  · simp only [hbit, ite_true, hnode]
    rfl
  · simp only [hbit, ite_false, hnode]
    rfl

/-- Equality with the stored filler gives an explicit original-domain preimage: a raw
endpoint vector at height zero or an ordered pair at positive height. -/
theorem filler_preimage_of_equal (P : HashInstance PP T X H h w v)
    (I : GXMSS.IntervalMerkle.Interval h) (pp : PP) (e : Fin (2 ^ h))
    (he : ¬ GXMSS.IntervalMerkle.Epoch.IsActive I e) (ys : Fin v → H) (auth : Fin h → H)
    (fillers : GXMSS.IntervalMerkle.Fillers I H)
    (heq : openingFrontierDigest P I pp e ys auth =
      GXMSS.IntervalMerkle.frontierValue I fillers
        (GXMSS.IntervalMerkle.frontierLevel I e)
        (e.val / 2 ^ GXMSS.IntervalMerkle.frontierLevel I e)
        (GXMSS.IntervalMerkle.frontierLevel_isInactiveFrontier I e he)) :
    let z := GXMSS.IntervalMerkle.frontierLevel I e
    (z = 0 ∧ P.leafHash pp e ys =
      GXMSS.IntervalMerkle.frontierValue I fillers z (e.val / 2 ^ z)
        (GXMSS.IntervalMerkle.frontierLevel_isInactiveFrontier I e he)) ∨
    (∃ hz : 0 < z,
      P.nodeHash pp
        ⟨z, Nat.lt_succ_of_le (GXMSS.IntervalMerkle.frontierLevel_isInactiveFrontier I e
            he).height_le⟩
        ⟨e.val / 2 ^ z,
          (Merkle.ancestor_legal e z
            (GXMSS.IntervalMerkle.frontierLevel_isInactiveFrontier I e he).height_le).2⟩
        (openingFrontierPair P I pp e he hz ys auth).1
        (openingFrontierPair P I pp e he hz ys auth).2 =
      GXMSS.IntervalMerkle.frontierValue I fillers z (e.val / 2 ^ z)
        (GXMSS.IntervalMerkle.frontierLevel_isInactiveFrontier I e he)) := by
  dsimp only
  by_cases hz : GXMSS.IntervalMerkle.frontierLevel I e = 0
  · left
    refine ⟨hz, ?_⟩
    have hzero : climb (GXMSS.IntervalMerkle.ordinaryNode P pp) e.val
        (P.leafHash pp e ys) [] = P.leafHash pp e ys := rfl
    simpa only [openingFrontierDigest, hz, List.take_zero, hzero, pow_zero,
      Nat.div_one] using heq
  · right
    have hzpos : 0 < GXMSS.IntervalMerkle.frontierLevel I e := by omega
    have hpair := openingFrontierDigest_eq_pair P I pp e he hzpos ys auth
    exact ⟨hzpos, Eq.trans hpair.symm heq⟩

/-- A verifier-accepted signature gives a successful encoded word and the exact
unrestricted recovered-root equation. The verifier has no active-range guard. -/
theorem accepted_opening [DecidableEq H]
    {M R : Type} (P : HashInstance PP T X H h w v)
    (enc : Encoding.IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w))
    (I : GXMSS.IntervalMerkle.Interval h) (pp : PP)
    (xs : Fin (2 ^ h) → Fin v → H) (fillers : GXMSS.IntervalMerkle.Fillers I H)
    (e : Fin (2 ^ h)) (msg : M) (sig : GXMSS.Signature R H h v)
    (hv : GXMSS.Interval.verify P enc
      ⟨GXMSS.IntervalMerkle.root P I pp xs fillers, pp⟩ e msg sig = true) :
    ∃ word : Encoding.Codeword v (2 ^ w),
      enc.value pp msg sig.randomizer e = some word ∧
      P.recoverRoot pp e
        (fun i => P.chain pp e i (word i) (2 ^ w - 1 - (word i).val) (sig.ots i))
        sig.path = GXMSS.IntervalMerkle.root P I pp xs fillers := by
  simp only [GXMSS.Interval.verify, GXMSS.verify] at hv
  cases hw : enc.value pp msg sig.randomizer e with
  | none => simp [hw] at hv
  | some word =>
    refine ⟨word, by simp, ?_⟩
    simpa only [hw, decide_eq_true_eq] using hv

/-- The explicit original-domain preimage alternatives at the unique frontier. -/
@[expose] def FrontierPreimage (P : HashInstance PP T X H h w v)
    (I : GXMSS.IntervalMerkle.Interval h) (pp : PP) (e : Fin (2 ^ h))
    (he : ¬ GXMSS.IntervalMerkle.Epoch.IsActive I e) (ys : Fin v → H)
    (auth : Fin h → H) (fillers : GXMSS.IntervalMerkle.Fillers I H) : Prop :=
  let z := GXMSS.IntervalMerkle.frontierLevel I e
  (z = 0 ∧ P.leafHash pp e ys =
    GXMSS.IntervalMerkle.frontierValue I fillers z (e.val / 2 ^ z)
      (GXMSS.IntervalMerkle.frontierLevel_isInactiveFrontier I e he)) ∨
  (∃ hz : 0 < z,
    P.nodeHash pp
      ⟨z, Nat.lt_succ_of_le (GXMSS.IntervalMerkle.frontierLevel_isInactiveFrontier I e
          he).height_le⟩
      ⟨e.val / 2 ^ z,
        (Merkle.ancestor_legal e z
          (GXMSS.IntervalMerkle.frontierLevel_isInactiveFrontier I e he).height_le).2⟩
      (openingFrontierPair P I pp e he hz ys auth).1
      (openingFrontierPair P I pp e he hz ys auth).2 =
        GXMSS.IntervalMerkle.frontierValue I fillers z (e.val / 2 ^ z)
          (GXMSS.IntervalMerkle.frontierLevel_isInactiveFrontier I e he))

/-- A returned raw payload itself hashes to the filler at its unique frontier address. -/
@[expose] def RawFrontierPreimage (P : HashInstance PP T X H h w v)
    (I : GXMSS.IntervalMerkle.Interval h) (pp : PP) (e : Fin (2 ^ h))
    (he : ¬ GXMSS.IntervalMerkle.Epoch.IsActive I e) (fillers : GXMSS.IntervalMerkle.Fillers I H)
    (raw : Sum (Fin v → H) (H × H)) : Prop :=
  let z := GXMSS.IntervalMerkle.frontierLevel I e
  match raw with
  | .inl vector =>
    z = 0 ∧ P.leafHash pp e vector =
      GXMSS.IntervalMerkle.frontierValue I fillers z (e.val / 2 ^ z)
        (GXMSS.IntervalMerkle.frontierLevel_isInactiveFrontier I e he)
  | .inr pair =>
    ∃ _hz : 0 < z,
      P.nodeHash pp
        ⟨z, Nat.lt_succ_of_le (GXMSS.IntervalMerkle.frontierLevel_isInactiveFrontier I e
            he).height_le⟩
        ⟨e.val / 2 ^ z,
          (Merkle.ancestor_legal e z
            (GXMSS.IntervalMerkle.frontierLevel_isInactiveFrontier I e he).height_le).2⟩
        pair.1 pair.2 =
          GXMSS.IntervalMerkle.frontierValue I fillers z (e.val / 2 ^ z)
            (GXMSS.IntervalMerkle.frontierLevel_isInactiveFrontier I e he)

/-- Compute the raw vector or ordered pair when the opening frontier digest equals its
sampled filler; otherwise run the finite oriented collision search. On arbitrary openings
the latter may return `none`. -/
@[expose] def extractInactiveOpening [DecidableEq H]
    (P : HashInstance PP T X H h w v) (I : GXMSS.IntervalMerkle.Interval h)
    (pp : PP) (xs : Fin (2 ^ h) → Fin v → H)
    (fillers : GXMSS.IntervalMerkle.Fillers I H) (e : Fin (2 ^ h))
    (he : ¬ GXMSS.IntervalMerkle.Epoch.IsActive I e) (ys : Fin v → H) (auth : Fin h → H) :
    Sum (Sum (Fin v → H) (H × H)) (Option (ℕ × (H × H) × (H × H))) :=
  if openingFrontierDigest P I pp e ys auth =
      GXMSS.IntervalMerkle.frontierValue I fillers
        (GXMSS.IntervalMerkle.frontierLevel I e)
        (e.val / 2 ^ GXMSS.IntervalMerkle.frontierLevel I e)
        (GXMSS.IntervalMerkle.frontierLevel_isInactiveFrontier I e he) then
    if hz : GXMSS.IntervalMerkle.frontierLevel I e = 0 then
      .inl (.inl ys)
    else
      .inl (.inr (openingFrontierPair P I pp e he (Nat.pos_of_ne_zero hz) ys auth))
  else
    .inr (findAboveFrontier P I pp xs fillers e ys auth)

/-- The unequal-frontier branch runs exactly the finite quotient collision finder. -/
theorem extractInactiveOpening_of_unequal [DecidableEq H]
    (P : HashInstance PP T X H h w v) (I : GXMSS.IntervalMerkle.Interval h)
    (pp : PP) (xs : Fin (2 ^ h) → Fin v → H)
    (fillers : GXMSS.IntervalMerkle.Fillers I H) (e : Fin (2 ^ h))
    (he : ¬ GXMSS.IntervalMerkle.Epoch.IsActive I e) (ys : Fin v → H) (auth : Fin h → H)
    (hne : openingFrontierDigest P I pp e ys auth ≠
      GXMSS.IntervalMerkle.frontierValue I fillers
        (GXMSS.IntervalMerkle.frontierLevel I e)
        (e.val / 2 ^ GXMSS.IntervalMerkle.frontierLevel I e)
        (GXMSS.IntervalMerkle.frontierLevel_isInactiveFrontier I e he)) :
    extractInactiveOpening P I pp xs fillers e he ys auth =
      .inr (findAboveFrontier P I pp xs fillers e ys auth) := by
  simp [extractInactiveOpening, hne]

/-- The equal-frontier branch computes the raw vector or pair and proves its
original-domain filler preimage equation. -/
theorem extractInactiveOpening_of_equal [DecidableEq H]
    (P : HashInstance PP T X H h w v) (I : GXMSS.IntervalMerkle.Interval h)
    (pp : PP) (xs : Fin (2 ^ h) → Fin v → H)
    (fillers : GXMSS.IntervalMerkle.Fillers I H) (e : Fin (2 ^ h))
    (he : ¬ GXMSS.IntervalMerkle.Epoch.IsActive I e) (ys : Fin v → H) (auth : Fin h → H)
    (heq : openingFrontierDigest P I pp e ys auth =
      GXMSS.IntervalMerkle.frontierValue I fillers
        (GXMSS.IntervalMerkle.frontierLevel I e)
        (e.val / 2 ^ GXMSS.IntervalMerkle.frontierLevel I e)
        (GXMSS.IntervalMerkle.frontierLevel_isInactiveFrontier I e he)) :
    ∃ raw : Sum (Fin v → H) (H × H),
      extractInactiveOpening P I pp xs fillers e he ys auth = .inl raw ∧
        RawFrontierPreimage P I pp e he fillers raw ∧
        FrontierPreimage P I pp e he ys auth fillers := by
  by_cases hz : GXMSS.IntervalMerkle.frontierLevel I e = 0
  · have hpre := filler_preimage_of_equal P I pp e he ys auth fillers heq
    have hleaf : P.leafHash pp e ys =
        GXMSS.IntervalMerkle.frontierValue I fillers
          (GXMSS.IntervalMerkle.frontierLevel I e)
          (e.val / 2 ^ GXMSS.IntervalMerkle.frontierLevel I e)
          (GXMSS.IntervalMerkle.frontierLevel_isInactiveFrontier I e he) := by
      rcases hpre with hvec | hpair
      · exact hvec.2
      · obtain ⟨hpos, _⟩ := hpair
        omega
    refine ⟨.inl ys, ?_, ?_, hpre⟩
    · simp [extractInactiveOpening, heq, hz]
    · exact ⟨hz, hleaf⟩
  · have hzpos : 0 < GXMSS.IntervalMerkle.frontierLevel I e := Nat.pos_of_ne_zero hz
    have hpre := filler_preimage_of_equal P I pp e he ys auth fillers heq
    have hpair : P.nodeHash pp
        ⟨GXMSS.IntervalMerkle.frontierLevel I e,
          by have := (GXMSS.IntervalMerkle.frontierLevel_isInactiveFrontier I e he).height_le;
              omega⟩
        ⟨e.val / 2 ^ GXMSS.IntervalMerkle.frontierLevel I e,
          (Merkle.ancestor_legal e (GXMSS.IntervalMerkle.frontierLevel I e)
            (GXMSS.IntervalMerkle.frontierLevel_isInactiveFrontier I e he).height_le).2⟩
        (openingFrontierPair P I pp e he hzpos ys auth).1
        (openingFrontierPair P I pp e he hzpos ys auth).2 =
          GXMSS.IntervalMerkle.frontierValue I fillers
            (GXMSS.IntervalMerkle.frontierLevel I e)
            (e.val / 2 ^ GXMSS.IntervalMerkle.frontierLevel I e)
            (GXMSS.IntervalMerkle.frontierLevel_isInactiveFrontier I e he) := by
      rcases hpre with hvec | ⟨hz', hp⟩
      · omega
      · exact hp
    refine ⟨.inr (openingFrontierPair P I pp e he hzpos ys auth), ?_, ?_, hpre⟩
    · simp [extractInactiveOpening, heq, hz]
    · exact ⟨hzpos, hpair⟩

/-- An inactive opening reaching the honest mixed root deterministically yields either
the frontier filler's raw preimage or an oriented original-THF collision above it. -/
theorem inactive_opening_decomposition [DecidableEq H]
    (P : HashInstance PP T X H h w v) (I : GXMSS.IntervalMerkle.Interval h)
    (pp : PP) (xs : Fin (2 ^ h) → Fin v → H)
    (fillers : GXMSS.IntervalMerkle.Fillers I H) (e : Fin (2 ^ h))
    (he : ¬ GXMSS.IntervalMerkle.Epoch.IsActive I e) (ys : Fin v → H) (auth : Fin h → H)
    (hroot : P.recoverRoot pp e ys auth = GXMSS.IntervalMerkle.root P I pp xs fillers) :
    FrontierPreimage P I pp e he ys auth fillers ∨
      ∃ q first second, ∃ address : Fin (h + 1) × Fin (2 ^ h),
        let (subtreeHeight, subtreeIndex) := address
        findAboveFrontier P I pp xs fillers e ys auth = some (q, first, second) ∧
        subtreeHeight.val = GXMSS.IntervalMerkle.frontierLevel I e + q ∧
        subtreeIndex.val = e.val / 2 ^ (GXMSS.IntervalMerkle.frontierLevel I e + q) ∧
        GXMSS.IntervalMerkle.frontierLevel I e < subtreeHeight.val ∧
        first = PerfectMerkleTree.honestChildren
          (fun i => GXMSS.IntervalMerkle.subtreeRoot P I pp xs fillers
            (GXMSS.IntervalMerkle.frontierLevel I e) i)
          (fun j i => GXMSS.IntervalMerkle.node P I pp fillers
            (GXMSS.IntervalMerkle.frontierLevel I e + j) i)
          q ((e.val / 2 ^ GXMSS.IntervalMerkle.frontierLevel I e) / 2 ^ q) ∧
        (GXMSS.Security.HashCollision.mk (P.treeTweak address)
          (P.pairInput first) (P.pairInput second)).Sound P.thf pp ∧
        (P.treeTweak address, P.pairInput first) ∈
          honestTargetQueries P I pp xs fillers := by
  by_cases heq : openingFrontierDigest P I pp e ys auth =
      GXMSS.IntervalMerkle.frontierValue I fillers
        (GXMSS.IntervalMerkle.frontierLevel I e)
        (e.val / 2 ^ GXMSS.IntervalMerkle.frontierLevel I e)
        (GXMSS.IntervalMerkle.frontierLevel_isInactiveFrontier I e he)
  · exact Or.inl (filler_preimage_of_equal P I pp e he ys auth fillers heq)
  · obtain ⟨q, second, hfind⟩ := findAboveFrontier_oriented P I pp xs fillers e
      he ys auth hroot (Ne.symm heq)
    let first := PerfectMerkleTree.honestChildren
      (fun i => GXMSS.IntervalMerkle.subtreeRoot P I pp xs fillers
        (GXMSS.IntervalMerkle.frontierLevel I e) i)
      (fun j i => GXMSS.IntervalMerkle.node P I pp fillers
        (GXMSS.IntervalMerkle.frontierLevel I e + j) i)
      q ((e.val / 2 ^ GXMSS.IntervalMerkle.frontierLevel I e) / 2 ^ q)
    obtain ⟨address, hlevel, hindex, habove, hfirst, hne, hhash, htarget⟩ :=
      findAboveFrontier_sound P I pp xs fillers e he ys auth q first second
        hfind hroot (Ne.symm heq)
    have hcollision : (GXMSS.Security.HashCollision.mk (P.treeTweak address)
        (P.pairInput first) (P.pairInput second)).Sound P.thf pp := by
      exact GXMSS.Security.collision_embedding P.thf pp (P.treeTweak address)
        P.pairInput hne hhash
    exact Or.inr ⟨q, first, second, address, hfind, hlevel, hindex, habove,
      hfirst, hcollision, htarget⟩

/-- The verifier's accepted inactive signature reaches the same concrete decomposition.
Successful encoding and its recovered endpoint vector are retained explicitly. -/
theorem accepted_inactive_decomposition [DecidableEq H]
    {M R : Type} (P : HashInstance PP T X H h w v)
    (enc : Encoding.IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w))
    (I : GXMSS.IntervalMerkle.Interval h) (pp : PP)
    (xs : Fin (2 ^ h) → Fin v → H) (fillers : GXMSS.IntervalMerkle.Fillers I H)
    (e : Fin (2 ^ h)) (he : ¬ GXMSS.IntervalMerkle.Epoch.IsActive I e)
    (msg : M) (sig : GXMSS.Signature R H h v)
    (hv : GXMSS.Interval.verify P enc
      ⟨GXMSS.IntervalMerkle.root P I pp xs fillers, pp⟩ e msg sig = true) :
    ∃ word : Encoding.Codeword v (2 ^ w),
      enc.value pp msg sig.randomizer e = some word ∧
      let ys := fun i => P.chain pp e i (word i) (2 ^ w - 1 - (word i).val) (sig.ots i)
      FrontierPreimage P I pp e he ys sig.path fillers ∨
        ∃ q first second, ∃ address : Fin (h + 1) × Fin (2 ^ h),
          let (subtreeHeight, subtreeIndex) := address
          findAboveFrontier P I pp xs fillers e ys sig.path = some (q, first, second) ∧
          subtreeHeight.val = GXMSS.IntervalMerkle.frontierLevel I e + q ∧
          subtreeIndex.val = e.val / 2 ^ (GXMSS.IntervalMerkle.frontierLevel I e + q) ∧
          GXMSS.IntervalMerkle.frontierLevel I e < subtreeHeight.val ∧
          first = PerfectMerkleTree.honestChildren
            (fun i => GXMSS.IntervalMerkle.subtreeRoot P I pp xs fillers
              (GXMSS.IntervalMerkle.frontierLevel I e) i)
            (fun j i => GXMSS.IntervalMerkle.node P I pp fillers
              (GXMSS.IntervalMerkle.frontierLevel I e + j) i)
            q ((e.val / 2 ^ GXMSS.IntervalMerkle.frontierLevel I e) / 2 ^ q) ∧
          (GXMSS.Security.HashCollision.mk (P.treeTweak address)
            (P.pairInput first) (P.pairInput second)).Sound P.thf pp ∧
          (P.treeTweak address, P.pairInput first) ∈
            honestTargetQueries P I pp xs fillers := by
  obtain ⟨word, hw, hroot⟩ := accepted_opening P enc I pp xs fillers e msg sig hv
  exact ⟨word, hw, inactive_opening_decomposition P I pp xs fillers e he
    (fun i => P.chain pp e i (word i) (2 ^ w - 1 - (word i).val) (sig.ots i))
    sig.path hroot⟩

/-- Equal-frontier raw branch without any complete endpoint array. -/
@[expose] def openingFrontierPreimage [DecidableEq H]
    (P : HashInstance PP T X H h w v) (I : Interval h) (pp : PP)
    (fillers : Fillers I H) (e : Fin (2 ^ h)) (he : ¬ Epoch.IsActive I e)
    (ys : Fin v → H) (auth : Fin h → H) : Option (Sum (Fin v → H) (H × H)) :=
  if openingFrontierDigest P I pp e ys auth = fillers (frontierOf I e he) then
    if hz : frontierLevel I e = 0 then some (.inl ys)
    else some (.inr (openingFrontierPair P I pp e he (Nat.pos_of_ne_zero hz) ys auth))
  else none

/-- Every complete endpoint array has the same raw-preimage projection. -/
theorem openingFrontierPreimage_eq_projection [DecidableEq H]
    (P : HashInstance PP T X H h w v) (I : Interval h) (pp : PP)
    (xs : Fin (2 ^ h) → Fin v → H) (fillers : Fillers I H) (e : Fin (2 ^ h))
    (he : ¬ Epoch.IsActive I e) (ys : Fin v → H) (auth : Fin h → H) :
    openingFrontierPreimage P I pp fillers e he ys auth =
      (match extractInactiveOpening P I pp xs fillers e he ys auth with
      | .inl raw => some raw
      | .inr _ => none) := by
  by_cases hd : openingFrontierDigest P I pp e ys auth = fillers (frontierOf I e he)
  · by_cases hz : frontierLevel I e = 0 <;>
      simp [openingFrontierPreimage, extractInactiveOpening, frontierValue, frontierOf,
        hz] at hd ⊢ <;> simp_all
  · simp [openingFrontierPreimage, extractInactiveOpening, frontierValue, frontierOf] at hd ⊢
    simp_all

/-- Every payload returned by `openingFrontierPreimage` satisfies `RawFrontierPreimage`. -/
theorem openingFrontierPreimage_sound [DecidableEq H]
    (P : HashInstance PP T X H h w v) (I : Interval h) (pp : PP)
    (fillers : Fillers I H) (e : Fin (2 ^ h)) (he : ¬ Epoch.IsActive I e)
    (ys : Fin v → H) (auth : Fin h → H) (raw : Sum (Fin v → H) (H × H))
    (hr : openingFrontierPreimage P I pp fillers e he ys auth = some raw) :
    RawFrontierPreimage P I pp e he fillers raw := by
  have hd : openingFrontierDigest P I pp e ys auth = fillers (frontierOf I e he) := by
    by_contra hn
    simp [openingFrontierPreimage, hn] at hr
  obtain ⟨returned, hx, hp, _⟩ := extractInactiveOpening_of_equal P I pp (fun _ => ys)
    fillers e he ys auth hd
  have hproj := openingFrontierPreimage_eq_projection P I pp (fun _ => ys)
    fillers e he ys auth
  rw [hx, hr] at hproj
  cases Option.some.inj hproj
  exact hp

end GXMSS.Interval.MerkleWitnesses
