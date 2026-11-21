/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import HashSig.GXMSS.Security.Interval.Auxiliary.MerkleWitnesses.Frontier

/-!
# Collisions above inactive frontiers

The quotient-tree extractor keeps the honestly committed input first. Its address and child
values refer to surviving mixed-tree calls in the original hash domain.
-/

public section

namespace GXMSS.Interval.MerkleWitnesses

open GXMSS GXMSS.IntervalMerkle BinaryTree AddressedMerkleTree PerfectMerkleTree

variable {PP T X H : Type} {h w v : ℕ}

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
        ⟨subtreeIndex, (PerfectMerkleTree.subtree_legal hle hlegal).2⟩),
      P.pairInput
        (GXMSS.IntervalMerkle.subtreeRoot P I pp xs fillers (subtreeHeight - 1) (2 * subtreeIndex),
          GXMSS.IntervalMerkle.subtreeRoot P I pp xs fillers (subtreeHeight - 1) (2 * subtreeIndex +
            1))) ∈
        honestTargetQueries P I pp xs fillers := by
  unfold honestTargetQueries
  apply List.mem_flatMap.mpr
  refine ⟨⟨subtreeHeight, by omega⟩, by simp, ?_⟩
  apply List.mem_map.mpr
  refine ⟨⟨subtreeIndex, (PerfectMerkleTree.subtree_legal hle hlegal).2⟩, ?_, rfl⟩
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
  obtain ⟨_, _, hlegal⟩ := PerfectMerkleTree.ancestor_reachable e (z + q) hgpos hgle
  have htarget := honestTargetQueries_mem P I pp xs fillers (z + q)
    (e.val / 2 ^ (z + q)) hgpos hgle hlegal hnot
  have hnode (l r : H) :
      GXMSS.IntervalMerkle.node P I pp fillers (z + q) (e.val / 2 ^ (z + q)) l r =
        P.nodeHash pp ⟨z + q, by omega⟩
          ⟨e.val / 2 ^ (z + q), (PerfectMerkleTree.ancestor_legal e (z + q) hgle).2⟩
          l r := GXMSS.IntervalMerkle.node_above_frontier P I pp fillers e (z + q)
            (by omega) hgle l r
  rw [hidx, hnode, hnode] at hhash
  let address : Fin (h + 1) × Fin (2 ^ h) :=
    (⟨z + q, by omega⟩,
      ⟨e.val / 2 ^ (z + q), (PerfectMerkleTree.ancestor_legal e (z + q) hgle).2⟩)
  refine ⟨address, rfl, rfl, ?_, ?_, hpairs, ?_, ?_⟩
  · change z < z + q
    omega
  · exact hfirstUpper
  · exact hhash
  · simpa only [address, hfirst] using htarget

end GXMSS.Interval.MerkleWitnesses
