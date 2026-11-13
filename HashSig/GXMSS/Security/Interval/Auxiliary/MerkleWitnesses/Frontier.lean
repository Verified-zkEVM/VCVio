/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import HashSig.GXMSS.Interval.Scheme
public import HashSig.GXMSS.Security.Auxiliary.HashWitnesses
public import VCVio.CryptoFoundations.MerkleTree.Addressed.NatIndexed.Option

/-!
# Opening digests at inactive frontiers

A supplied opening is split at its unique maximal inactive frontier. The shared monadic climb
laws specialize through Id, retaining the original upper-tree levels and child order.
-/

public section

namespace GXMSS.Interval.MerkleWitnesses

open GXMSS GXMSS.IntervalMerkle BinaryTree AddressedMerkleTree PerfectMerkleTree

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
  have hsplit := congrArg Id.run (PerfectMerkleTree.climbM_append (m := Id)
    (GXMSS.IntervalMerkle.ordinaryNode P pp) e.val (P.leafHash pp e ys)
    ((List.ofFn auth).take z) ((List.ofFn auth).drop z))
  simp only [PerfectMerkleTree.idRun_climbM, Id.run_bind] at hsplit
  simp only [Id.run] at hsplit
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
      _ = _ := by simpa only [htake, openingFrontierDigest, Nat.add_comm] using hsplit
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
            ⟨e.val / 2 ^ (z + j), (PerfectMerkleTree.ancestor_legal e (z + j) hlevel).2⟩
            l r := by
      unfold GXMSS.IntervalMerkle.ordinaryNode
      rw [dite_eq_left (by omega : z + j < h + 1)]
      rw [dite_eq_left (PerfectMerkleTree.ancestor_legal e (z + j) hlevel).2]
    rw [hordinaryNode, GXMSS.IntervalMerkle.node_above_frontier P I pp fillers e
      (z + j) hstrict hlevel]
  have hcongr := PerfectMerkleTree.climb_congr_ancestors
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

end GXMSS.Interval.MerkleWitnesses
