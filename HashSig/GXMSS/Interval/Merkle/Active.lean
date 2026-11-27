/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import HashSig.GXMSS.Interval.Merkle.Construction

/-!
# Active paths in interval Merkle trees

Active paths use ordinary ordered pair hashes. Mixed roots and active authentication paths
depend only on active endpoints and the retained frontier table.
-/

public section

namespace GXMSS.IntervalMerkle

variable {h : ℕ}

/-- An active epoch retains its ordinary endpoint-vector leaf hash. -/
theorem leaf_isActive {PP T X H : Type} {w v : ℕ}
    (P : HashInstance PP T X H h w v) (I : Interval h) (pp : PP)
    (xs : Fin (2 ^ h) → Fin v → H) (fillers : Fillers I H)
    (e : Fin (2 ^ h)) (he : Epoch.IsActive I e) :
    leaf P I pp xs fillers e.val = P.leafHash pp e (xs e) := by
  have hnot : ¬ Subtree.IsInactiveFrontier I 0 e.val := by
    simpa using Epoch.isActive_ancestor_not_isInactiveFrontier I e he 0
  simp [leaf, e.isLt, hnot]

/-- Every parent hash on an active path is the ordinary addressed pair hash. -/
theorem node_isActive_ancestor {PP T X H : Type} {w v : ℕ}
    (P : HashInstance PP T X H h w v) (I : Interval h) (pp : PP)
    (fillers : Fillers I H) (e : Fin (2 ^ h)) (he : Epoch.IsActive I e)
    (subtreeHeight : ℕ) (hl : subtreeHeight ≤ h) (left right : H) :
    node P I pp fillers subtreeHeight (e.val / 2 ^ subtreeHeight) left right =
      P.nodeHash pp ⟨subtreeHeight, by omega⟩
        ⟨e.val / 2 ^ subtreeHeight,
          (PerfectMerkleTree.ancestor_legal e subtreeHeight hl).2⟩ left right := by
  have hl' : subtreeHeight < h + 1 := by omega
  have hi' := (PerfectMerkleTree.ancestor_legal e subtreeHeight hl).2
  simp [node, hl', hi', Epoch.isActive_ancestor_not_isInactiveFrontier I e he subtreeHeight]

/-- Every pair hash strictly above an inactive epoch's frontier uses the ordinary addressed
Merkle hash, which is the branch needed for inactive-opening collision extraction. -/
theorem node_above_frontier {PP T X H : Type} {w v : ℕ}
    (P : HashInstance PP T X H h w v) (I : Interval h) (pp : PP)
    (fillers : Fillers I H) (e : Fin (2 ^ h))
    (subtreeHeight : ℕ) (hlt : frontierLevel I e < subtreeHeight) (hle : subtreeHeight ≤ h)
    (left right : H) :
    node P I pp fillers subtreeHeight (e.val / 2 ^ subtreeHeight) left right =
      P.nodeHash pp ⟨subtreeHeight, by omega⟩
        ⟨e.val / 2 ^ subtreeHeight,
          (PerfectMerkleTree.ancestor_legal e subtreeHeight hle).2⟩ left right := by
  have hl' : subtreeHeight < h + 1 := by omega
  have hi' := (PerfectMerkleTree.ancestor_legal e subtreeHeight hle).2
  have hnot : ¬ Subtree.IsInactiveFrontier I subtreeHeight (e.val / 2 ^ subtreeHeight) := by
    intro hf
    exact frontier_above_not_disjointFromInterval I e subtreeHeight hlt hle hf.disjoint
  simp [node, hl', hi', hnot]

/-- A finite mixed-tree path is the engine's leaf-first list. -/
private theorem ofFn_authPath {PP T X H : Type} {w v : ℕ}
    (P : HashInstance PP T X H h w v) (I : Interval h) (pp : PP)
    (xs : Fin (2 ^ h) → Fin v → H) (fillers : Fillers I H)
    (e : Fin (2 ^ h)) :
    List.ofFn (authPath P I pp xs fillers e) =
      PerfectMerkleTree.authPath (leaf P I pp xs fillers) (node P I pp fillers) e h := by
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp [authPath]

/-- Each mixed authentication-path entry is the digest of its exact sibling subtree. -/
theorem authPath_eq_subtreeRoot {PP T X H : Type} {w v : ℕ}
    (P : HashInstance PP T X H h w v) (I : Interval h) (pp : PP)
    (xs : Fin (2 ^ h) → Fin v → H) (fillers : Fillers I H)
    (e : Fin (2 ^ h)) (z : Fin h) :
    authPath P I pp xs fillers e z = subtreeRoot P I pp xs fillers z.val
      (PerfectMerkleTree.sibling (e.val / 2 ^ z.val)) := by
  exact PerfectMerkleTree.authPath_getElem_eq_merkleRoot
    (leaf P I pp xs fillers) (node P I pp fillers)
    e.val h z.val z.isLt

/-- For every active epoch, `HashInstance.recoverRoot` applied to its endpoint vector and
mixed-tree `authPath` yields `root`, using the addressed pair-hash recurrence. -/
theorem recoverRoot_authPath_isActive {PP T X H : Type} {w v : ℕ}
    (P : HashInstance PP T X H h w v) (I : Interval h) (pp : PP)
    (xs : Fin (2 ^ h) → Fin v → H) (fillers : Fillers I H)
    (e : Fin (2 ^ h)) (he : Epoch.IsActive I e) :
    P.recoverRoot pp e (xs e) (authPath P I pp xs fillers e) =
      root P I pp xs fillers := by
  have hn : ∀ subtreeHeight, 0 < subtreeHeight → subtreeHeight ≤ h → ∀ l r,
      ordinaryNode P pp subtreeHeight (e.val / 2 ^ subtreeHeight) l r =
        node P I pp fillers subtreeHeight (e.val / 2 ^ subtreeHeight) l r := by
    intro subtreeHeight _ hle l r
    have hl' : subtreeHeight < h + 1 := by omega
    have hi' := (PerfectMerkleTree.ancestor_legal e subtreeHeight hle).2
    simpa [ordinaryNode, hl', hi'] using
      (node_isActive_ancestor P I pp fillers e he subtreeHeight hle l r).symm
  have hc := PerfectMerkleTree.climb_congr_ancestors (ordinaryNode P pp) (node P I pp fillers)
    e.val (P.leafHash pp e (xs e)) (List.ofFn (authPath P I pp xs fillers e))
    (by intro subtreeHeight hp hl l r; exact hn subtreeHeight hp (by simpa using hl) l r)
  have heq := PerfectMerkleTree.climb_authPath
    (leaf P I pp xs fillers) (node P I pp fillers) e.val h
  rw [← ofFn_authPath, leaf_isActive P I pp xs fillers e he] at heq
  rw [Nat.div_eq_of_lt e.isLt] at heq
  rw [recoverRoot_eq_climb]
  exact hc.trans (by simpa [root, subtreeRoot] using heq)

/-- A maximal inactive subtree contributes exactly its sampled digest, irrespective of the
complete start and endpoint arrays below it. -/
theorem subtreeRoot_isInactiveFrontier {PP T X H : Type} {w v : ℕ}
    (P : HashInstance PP T X H h w v) (I : Interval h) (pp : PP)
    (xs : Fin (2 ^ h) → Fin v → H) (fillers : Fillers I H)
    (subtreeHeight subtreeIndex : ℕ)
    (hf : Subtree.IsInactiveFrontier I subtreeHeight subtreeIndex) :
    subtreeRoot P I pp xs fillers subtreeHeight subtreeIndex =
      fillers ⟨(⟨subtreeHeight, Nat.lt_succ_of_le hf.height_le⟩,
        ⟨subtreeIndex, (PerfectMerkleTree.subtree_legal hf.height_le hf.span_le).2⟩), hf⟩ := by
  have hle : subtreeHeight ≤ h := hf.height_le
  have hl : subtreeHeight < h + 1 := by omega
  have hi := (PerfectMerkleTree.subtree_legal hf.height_le hf.span_le).2
  cases subtreeHeight with
  | zero =>
    simp [subtreeRoot, leaf, hi, hf]
  | succ z =>
    simp [subtreeRoot, PerfectMerkleTree.merkleRoot_succ, node, hl, hi, hf]

/-- A subtree whose parent meets the active interval ignores all inactive endpoint entries. -/
private theorem subtreeRoot_eq_of_active_endpoints_eq {PP T X H : Type} {w v : ℕ}
    (P : HashInstance PP T X H h w v) (I : Interval h) (pp : PP)
    (xs ys : Fin (2 ^ h) → Fin v → H) (fillers : Fillers I H)
    (hactive : ∀ e, Epoch.IsActive I e → xs e = ys e)
    (z i : ℕ) (hz : z ≤ h) (hspan : (i + 1) * 2 ^ z ≤ 2 ^ h)
    (hparent : ¬ Subtree.DisjointFromInterval I (z + 1) (i / 2)) :
    subtreeRoot P I pp xs fillers z i = subtreeRoot P I pp ys fillers z i := by
  induction z generalizing i with
  | zero =>
    have hi : i < 2 ^ h := by simpa using hspan
    by_cases hd : Subtree.DisjointFromInterval I 0 i
    · have hf : Subtree.IsInactiveFrontier I 0 i :=
        (Subtree.isInactiveFrontier_iff_expanded I 0 i).2
          ⟨hz, hspan, hd, Or.inr hparent⟩
      rw [subtreeRoot_isInactiveFrontier P I pp xs fillers 0 i hf,
        subtreeRoot_isInactiveFrontier P I pp ys fillers 0 i hf]
    · have he : Epoch.IsActive I (⟨i, hi⟩ : Fin (2 ^ h)) := by
        by_contra hn
        exact hd ((Subtree.disjointFromInterval_leaf_iff I ⟨i, hi⟩).2 hn)
      simp only [subtreeRoot, PerfectMerkleTree.merkleRoot_zero]
      rw [leaf_isActive P I pp xs fillers ⟨i, hi⟩ he,
        leaf_isActive P I pp ys fillers ⟨i, hi⟩ he, hactive _ he]
  | succ z ih =>
    by_cases hd : Subtree.DisjointFromInterval I (z + 1) i
    · have hf : Subtree.IsInactiveFrontier I (z + 1) i :=
        (Subtree.isInactiveFrontier_iff_expanded I (z + 1) i).2
          ⟨hz, hspan, hd, Or.inr hparent⟩
      rw [subtreeRoot_isInactiveFrontier P I pp xs fillers (z + 1) i hf,
        subtreeRoot_isInactiveFrontier P I pp ys fillers (z + 1) i hf]
    · have hp : 0 < 2 ^ z := by positivity
      have hl : (2 * i + 1) * 2 ^ z ≤ 2 ^ h := by
        rw [pow_succ] at hspan
        nlinarith
      have hr : (2 * i + 1 + 1) * 2 ^ z ≤ 2 ^ h := by
        rw [pow_succ] at hspan
        nlinarith
      have hleft := ih (2 * i) (by omega) hl (by simpa using hd)
      have hright := ih (2 * i + 1) (by omega) hr (by
        have hi : (2 * i + 1) / 2 = i := by omega
        simpa only [hi] using hd)
      change node P I pp fillers (z + 1) i
        (subtreeRoot P I pp xs fillers z (2 * i))
        (subtreeRoot P I pp xs fillers z (2 * i + 1)) = _
      rw [hleft, hright]
      rfl

/-- The interval root depends only on active endpoint vectors and the retained frontier table. -/
theorem root_eq_of_active_endpoints_eq {PP T X H : Type} {w v : ℕ}
    (P : HashInstance PP T X H h w v) (I : Interval h) (pp : PP)
    (xs ys : Fin (2 ^ h) → Fin v → H) (fillers : Fillers I H)
    (hactive : ∀ e, Epoch.IsActive I e → xs e = ys e) :
    root P I pp xs fillers = root P I pp ys fillers := by
  apply subtreeRoot_eq_of_active_endpoints_eq P I pp xs ys fillers hactive h 0 le_rfl
    (by simp)
  let first := I.first
  have he : Epoch.IsActive I first := ⟨le_rfl, I.ordered⟩
  have hi : first.val < 2 ^ (h + 1) := by
    have hf := first.isLt
    rw [pow_succ]
    omega
  simpa [Nat.div_eq_of_lt hi] using
    Epoch.isActive_ancestor_not_disjointFromInterval I first he (h + 1)

/-- An honest active authentication path ignores inactive endpoint entries, including entries
strictly below an inactive frontier of positive height. -/
theorem authPath_eq_of_active_endpoints_eq {PP T X H : Type} {w v : ℕ}
    (P : HashInstance PP T X H h w v) (I : Interval h) (pp : PP)
    (xs ys : Fin (2 ^ h) → Fin v → H) (fillers : Fillers I H)
    (hactive : ∀ e, Epoch.IsActive I e → xs e = ys e)
    (e : Fin (2 ^ h)) (he : Epoch.IsActive I e) :
    authPath P I pp xs fillers e = authPath P I pp ys fillers e := by
  funext z
  rw [authPath_eq_subtreeRoot, authPath_eq_subtreeRoot]
  have hparent := Epoch.isActive_ancestor_not_disjointFromInterval I e he (z.val + 1)
  have hdiv : e.val / 2 ^ (z.val + 1) = (e.val / 2 ^ z.val) / 2 := by
    simp [pow_succ, Nat.div_div_eq_div_mul]
  rw [hdiv] at hparent
  have hsib := PerfectMerkleTree.sibling_div_two (e.val / 2 ^ z.val)
  have hs : PerfectMerkleTree.sibling (e.val / 2 ^ z.val) + 1 ≤
      ((e.val / 2 ^ z.val) / 2 + 1) * 2 := by
    unfold PerfectMerkleTree.sibling
    split_ifs <;> omega
  obtain ⟨_, _, hbound⟩ := PerfectMerkleTree.ancestor_reachable e (z.val + 1) (by omega) (by omega)
  rw [hdiv, pow_succ] at hbound
  apply subtreeRoot_eq_of_active_endpoints_eq P I pp xs ys fillers hactive z.val _ (by omega)
  · nlinarith [Nat.mul_le_mul_right (2 ^ z.val) hs]
  · simpa only [hsib] using hparent

end GXMSS.IntervalMerkle
