/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import HashSig.GXMSS.Interval.Merkle.Basic
import all HashSig.GXMSS.Merkle

/-!
# Mixed interval Merkle construction

Sample one independent root per maximal inactive subtree. Natural-index adapters retain the
complete hashed-leaf engine, with exact full-range root and authentication-path equalities.
-/

public section

namespace GXMSS.IntervalMerkle

variable {h : ℕ}

/-- One digest for each maximal inactive subtree. -/
abbrev Fillers (I : Interval h) (H : Type) := Subtree.FrontierNode I → H

instance (h : ℕ) : IsEmpty (Subtree.FrontierNode (Interval.full h)) where
  false node := by
    obtain ⟨⟨subtreeHeight, subtreeIndex⟩, hfrontier⟩ := node
    exact Subtree.full_not_isInactiveFrontier h subtreeHeight.val subtreeIndex.val hfrontier

/-- Sample independent uniform digests only at maximal inactive subtree roots. -/
@[expose] noncomputable def sampleFillers (I : Interval h) (H : Type) [SampleableType H] :
    ProbComp (Fillers I H) :=
  if hc : Fintype.card (Subtree.FrontierNode I) = 0 then
    let emptyFrontier : IsEmpty (Subtree.FrontierNode I) := Fintype.card_eq_zero_iff.mp hc
    pure (fun node => False.elim (emptyFrontier.false node))
  else Fintype.mPi (fun _ : Subtree.FrontierNode I => $ᵗ H)

/-- Full-range key generation has no filler draw or filler output coordinate. -/
theorem sampleFillers_full (h : ℕ) (H : Type) [SampleableType H] :
    sampleFillers (Interval.full h) H = pure (fun x => isEmptyElim x) := by
  have hc : Fintype.card (Subtree.FrontierNode (Interval.full h)) = 0 :=
    Fintype.card_eq_zero
  simp only [sampleFillers, dite_eq_left hc]
  congr 1

/-- The mixed tree's natural-index leaf adapter. A leaf covered by a larger inactive subtree
may retain its ordinary endpoint hash; the ancestor filler replaces that subtree's result. -/
@[expose] def leaf {PP T X H : Type} {w v : ℕ}
    (P : HashInstance PP T X H h w v) (I : Interval h) (pp : PP)
    (xs : Fin (2 ^ h) → Fin v → H) (fillers : Fillers I H) (subtreeIndex : ℕ) : H :=
  if hi : subtreeIndex < 2 ^ h then
    if hf : Subtree.IsInactiveFrontier I 0 subtreeIndex then
      fillers ⟨(⟨0, by omega⟩, ⟨subtreeIndex, hi⟩), hf⟩
    else P.leafHash pp ⟨subtreeIndex, hi⟩ (xs ⟨subtreeIndex, hi⟩)
  else P.leafHash pp 0 (xs 0)

/-- The mixed tree's natural-index pair adapter. A frontier node terminates recursion at
its stored uniform digest; all other reachable internal nodes use the ordinary ordered pair hash. -/
@[expose] def node {PP T X H : Type} {w v : ℕ}
    (P : HashInstance PP T X H h w v) (I : Interval h) (pp : PP)
    (fillers : Fillers I H) (subtreeHeight subtreeIndex : ℕ) (left right : H) : H :=
  if hl : subtreeHeight < h + 1 then
    if hi : subtreeIndex < 2 ^ h then
      if hf : Subtree.IsInactiveFrontier I subtreeHeight subtreeIndex then
        fillers ⟨(⟨subtreeHeight, hl⟩, ⟨subtreeIndex, hi⟩), hf⟩
      else P.nodeHash pp ⟨subtreeHeight, hl⟩ ⟨subtreeIndex, hi⟩ left right
    else left
  else left

/-- The ordinary addressed pair hash on natural indices, including the complete tree's
out-of-rectangle default. This is the recurrence used by unrestricted root recovery. -/
@[expose] def ordinaryNode {PP T X H : Type} {w v : ℕ}
    (P : HashInstance PP T X H h w v) (pp : PP)
    (subtreeHeight subtreeIndex : ℕ) (left right : H) : H :=
  if hl : subtreeHeight < h + 1 then
    if hi : subtreeIndex < 2 ^ h then
      P.nodeHash pp ⟨subtreeHeight, hl⟩ ⟨subtreeIndex, hi⟩ left right
    else left
  else left

/-- The unrestricted complete-tree root recovery is the ordinary addressed climb. -/
theorem recoverRoot_eq_climb {PP T X H : Type} {w v : ℕ}
    (P : HashInstance PP T X H h w v) (pp : PP)
    (e : Fin (2 ^ h)) (xs : Fin v → H) (auth : Fin h → H) :
    P.recoverRoot pp e xs auth =
      PerfectMerkleTree.climb (ordinaryNode P pp) e.val
        (P.leafHash pp e xs) (List.ofFn auth) := by
  unfold HashInstance.recoverRoot HashInstance.nodeExtension ordinaryNode
  rfl

/-- Mixed-tree digest of the subtree at a natural height and index. -/
@[expose] def subtreeRoot {PP T X H : Type} {w v : ℕ}
    (P : HashInstance PP T X H h w v) (I : Interval h) (pp : PP)
    (xs : Fin (2 ^ h) → Fin v → H) (fillers : Fillers I H)
    (subtreeHeight subtreeIndex : ℕ) : H :=
  PerfectMerkleTree.merkleRoot (leaf P I pp xs fillers) (node P I pp fillers)
    subtreeHeight subtreeIndex

/-- Public root of the mixed tree. -/
@[expose] def root {PP T X H : Type} {w v : ℕ}
    (P : HashInstance PP T X H h w v) (I : Interval h) (pp : PP)
    (xs : Fin (2 ^ h) → Fin v → H) (fillers : Fillers I H) : H :=
  subtreeRoot P I pp xs fillers h 0

/-- Leaf-first authentication path in the mixed tree. -/
@[expose] def authPath {PP T X H : Type} {w v : ℕ}
    (P : HashInstance PP T X H h w v) (I : Interval h) (pp : PP)
    (xs : Fin (2 ^ h) → Fin v → H) (fillers : Fillers I H)
    (e : Fin (2 ^ h)) : Fin h → H :=
  fun z => (PerfectMerkleTree.authPath (leaf P I pp xs fillers)
    (node P I pp fillers) e h)[z.val]'(by simp)

/-- In a full interval, each legal leaf is the ordinary hashed endpoint vector. -/
theorem leaf_full {PP T X H : Type} {w v : ℕ}
    (P : HashInstance PP T X H h w v) (pp : PP)
    (xs : Fin (2 ^ h) → Fin v → H) (fillers : Fillers (Interval.full h) H)
    (e : Fin (2 ^ h)) :
    leaf P (Interval.full h) pp xs fillers e.val = P.leafHash pp e (xs e) := by
  simp [leaf, e.isLt, Subtree.full_not_isInactiveFrontier]

/-- In a full interval, each reachable internal address uses the ordinary pair hash. -/
theorem node_full {PP T X H : Type} {w v : ℕ}
    (P : HashInstance PP T X H h w v) (pp : PP)
    (fillers : Fillers (Interval.full h) H) (subtreeHeight subtreeIndex : ℕ)
    (hl : subtreeHeight ≤ h) (hi : (subtreeIndex + 1) * 2 ^ subtreeHeight ≤ 2 ^ h)
    (left right : H) :
    node P (Interval.full h) pp fillers subtreeHeight subtreeIndex left right =
      P.nodeHash pp ⟨subtreeHeight, by omega⟩
        ⟨subtreeIndex, (PerfectMerkleTree.subtree_legal hl hi).2⟩ left right := by
  have hl' : subtreeHeight < h + 1 := by omega
  have hi' := (PerfectMerkleTree.subtree_legal hl hi).2
  simp [node, hl', hi', Subtree.full_not_isInactiveFrontier]

/-- At the full interval, `root` equals `HashInstance.merkleRoot` on the same endpoint array. -/
theorem root_full {PP T X H : Type} {w v : ℕ}
    (P : HashInstance PP T X H h w v) (pp : PP)
    (xs : Fin (2 ^ h) → Fin v → H) (fillers : Fillers (Interval.full h) H) :
    root P (Interval.full h) pp xs fillers = P.merkleRoot pp xs := by
  unfold root subtreeRoot HashInstance.merkleRoot
  apply PerfectMerkleTree.root_extension_independent _ _ _ _ h h 0 le_rfl (by simp)
  · intro i hi
    simpa [HashInstance.leafExtension, hi] using leaf_full P pp xs fillers ⟨i, hi⟩
  · intro j hj hle i hi l r
    have hj' : j < h + 1 := by omega
    have hi' := (PerfectMerkleTree.subtree_legal hle hi).2
    simpa [HashInstance.nodeExtension, hj', hi'] using
      node_full P pp fillers j i hle hi l r

/-- At the full interval, `authPath` equals `HashInstance.authPath` for every epoch. -/
theorem authPath_full {PP T X H : Type} {w v : ℕ}
    (P : HashInstance PP T X H h w v) (pp : PP)
    (xs : Fin (2 ^ h) → Fin v → H) (fillers : Fillers (Interval.full h) H)
    (e : Fin (2 ^ h)) :
    authPath P (Interval.full h) pp xs fillers e = P.authPath pp xs e := by
  have heq := PerfectMerkleTree.authPath_extension_independent
    (leaf P (Interval.full h) pp xs fillers) (P.leafExtension pp xs)
    (node P (Interval.full h) pp fillers) (P.nodeExtension pp) h e
    (by intro i hi
        simpa [HashInstance.leafExtension, hi] using leaf_full P pp xs fillers ⟨i, hi⟩)
    (by intro j hj hle i hi l r
        have hj' : j < h + 1 := by omega
        have hi' := (PerfectMerkleTree.subtree_legal hle hi).2
        simpa [HashInstance.nodeExtension, hj', hi'] using
          node_full P pp fillers j i hle hi l r)
  funext z
  unfold authPath HashInstance.authPath
  simp only [heq]

end GXMSS.IntervalMerkle
