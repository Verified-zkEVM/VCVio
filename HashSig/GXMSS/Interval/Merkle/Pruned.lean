/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import HashSig.GXMSS.Interval.Merkle.Active

/-!
# Pruned interval Merkle recursion

The direct recursion returns a stored digest at each inactive frontier without descending.
It agrees with the mixed engine at every address and preserves shifted subtree coordinates.
-/

public section

namespace GXMSS.IntervalMerkle

variable {h : ℕ}

/-- The digest stored at a legal maximal inactive address. -/
@[expose] def frontierValue {H : Type} (I : Interval h) (fillers : Fillers I H)
    (subtreeHeight subtreeIndex : ℕ)
    (hf : Subtree.IsInactiveFrontier I subtreeHeight subtreeIndex) : H :=
  fillers ⟨(⟨subtreeHeight, Nat.lt_succ_of_le hf.height_le⟩,
    ⟨subtreeIndex, (PerfectMerkleTree.subtree_legal hf.height_le hf.span_le).2⟩), hf⟩

/-- A direct partial-tree recursion. At a maximal inactive node it returns the stored filler
without descending; otherwise it follows the ordinary hashed-leaf and pair-hash recursion. -/
@[expose] def prunedRoot {PP T X H : Type} {w v : ℕ}
    (P : HashInstance PP T X H h w v) (I : Interval h) (pp : PP)
    (xs : Fin (2 ^ h) → Fin v → H) (fillers : Fillers I H) : (subtreeHeight subtreeIndex : ℕ) → H
  | 0, subtreeIndex =>
      if hf : Subtree.IsInactiveFrontier I 0 subtreeIndex then
        frontierValue I fillers 0 subtreeIndex hf
      else leaf P I pp xs fillers subtreeIndex
  | subtreeHeight + 1, subtreeIndex =>
      if hf : Subtree.IsInactiveFrontier I (subtreeHeight + 1) subtreeIndex then
        frontierValue I fillers (subtreeHeight + 1) subtreeIndex hf
      else node P I pp fillers (subtreeHeight + 1) subtreeIndex
        (prunedRoot P I pp xs fillers subtreeHeight (2 * subtreeIndex))
        (prunedRoot P I pp xs fillers subtreeHeight (2 * subtreeIndex + 1))

/-- The direct pruned recursion and the addressed perfect-tree engine have identical digests
at every height and address. -/
theorem prunedRoot_eq_subtreeRoot {PP T X H : Type} {w v : ℕ}
    (P : HashInstance PP T X H h w v) (I : Interval h) (pp : PP)
    (xs : Fin (2 ^ h) → Fin v → H) (fillers : Fillers I H)
    (subtreeHeight subtreeIndex : ℕ) :
    prunedRoot P I pp xs fillers subtreeHeight subtreeIndex =
      subtreeRoot P I pp xs fillers subtreeHeight subtreeIndex := by
  induction subtreeHeight generalizing subtreeIndex with
  | zero =>
      by_cases hf : Subtree.IsInactiveFrontier I 0 subtreeIndex
      · simp [prunedRoot, hf, frontierValue,
          subtreeRoot_isInactiveFrontier P I pp xs fillers 0 subtreeIndex hf]
      · simp [prunedRoot, hf, subtreeRoot]
  | succ subtreeHeight ih =>
      by_cases hf : Subtree.IsInactiveFrontier I (subtreeHeight + 1) subtreeIndex
      · simp [prunedRoot, hf, frontierValue,
          subtreeRoot_isInactiveFrontier P I pp xs fillers (subtreeHeight + 1) subtreeIndex hf]
      · simp only [prunedRoot, dite_eq_right hf, subtreeRoot,
          PerfectMerkleTree.merkleRoot_succ]
        rw [ih (2 * subtreeIndex), ih (2 * subtreeIndex + 1)]
        rfl

/-- Every authentication entry is the corresponding pruned sibling-subtree digest. -/
theorem authPath_eq_prunedRoot {PP T X H : Type} {w v : ℕ}
    (P : HashInstance PP T X H h w v) (I : Interval h) (pp : PP)
    (xs : Fin (2 ^ h) → Fin v → H) (fillers : Fillers I H)
    (e : Fin (2 ^ h)) (z : Fin h) :
    authPath P I pp xs fillers e z = prunedRoot P I pp xs fillers z.val
      (PerfectMerkleTree.sibling (e.val / 2 ^ z.val)) := by
  rw [authPath_eq_subtreeRoot, prunedRoot_eq_subtreeRoot]

/-- A complete subtree can be used as a leaf in a higher perfect tree, with original
address levels retained by shifting each parent hash height. -/
theorem subtreeRoot_shift {PP T X H : Type} {w v : ℕ}
    (P : HashInstance PP T X H h w v) (I : Interval h) (pp : PP)
    (xs : Fin (2 ^ h) → Fin v → H) (fillers : Fillers I H)
    (z k t : ℕ) :
    subtreeRoot P I pp xs fillers (z + k) t =
      PerfectMerkleTree.merkleRoot
        (fun i => subtreeRoot P I pp xs fillers z i)
        (fun j i => node P I pp fillers (z + j) i) k t :=
  PerfectMerkleTree.merkleRoot_add (leaf P I pp xs fillers) (node P I pp fillers) z k t

end GXMSS.IntervalMerkle
