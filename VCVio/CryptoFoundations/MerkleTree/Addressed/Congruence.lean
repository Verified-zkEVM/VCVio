/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import VCVio.CryptoFoundations.MerkleTree.Addressed.Query

/-!
# Ancestor-local congruence for addressed Merkle openings

Root recovery visits only the ancestors of the selected leaf. Agreement there preserves the
recomputed root and the complete ordered list of node-query inputs under an address rekeying.
No injectivity of the address map is required.
-/

public section

namespace AddressedMerkleTree

/-- Putative recovery depends only on pair hashes along the selected leaf's ancestors. -/
theorem getPutativeRootAddressedWithHash_congr_ancestors {Y : Type*} {s : BinaryTree.Skeleton}
    (node₁ node₂ : BinaryTree.SkeletonInternalIndex s → Y → Y → Y)
    (idx : BinaryTree.SkeletonLeafIndex s) (value : Y)
    (path : List.Vector Y idx.depth)
    (hn : ∀ a, a.IsAncestorOf idx → ∀ l r, node₁ a l r = node₂ a l r) :
    AddressedMerkleTree.getPutativeRootAddressedWithHash node₁ idx value path =
      AddressedMerkleTree.getPutativeRootAddressedWithHash node₂ idx value path := by
  induction idx with
  | ofLeaf => rfl
  | ofLeft sub ih =>
    simp only [AddressedMerkleTree.getPutativeRootAddressedWithHash]
    rw [ih (fun a => node₁ (.ofLeft a)) (fun a => node₂ (.ofLeft a)) path.tail
      (by intro a ha l r; exact hn (.ofLeft a) (by simpa using ha) l r)]
    exact hn .ofInternal (by simp) _ _
  | ofRight sub ih =>
    simp only [AddressedMerkleTree.getPutativeRootAddressedWithHash]
    rw [ih (fun a => node₁ (.ofRight a)) (fun a => node₂ (.ofRight a)) path.tail
      (by intro a ha l r; exact hn (.ofRight a) (by simpa using ha) l r)]
    exact hn .ofInternal (by simp) _ _

/-- Rekeying an opening preserves the ordered query inputs when keys and hashes agree
at every visited ancestor. -/
theorem openingQueries_rekey {A B Y : Type*} {s : BinaryTree.Skeleton}
    (key₁ : BinaryTree.SkeletonInternalIndex s → A) (hash₁ : A → Y → Y → Y)
    (key₂ : BinaryTree.SkeletonInternalIndex s → B) (hash₂ : B → Y → Y → Y)
    (rekey : A → B) (idx : BinaryTree.SkeletonLeafIndex s) (leaf : Y)
    (path : List.Vector Y idx.depth)
    (hk : ∀ a, a.IsAncestorOf idx → rekey (key₁ a) = key₂ a)
    (hn : ∀ a, a.IsAncestorOf idx → ∀ l r,
      hash₁ (key₁ a) l r = hash₂ (key₂ a) l r) :
    (AddressedMerkleTree.openingQueries key₁ hash₁ idx leaf path).map
      (fun q => (⟨rekey q.address, q.input⟩ : AddressedMerkleTree.NodeQuery B Y)) =
      AddressedMerkleTree.openingQueries key₂ hash₂ idx leaf path := by
  induction idx with
  | ofLeaf => rfl
  | ofLeft idx ih =>
    have hc := getPutativeRootAddressedWithHash_congr_ancestors
      (fun a => hash₁ (key₁ (.ofLeft a))) (fun a => hash₂ (key₂ (.ofLeft a)))
      idx leaf path.tail (by intro a ha; exact hn (.ofLeft a) (by simpa using ha))
    simp only [AddressedMerkleTree.openingQueries, List.map_cons]
    rw [hc, hk .ofInternal (by simp)]
    congr 1
    exact ih _ _ path.tail
      (by intro a ha; exact hk (.ofLeft a) (by simpa using ha))
      (by intro a ha; exact hn (.ofLeft a) (by simpa using ha))
  | ofRight idx ih =>
    have hc := getPutativeRootAddressedWithHash_congr_ancestors
      (fun a => hash₁ (key₁ (.ofRight a))) (fun a => hash₂ (key₂ (.ofRight a)))
      idx leaf path.tail (by intro a ha; exact hn (.ofRight a) (by simpa using ha))
    simp only [AddressedMerkleTree.openingQueries, List.map_cons]
    rw [hc, hk .ofInternal (by simp)]
    congr 1
    exact ih _ _ path.tail
      (by intro a ha; exact hk (.ofRight a) (by simpa using ha))
      (by intro a ha; exact hn (.ofRight a) (by simpa using ha))

end AddressedMerkleTree
