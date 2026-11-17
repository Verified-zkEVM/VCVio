/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import VCVio.CryptoFoundations.MerkleTree.Addressed.Query

/-!
# Honest addressed opening queries

An honest opening queries the stored ordered children of visited ancestors. Address keys may
repeat: provenance identifies the actual ancestor, without assuming address-map injectivity.
-/

public section

namespace AddressedMerkleTree
open BinaryTree
variable {Y : Type*}

/-- Every query in an honest opening contains the stored ordered children of a visited ancestor. -/
theorem mem_openingQueries_honestTree {Address : Type*} {s : Skeleton}
    (addressKey : SkeletonInternalIndex s → Address)
    (nodeHash : Address → Y → Y → Y) (ld : LeafData Y s)
    (idx : SkeletonLeafIndex s) (query : NodeQuery Address Y)
    (hquery : query ∈ openingQueries addressKey nodeHash idx (ld.get idx)
      (InductiveMerkleTree.generateProof (buildMerkleTreeAddressedWithHash ld
        (fun a l r => nodeHash (addressKey a) l r)) idx)) :
    ∃ a : SkeletonInternalIndex s, a.IsAncestorOf idx ∧
      query.address = addressKey a ∧
      query.input = childPairAt
        (buildMerkleTreeAddressedWithHash ld (fun a l r => nodeHash (addressKey a) l r)) a := by
  induction idx with
  | ofLeaf => simp [openingQueries] at hquery
  | ofLeft idx ih =>
      cases ld with
      | internal left right =>
          let leftTree := buildMerkleTreeAddressedWithHash left
            (fun a l r => nodeHash (addressKey (.ofLeft a)) l r)
          let rightTree := buildMerkleTreeAddressedWithHash right
            (fun a l r => nodeHash (addressKey (.ofRight a)) l r)
          have hsub := addressed_functional_completeness idx left
            (fun a l r => nodeHash (addressKey (.ofLeft a)) l r)
          change query ∈
            ((⟨addressKey .ofInternal, (getPutativeRootAddressedWithHash
                (fun a => nodeHash (addressKey (.ofLeft a))) idx (left.get idx)
                (InductiveMerkleTree.generateProof leftTree idx), rightTree.getRootValue)⟩ :
              NodeQuery Address Y) ::
              openingQueries (fun a => addressKey (.ofLeft a)) nodeHash idx (left.get idx)
                (InductiveMerkleTree.generateProof leftTree idx)) at hquery
          rw [hsub] at hquery
          simp only [List.mem_cons] at hquery
          rcases hquery with hquery | hquery
          · subst query
            exact ⟨.ofInternal, trivial, rfl, rfl⟩
          · obtain ⟨a, hancestor, haddress, hinput⟩ :=
              ih (ld := left) (addressKey := fun a => addressKey (.ofLeft a)) hquery
            exact ⟨.ofLeft a, hancestor, haddress, hinput⟩
  | ofRight idx ih =>
      cases ld with
      | internal left right =>
          let leftTree := buildMerkleTreeAddressedWithHash left
            (fun a l r => nodeHash (addressKey (.ofLeft a)) l r)
          let rightTree := buildMerkleTreeAddressedWithHash right
            (fun a l r => nodeHash (addressKey (.ofRight a)) l r)
          have hsub := addressed_functional_completeness idx right
            (fun a l r => nodeHash (addressKey (.ofRight a)) l r)
          change query ∈
            ((⟨addressKey .ofInternal, (leftTree.getRootValue, getPutativeRootAddressedWithHash
                (fun a => nodeHash (addressKey (.ofRight a))) idx (right.get idx)
                (InductiveMerkleTree.generateProof rightTree idx))⟩ : NodeQuery Address Y) ::
              openingQueries (fun a => addressKey (.ofRight a)) nodeHash idx (right.get idx)
                (InductiveMerkleTree.generateProof rightTree idx)) at hquery
          rw [hsub] at hquery
          simp only [List.mem_cons] at hquery
          rcases hquery with hquery | hquery
          · subst query
            exact ⟨.ofInternal, trivial, rfl, rfl⟩
          · obtain ⟨a, hancestor, haddress, hinput⟩ :=
              ih (ld := right) (addressKey := fun a => addressKey (.ofRight a)) hquery
            exact ⟨.ofRight a, hancestor, haddress, hinput⟩

end AddressedMerkleTree
