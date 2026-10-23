/-
Copyright (c) 2026 Tom Wambsgans. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Wambsgans
-/

module

public import HashSig.SLHDSA.SHAKE128s.Proof.HashSeparation
public import HashSig.SLHDSA.SHAKE128s.Proof.CanonicalGraph.Nodes

/-!
# Every structural address is in bounds

`HashSeparation.WithinBounds` is the loose rectangle inside which a message input cannot be
mistaken for a structural one: layer below `2 ^ 3`, tree below `2 ^ 54`, key pair below
`2 ^ 9`, chain or height below `2 ^ 6`, hash or index below `2 ^ 16`. It is a fact about the
scheme's parameters rather than about anything probabilistic, so `withinBounds_structural`
supplies it wherever a message input has to be separated from a structural one.

It holds, with room, and the reason is that the canonical nodes carry their own bounds: a
`Tree` has `Fin layers` and `Fin (2 ^ (totalHeight - subtreeHeight))`, a key's leaf has
`Fin (2 ^ subtreeHeight)`, a chain index `Fin chains`, a chain step `Fin (w - 1)`. At the
standard parameters those are `7 < 8`, `2 ^ 54`, `512 = 2 ^ 9`, `35 < 64` and `15 < 2 ^ 16`.
The widest is the FORS node index, `forsTrees * 2 ^ forsHeight = 57344`, still under `2 ^ 16`.

So nothing here is a near miss except the key-pair field, which is exactly `2 ^ 9` and fits
because the bound is strict on an index that is strictly below it.
-/

@[expose] public section

namespace SlhDsaSecurity

open CanonicalGraph HashSeparation

private theorem ofNat_toNat_of_lt {width value : Nat} (h : value < 2 ^ width) :
    (BitVec.ofNat width value).toNat = value := by
  simp only [BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt h

/-- **Every canonical node's address lies in the separation rectangle.** -/
theorem withinBounds_structural (parent : StructuralNode) : WithinBounds parent.address := by
  have hlayer : ∀ tree : Tree, (BitVec.ofNat 32 tree.layer.val).toNat < 2 ^ 3 := by
    intro tree
    rw [ofNat_toNat_of_lt (by have := tree.layer.isLt; simp only [layers] at this; omega)]
    have := tree.layer.isLt
    simp only [layers] at this
    omega
  have htree : ∀ tree : Tree, (BitVec.ofNat 96 tree.tree.val).toNat < 2 ^ 54 := by
    intro tree
    have hlt : tree.tree.val < 2 ^ 54 := by
      have := tree.tree.isLt
      simpa only [totalHeight, subtreeHeight] using this
    rw [ofNat_toNat_of_lt (by omega)]
    exact hlt
  have hleaf : ∀ leaf : Fin (2 ^ subtreeHeight), (BitVec.ofNat 32 leaf.val).toNat < 2 ^ 9 := by
    intro leaf
    have hlt : leaf.val < 2 ^ 9 := by simpa only [subtreeHeight] using leaf.isLt
    rw [ofNat_toNat_of_lt (by omega)]
    exact hlt
  cases parent with
  | wotsPrf key chain =>
    simp only [WithinBounds, StructuralNode.address, Tree.address, WotsKey.address,
      Hypertree.address, Merkle.wotsAddress,
      Wots.secretAddress,
      Address.setTypeAndClear]
    refine ⟨hlayer key.tree, htree key.tree, hleaf key.leaf, ?_, by simp⟩
    have hlt : chain.val < 2 ^ 6 := by
      have := chain.isLt
      simp only [chains, messageDigits, checksumDigits, n, winternitzBits] at this
      omega
    rw [ofNat_toNat_of_lt (by omega)]
    exact hlt
  | wotsHash key chain step =>
    simp only [WithinBounds, StructuralNode.address, Tree.address, WotsKey.address,
      Hypertree.address, Merkle.wotsAddress,
      Address.setTypeAndClear]
    refine ⟨hlayer key.tree, htree key.tree, hleaf key.leaf, ?_, ?_⟩
    · have hlt : chain.val < 2 ^ 6 := by
        have := chain.isLt
        simp only [chains, messageDigits, checksumDigits, n, winternitzBits] at this
        omega
      rw [ofNat_toNat_of_lt (by omega)]
      exact hlt
    · have hlt : step.val < 2 ^ 16 := by
        have := step.isLt
        simp only [w, winternitzBits] at this
        omega
      rw [ofNat_toNat_of_lt (by omega)]
      exact hlt
  | wotsPk key =>
    simp only [WithinBounds, StructuralNode.address, Tree.address, WotsKey.address,
      Hypertree.address, Merkle.wotsAddress,
      Wots.publicKeyAddress,
      Address.setTypeAndClear]
    exact ⟨hlayer key.tree, htree key.tree, hleaf key.leaf, by simp, by simp⟩
  | tree location height index =>
    simp only [WithinBounds, StructuralNode.address, Tree.address,
      Hypertree.address, Merkle.nodeAddress,
      Address.setTypeAndClear]
    refine ⟨hlayer location, htree location, by simp, ?_, ?_⟩
    · have hlt : height.val + 1 < 2 ^ 6 := by
        have := height.isLt
        simp only [subtreeHeight] at this
        omega
      rw [ofNat_toNat_of_lt (by omega)]
      exact hlt
    · have hlt : index.val < 2 ^ 16 := by
        have := index.isLt
        have hle : 2 ^ (subtreeHeight - (height.val + 1)) ≤ 2 ^ 16 :=
          Nat.pow_le_pow_right (by norm_num) (by simp only [subtreeHeight]; omega)
        omega
      rw [ofNat_toNat_of_lt (by omega)]
      exact hlt
  | forsPrf key index =>
    simp only [WithinBounds, StructuralNode.address,
      ForsKey.address, Hypertree.address,
      Fors.secretAddress,
      Address.setTypeAndClear]
    refine ⟨by simp, ?_, hleaf key.leaf, by simp, ?_⟩
    · have hlt : key.tree.val < 2 ^ 54 := by
        have := key.tree.isLt
        simpa only [totalHeight, subtreeHeight] using this
      rw [ofNat_toNat_of_lt (by omega)]
      exact hlt
    · have hlt : index.val < 2 ^ 16 := by
        have := index.isLt
        simp only [forsTrees, forsHeight] at this
        omega
      rw [ofNat_toNat_of_lt (by omega)]
      exact hlt
  | forsTree key height index =>
    simp only [WithinBounds, StructuralNode.address,
      ForsKey.address, Hypertree.address,
      Fors.nodeAddress,
      Address.setTypeAndClear]
    refine ⟨by simp, ?_, hleaf key.leaf, ?_, ?_⟩
    · have hlt : key.tree.val < 2 ^ 54 := by
        have := key.tree.isLt
        simpa only [totalHeight, subtreeHeight] using this
      rw [ofNat_toNat_of_lt (by omega)]
      exact hlt
    · have hlt : height.val < 2 ^ 6 := by
        have := height.isLt
        simp only [forsHeight] at this
        omega
      rw [ofNat_toNat_of_lt (by omega)]
      exact hlt
    · have hlt : index.val < 2 ^ 16 := by
        have hle : forsTrees * 2 ^ (forsHeight - height.val) ≤ forsTrees * 2 ^ forsHeight :=
          Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) (by omega))
        have hbound : index.val < forsTrees * 2 ^ forsHeight :=
          lt_of_lt_of_le index.isLt hle
        simp only [forsTrees, forsHeight] at hbound
        omega
      rw [ofNat_toNat_of_lt (by omega)]
      exact hlt
  | forsRoots key =>
    simp only [WithinBounds, StructuralNode.address,
      ForsKey.address, Hypertree.address,
      Address.setTypeAndClear]
    refine ⟨by simp, ?_, hleaf key.leaf, by simp, by simp⟩
    have hlt : key.tree.val < 2 ^ 54 := by
      have := key.tree.isLt
      simpa only [totalHeight, subtreeHeight] using this
    rw [ofNat_toNat_of_lt (by omega)]
    exact hlt

end SlhDsaSecurity
