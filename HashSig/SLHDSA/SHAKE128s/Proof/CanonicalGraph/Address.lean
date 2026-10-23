/-
Copyright (c) 2026 Tom Wambsgans. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Wambsgans
-/

module

public import HashSig.SLHDSA.SHAKE128s.Proof.CanonicalGraph.Nodes
public import Mathlib.Tactic.NormNum

/-!
# Injectivity of canonical structural addresses

Canonical structural addresses identify their node coordinates uniquely. Both a structural node
and an address are flattened to a tuple of six numeric coordinates; the two flattenings agree on
every canonical node, and the node flattening is injective, so `StructuralNode.address_injective`
follows.
-/

@[expose] public section

namespace SlhDsaSecurity.CanonicalGraph

/-- Six numeric address coordinates: layer, tree, type, key pair, chain or height, and hash or
index. -/
private abbrev Code := Nat × Nat × AddressType × Nat × Nat × Nat

/-- The coordinates of a structural node, read from its typed fields. -/
private def code : StructuralNode → Code
  | .wotsPrf key chain =>
      (key.tree.layer.val, key.tree.tree.val, .wotsPrf, key.leaf.val, chain.val, 0)
  | .wotsHash key chain step =>
      (key.tree.layer.val, key.tree.tree.val, .wotsHash, key.leaf.val, chain.val, step.val)
  | .wotsPk key => (key.tree.layer.val, key.tree.tree.val, .wotsPk, key.leaf.val, 0, 0)
  | .tree location height index =>
      (location.layer.val, location.tree.val, .tree, 0, height.val + 1, index.val)
  | .forsPrf key index => (0, key.tree.val, .forsPrf, key.leaf.val, 0, index.val)
  | .forsTree key height index =>
      (0, key.tree.val, .forsTree, key.leaf.val, height.val, index.val)
  | .forsRoots key => (0, key.tree.val, .forsRoots, key.leaf.val, 0, 0)

/-- The coordinates of an address, read from its numeric fields. -/
private def addressCode (address : Address) : Code :=
  (address.layer.toNat, address.tree.toNat, address.kind, address.keyPair.toNat,
    address.chainOrHeight.toNat, address.hashOrIndex.toNat)

private theorem tree_index_bound (height : Nat)
    (index : Fin (2 ^ (subtreeHeight - height))) : index.val < 2 ^ subtreeHeight :=
  index.isLt.trans_le (Nat.pow_le_pow_right (by decide) (Nat.sub_le _ _))

private theorem fors_index_bound (height : Nat)
    (index : Fin (forsTrees * 2 ^ (forsHeight - height))) :
    index.val < forsTrees * 2 ^ forsHeight :=
  index.isLt.trans_le (Nat.mul_le_mul_left _
    (Nat.pow_le_pow_right (by decide) (Nat.sub_le _ _)))

private theorem zero32 : BitVec.toNat (0 : BitVec 32) = 0 := rfl

private theorem addressCode_eq (node : StructuralNode) : addressCode node.address = code node := by
  cases node with
  | tree tree height index =>
      have hi := tree_index_bound (height.val + 1) index
      simp only [addressCode, StructuralNode.address, code, Tree.address,
        Merkle.nodeAddress, Hypertree.address, Address.setTypeAndClear,
        BitVec.toNat_ofNat, zero32, Prod.mk.injEq]
      simp only [subtreeHeight, layers, totalHeight] at *
      norm_num at *
      omega
  | forsTree key height index =>
      have hi := fors_index_bound height.val index
      simp only [addressCode, StructuralNode.address, code, ForsKey.address,
        Fors.nodeAddress, Hypertree.address, Address.setTypeAndClear,
        BitVec.toNat_ofNat, Prod.mk.injEq]
      simp only [subtreeHeight, totalHeight, forsHeight, forsTrees] at *
      norm_num at *
      omega
  | _ =>
      simp only [addressCode, StructuralNode.address, code, WotsKey.address, Tree.address,
        ForsKey.address, Wots.secretAddress, Wots.publicKeyAddress, Merkle.wotsAddress,
        Fors.secretAddress, Hypertree.address, Address.setTypeAndClear,
        BitVec.toNat_ofNat, zero32, Prod.mk.injEq]
      simp only [subtreeHeight, layers, totalHeight, forsHeight, forsTrees,
        chains, messageDigits, checksumDigits, n, winternitzBits, w] at *
      norm_num at *
      omega

private theorem tree_ext (left right : Tree)
    (hlayer : left.layer = right.layer) (htree : left.tree = right.tree) : left = right := by
  cases left; cases right; simp_all

private theorem wots_ext (left right : WotsKey)
    (hlayer : left.tree.layer = right.tree.layer) (htree : left.tree.tree = right.tree.tree)
    (hleaf : left.leaf = right.leaf) : left = right := by
  have := tree_ext left.tree right.tree hlayer htree
  cases left; cases right; simp_all

private theorem fors_ext (left right : ForsKey)
    (htree : left.tree = right.tree) (hleaf : left.leaf = right.leaf) : left = right := by
  cases left; cases right; simp_all

private theorem code_injective : Function.Injective code := by
  intro left right h
  cases left <;> cases right <;> simp [code] at h
  all_goals
    simp_all only [Fin.val_inj]
    aesop (add safe apply [tree_ext, wots_ext, fors_ext, Fin.ext])

/-- Distinct structural nodes have distinct addresses. -/
theorem StructuralNode.address_injective : Function.Injective StructuralNode.address := by
  intro left right h
  apply code_injective
  simpa only [addressCode_eq] using congrArg addressCode h

end SlhDsaSecurity.CanonicalGraph
