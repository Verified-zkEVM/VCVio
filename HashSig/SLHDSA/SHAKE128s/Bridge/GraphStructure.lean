/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module
public import HashSig.SLHDSA.Graph.Children
public import HashSig.SLHDSA.SHAKE128s.Proof.CanonicalGraph.Children
public import HashSig.SLHDSA.SHAKE128s.Bridge.Encodings

/-!
# SHAKE-128s structural coordinate equivalences

The parameterized graph has the same complete coordinate domains, ordered dependencies and
ranks as the fixed SHAKE-128s graph. Natural address fields are related through the existing
address conversion. These are structural identifications; no traversal or sampling law is asserted.
-/

public section

namespace SLHDSA.SHAKE128s.Bridge.GraphStructure

local notation "p128" => FIPS205.params.params

/-- Every layer retains the full rectangular tree coordinate domain. -/
@[expose] def treeEquiv : Graph.Tree p128 ≃ CanonicalGraph.Tree where
  toFun tree := ⟨tree.layer, tree.tree⟩
  invFun tree := ⟨tree.layer, tree.tree⟩
  left_inv tree := by cases tree; rfl
  right_inv tree := by cases tree; rfl

/-- WOTS key locations preserve their tree and leaf coordinates. -/
@[expose] def wotsKeyEquiv : Graph.WotsKey p128 ≃ CanonicalGraph.WotsKey where
  toFun key := ⟨treeEquiv key.tree, key.leaf⟩
  invFun key := ⟨treeEquiv.symm key.tree, key.leaf⟩
  left_inv key := by cases key with | mk tree leaf => cases tree; rfl
  right_inv key := by cases key with | mk tree leaf => cases tree; rfl

/-- FORS key locations preserve their bottom tree and key-pair coordinates. -/
@[expose] def forsKeyEquiv : Graph.ForsKey p128 ≃ CanonicalGraph.ForsKey where
  toFun key := ⟨key.tree, key.leaf⟩
  invFun key := ⟨key.tree, key.leaf⟩
  left_inv key := by cases key; rfl
  right_inv key := by cases key; rfl

/-- All seven structural node families retain their exact finite coordinate bounds. -/
@[expose] def structuralEquiv : Graph.StructuralNode p128 ≃ CanonicalGraph.StructuralNode where
  toFun
    | .wotsPrf key chain => .wotsPrf (wotsKeyEquiv key) chain
    | .wotsHash key chain step => .wotsHash (wotsKeyEquiv key) chain step
    | .wotsPk key => .wotsPk (wotsKeyEquiv key)
    | .tree tree height index => .tree (treeEquiv tree) height index
    | .forsPrf key index => .forsPrf (forsKeyEquiv key) index
    | .forsTree key height index => .forsTree (forsKeyEquiv key) height index
    | .forsRoots key => .forsRoots (forsKeyEquiv key)
  invFun
    | .wotsPrf key chain => .wotsPrf (wotsKeyEquiv.symm key) chain
    | .wotsHash key chain step => .wotsHash (wotsKeyEquiv.symm key) chain step
    | .wotsPk key => .wotsPk (wotsKeyEquiv.symm key)
    | .tree tree height index => .tree (treeEquiv.symm tree) height index
    | .forsPrf key index => .forsPrf (forsKeyEquiv.symm key) index
    | .forsTree key height index => .forsTree (forsKeyEquiv.symm key) height index
    | .forsRoots key => .forsRoots (forsKeyEquiv.symm key)
  left_inv node := by cases node <;> simp
  right_inv node := by cases node <;> simp

/-- The separate secret-seed node and every structural node are retained. -/
@[expose] def nodeEquiv : Graph.Node p128 ≃ CanonicalGraph.Node where
  toFun
    | .secretSeed => .secretSeed
    | .structural node => .structural (structuralEquiv node)
  invFun
    | .secretSeed => .secretSeed
    | .structural node => .structural (structuralEquiv.symm node)
  left_inv node := by cases node <;> simp
  right_inv node := by cases node <;> simp

/-- Structural ranks agree, including the positive-height XMSS offset. -/
theorem structuralEquiv_rank (node : Graph.StructuralNode p128) :
    (structuralEquiv node).rank = node.rank := by
  cases node with
  | wotsPrf key chain => rfl
  | wotsHash key chain step => rfl
  | wotsPk key => rfl
  | tree location height index =>
      change 17 + (height.val + 1) = 16 + 2 + height.val
      omega
  | forsPrf key index => rfl
  | forsTree key height index => rfl
  | forsRoots key => rfl

/-- The seed has rank zero and all structural ranks agree. -/
theorem nodeEquiv_rank (node : Graph.Node p128) : (nodeEquiv node).rank = node.rank := by
  cases node with
  | secretSeed => rfl
  | structural node => exact structuralEquiv_rank node

/-- An XMSS node at any valid height preserves its precise structural constructor. -/
theorem structuralEquiv_merkleNode (tree : Graph.Tree p128) (height : Nat)
    (bound : height ≤ (p128).hp) (index : Fin (2 ^ ((p128).hp - height))) :
    structuralEquiv (Graph.merkleNode tree height bound index) =
      CanonicalGraph.merkleNode (treeEquiv tree) height bound index := by
  unfold Graph.merkleNode CanonicalGraph.merkleNode
  by_cases zero : height = 0
  · simp only [dite_eq_left zero]
    rfl
  · simp only [dite_eq_right zero]
    rfl

/-- Ordered left/right XMSS child coordinates preserve their exact bounds. -/
theorem structuralEquiv_merkleChild (tree : Graph.Tree p128) (height : Fin (p128).hp)
    (index : Fin (2 ^ ((p128).hp - (height.val + 1)))) (side : Fin 2) :
    structuralEquiv (Graph.merkleChild tree height index side) =
      CanonicalGraph.merkleChild (treeEquiv tree) height index side :=
  structuralEquiv_merkleNode tree height.val (Nat.le_of_lt height.isLt) _

/-- Ordered FORS child coordinates preserve their global tree offsets. -/
theorem structuralEquiv_forsChild (key : Graph.ForsKey p128) (height : Fin ((p128).a + 1))
    (positive : 0 < height.val) (index : Fin ((p128).k * 2 ^ ((p128).a - height.val)))
    (side : Fin 2) :
    structuralEquiv (Graph.forsChild key height positive index side) =
      CanonicalGraph.forsChild (forsKeyEquiv key) height positive index side := rfl

/-- The complete ordered child list agrees at every structural node. -/
theorem structuralEquiv_children (parent : Graph.StructuralNode p128) :
    (Graph.StructuralNode.children FIPS205.params.valid parent).map nodeEquiv =
      (structuralEquiv parent).children := by
  cases parent with
  | wotsPrf key chain => rfl
  | forsPrf key index => rfl
  | wotsHash key chain step =>
      rw [show structuralEquiv (.wotsHash key chain step) =
        .wotsHash (wotsKeyEquiv key) chain step from rfl]
      by_cases zero : step.val = 0
      · simp only [Graph.StructuralNode.children, CanonicalGraph.StructuralNode.children,
          dite_eq_left zero, List.map_singleton]
        rfl
      · simp only [Graph.StructuralNode.children, CanonicalGraph.StructuralNode.children,
          dite_eq_right zero, List.map_singleton]
        rfl
  | wotsPk key =>
      rw [show structuralEquiv (.wotsPk key) = .wotsPk (wotsKeyEquiv key) from rfl]
      simp only [Graph.StructuralNode.children, CanonicalGraph.StructuralNode.children,
        List.map_ofFn]
      rfl
  | tree location height index =>
      rw [show structuralEquiv (.tree location height index) =
        .tree (treeEquiv location) height index from rfl]
      simp only [Graph.StructuralNode.children, CanonicalGraph.StructuralNode.children,
        List.map_cons, List.map_nil]
      change [CanonicalGraph.Node.structural
        (structuralEquiv (Graph.merkleChild location height index 0)),
        CanonicalGraph.Node.structural
          (structuralEquiv (Graph.merkleChild location height index 1))] = _
      rw [structuralEquiv_merkleChild, structuralEquiv_merkleChild]
  | forsTree key height index =>
      rw [show structuralEquiv (.forsTree key height index) =
        .forsTree (forsKeyEquiv key) height index from rfl]
      by_cases zero : height.val = 0
      · simp only [Graph.StructuralNode.children, CanonicalGraph.StructuralNode.children,
          dite_eq_left zero, List.map_singleton]
        rfl
      · simp only [Graph.StructuralNode.children, CanonicalGraph.StructuralNode.children,
          dite_eq_right zero, List.map_cons, List.map_nil]
        change [CanonicalGraph.Node.structural
          (structuralEquiv (Graph.forsChild key height (by omega) index 0)),
          CanonicalGraph.Node.structural
            (structuralEquiv (Graph.forsChild key height (by omega) index 1))] = _
        rw [structuralEquiv_forsChild, structuralEquiv_forsChild]
  | forsRoots key =>
      rw [show structuralEquiv (.forsRoots key) = .forsRoots (forsKeyEquiv key) from rfl]
      simp only [Graph.StructuralNode.children, CanonicalGraph.StructuralNode.children,
        List.map_ofFn]
      rfl

private theorem merkle_index_bound (height : Nat)
    (index : Fin (2 ^ (9 - height))) : index.val < 512 :=
  index.isLt.trans_le (Nat.pow_le_pow_right (by decide) (Nat.sub_le _ _))

private theorem fors_index_bound (height : Nat)
    (index : Fin (14 * 2 ^ (12 - height))) : index.val < 57344 :=
  index.isLt.trans_le (Nat.mul_le_mul_left _
    (Nat.pow_le_pow_right (by decide) (Nat.sub_le _ _)))

/-- All six natural address fields agree with the existing bit-vector address conversion. -/
theorem structuralEquiv_address (node : Graph.StructuralNode p128) :
    toAdrs (structuralEquiv node).address = node.address := by
  change toAdrs (structuralEquiv.toFun node).address = _
  cases node with
  | tree location height index =>
      have hi := merkle_index_bound (height.val + 1) index
      simp only [structuralEquiv, treeEquiv, toAdrs, Graph.StructuralNode.address,
        CanonicalGraph.StructuralNode.address, CanonicalGraph.Tree.address,
        Merkle.nodeAddress, Hypertree.address, Address.setTypeAndClear, BitVec.toNat_ofNat]
      simp only [layers, totalHeight, subtreeHeight] at *
      apply Adrs.ext <;>
        norm_num [AddressType.toAddrType, AddrType.toCode] at * <;> omega
  | forsTree key height index =>
      have hi := fors_index_bound height.val index
      simp only [structuralEquiv, forsKeyEquiv, toAdrs, Graph.StructuralNode.address,
        CanonicalGraph.StructuralNode.address, CanonicalGraph.ForsKey.address,
        Fors.nodeAddress, Hypertree.address, Address.setTypeAndClear, BitVec.toNat_ofNat]
      simp only [totalHeight, subtreeHeight, forsHeight, forsTrees] at *
      apply Adrs.ext <;>
        norm_num [AddressType.toAddrType, AddrType.toCode] at * <;> omega
  | _ =>
      simp only [structuralEquiv, wotsKeyEquiv, treeEquiv, forsKeyEquiv, toAdrs,
        Graph.StructuralNode.address, CanonicalGraph.StructuralNode.address,
        CanonicalGraph.WotsKey.address, CanonicalGraph.Tree.address,
        CanonicalGraph.ForsKey.address, Wots.secretAddress, Wots.publicKeyAddress,
        Merkle.wotsAddress, Fors.secretAddress, Hypertree.address, Address.setTypeAndClear,
        BitVec.toNat_ofNat]
      all_goals
        simp only [layers, totalHeight, subtreeHeight, forsHeight, forsTrees, chains,
          messageDigits, checksumDigits, n, winternitzBits, w] at *
      all_goals apply Adrs.ext <;>
        norm_num [AddressType.toAddrType, AddrType.toCode] at * <;> omega

end SLHDSA.SHAKE128s.Bridge.GraphStructure
