/-
Copyright (c) 2026 Tom Wambsgans, Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Wambsgans, Alexander Hicks
-/

module
public import HashSig.SLHDSA.Graph.Structure
import Mathlib.Tactic.NormNum

/-!
# Representability of structural graph addresses

Natural structural coordinates distinguish all seven node families. Explicit field capacities
make their full 32-byte address encodings canonical and injective. These capacities are local
encoding conditions, separate from mathematical parameter validity and oracle-answer lengths.
-/

public section

namespace SLHDSA.Graph

variable {p : Params}

/-- Capacities for every field used by the complete structural address domains. -/
structure Widths (p : Params) : Prop where
  /-- The full layer domain fits its field. -/
  layers : p.d ≤ 2 ^ 32
  /-- The full tree rectangle fits its tree field. -/
  trees : 2 ^ (p.h - p.hp) ≤ 2 ^ 96
  /-- Every key-pair leaf fits its field. -/
  leaves : 2 ^ p.hp ≤ 2 ^ 32
  /-- All WOTS chain indices fit their field. -/
  chains : p.len ≤ 2 ^ 32
  /-- Every WOTS hash step fits its field. -/
  steps : p.w ≤ 2 ^ 32
  /-- Positive XMSS heights, including the root, fit their field. -/
  xmssHeight : p.hp < 2 ^ 32
  /-- FORS heights, including the root, fit their field. -/
  forsHeight : p.a < 2 ^ 32
  /-- Every global FORS leaf index fits its field. -/
  forsIndex : p.k * 2 ^ p.a ≤ 2 ^ 32

private theorem tree_ext (left right : Tree p)
    (hlayer : left.layer = right.layer) (htree : left.tree = right.tree) : left = right := by
  cases left; cases right; simp_all

private theorem wots_ext (left right : WotsKey p)
    (hlayer : left.tree.layer = right.tree.layer) (htree : left.tree.tree = right.tree.tree)
    (hleaf : left.leaf = right.leaf) : left = right := by
  have := tree_ext left.tree right.tree hlayer htree
  cases left; cases right; simp_all

private theorem fors_ext (left right : ForsKey p)
    (htree : left.tree = right.tree) (hleaf : left.leaf = right.leaf) : left = right := by
  cases left; cases right; simp_all

/-- Natural structural addresses determine their constructor and all finite coordinates. -/
theorem StructuralNode.address_injective :
    Function.Injective (StructuralNode.address (p := p)) := by
  intro left right equal
  cases left <;> cases right <;> simp [StructuralNode.address] at equal
  all_goals
    aesop (add safe forward [Fin.ext]) (add safe apply [tree_ext, wots_ext, fors_ext, Fin.ext])

private theorem merkle_index_bound (height : Nat) (index : Fin (2 ^ (p.hp - height))) :
    index.val < 2 ^ p.hp :=
  index.isLt.trans_le (Nat.pow_le_pow_right (by decide) (Nat.sub_le _ _))

private theorem fors_index_bound (height : Nat)
    (index : Fin (p.k * 2 ^ (p.a - height))) : index.val < p.k * 2 ^ p.a :=
  index.isLt.trans_le (Nat.mul_le_mul_left _
    (Nat.pow_le_pow_right (by decide) (Nat.sub_le _ _)))

private theorem address_bounds (widths : Widths p) (node : StructuralNode p) :
    node.address.layer < 2 ^ 32 ∧ node.address.tree < 2 ^ 96 ∧
      node.address.type < 2 ^ 32 ∧ node.address.word1 < 2 ^ 32 ∧
      node.address.word2 < 2 ^ 32 ∧ node.address.word3 < 2 ^ 32 := by
  cases node with
  | wotsPrf key chain =>
      exact ⟨key.tree.layer.isLt.trans_le widths.layers,
        key.tree.tree.isLt.trans_le widths.trees,
        by norm_num [StructuralNode.address], key.leaf.isLt.trans_le widths.leaves,
        chain.isLt.trans_le widths.chains,
        by norm_num [StructuralNode.address]⟩
  | wotsHash key chain step =>
      exact ⟨key.tree.layer.isLt.trans_le widths.layers,
        key.tree.tree.isLt.trans_le widths.trees,
        by norm_num [StructuralNode.address], key.leaf.isLt.trans_le widths.leaves,
        chain.isLt.trans_le widths.chains,
        step.isLt.trans_le ((Nat.sub_le _ _).trans widths.steps)⟩
  | wotsPk key =>
      exact ⟨key.tree.layer.isLt.trans_le widths.layers,
        key.tree.tree.isLt.trans_le widths.trees,
        by norm_num [StructuralNode.address], key.leaf.isLt.trans_le widths.leaves,
        by norm_num [StructuralNode.address],
        by norm_num [StructuralNode.address]⟩
  | tree location height index =>
      exact ⟨location.layer.isLt.trans_le widths.layers,
        location.tree.isLt.trans_le widths.trees,
        by norm_num [StructuralNode.address],
        by norm_num [StructuralNode.address],
        (Nat.succ_le_of_lt height.isLt).trans_lt widths.xmssHeight,
        (merkle_index_bound (height.val + 1) index).trans_le widths.leaves⟩
  | forsPrf key index =>
      exact ⟨by norm_num [StructuralNode.address], key.tree.isLt.trans_le widths.trees,
        by norm_num [StructuralNode.address],
        key.leaf.isLt.trans_le widths.leaves,
        by norm_num [StructuralNode.address],
        index.isLt.trans_le widths.forsIndex⟩
  | forsTree key height index =>
      exact ⟨by norm_num [StructuralNode.address], key.tree.isLt.trans_le widths.trees,
        by norm_num [StructuralNode.address],
        key.leaf.isLt.trans_le widths.leaves,
        (Nat.le_of_lt_succ height.isLt).trans_lt widths.forsHeight,
        (fors_index_bound height.val index).trans_le widths.forsIndex⟩
  | forsRoots key =>
      exact ⟨by norm_num [StructuralNode.address], key.tree.isLt.trans_le widths.trees,
        by norm_num [StructuralNode.address],
        key.leaf.isLt.trans_le widths.leaves,
        by norm_num [StructuralNode.address],
        by norm_num [StructuralNode.address]⟩

/-- Local width certificates make every structural address a canonical full FIPS address. -/
theorem StructuralNode.address_isCanonical (widths : Widths p) (node : StructuralNode p) :
    node.address.isCanonical = true := by
  obtain ⟨hlayer, htree, htype, hword1, hword2, hword3⟩ := address_bounds widths node
  have layerFits : Adrs.Fits 4 node.address.layer = true := Adrs.fits_iff.mpr hlayer
  have treeFits : Adrs.Fits 12 node.address.tree = true := Adrs.fits_iff.mpr htree
  have typeFits : Adrs.Fits 4 node.address.type = true := Adrs.fits_iff.mpr htype
  have word1Fits : Adrs.Fits 4 node.address.word1 = true := Adrs.fits_iff.mpr hword1
  have word2Fits : Adrs.Fits 4 node.address.word2 = true := Adrs.fits_iff.mpr hword2
  have word3Fits : Adrs.Fits 4 node.address.word3 = true := Adrs.fits_iff.mpr hword3
  unfold Adrs.isCanonical
  rw [layerFits, treeFits, typeFits, word1Fits, word2Fits, word3Fits]
  cases node <;> rfl

/-- Parsing the actual serialized address recovers its natural structural fields. -/
theorem StructuralNode.fromVector_toVector_address (widths : Widths p) (node : StructuralNode p) :
    Adrs.fromVector node.address.toVector = node.address :=
  Adrs.fromVector_toVector_of_isCanonical _ (node.address_isCanonical widths)

/-- Under the local width conditions, the actual full address codec distinguishes all nodes. -/
theorem StructuralNode.toVector_address_injective (widths : Widths p) :
    Function.Injective (fun node : StructuralNode p => node.address.toVector) := by
  intro left right equal
  apply StructuralNode.address_injective
  simpa only [StructuralNode.fromVector_toVector_address widths] using
    congrArg Adrs.fromVector equal

end SLHDSA.Graph
