/-
Copyright (c) 2026 Tom Wambsgans, Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Wambsgans, Alexander Hicks
-/

module
public import HashSig.SLHDSA.Graph.Structure

/-!
# Ordered dependencies of SLH-DSA structural coordinates

Children retain the order of hash payloads. Their ranks strictly decrease under mathematical
parameter validity. This is dependency order; it does not require actual signing traffic to be
globally rank sorted.
-/

public section

namespace SLHDSA.Graph

variable {p : Params}

/-- The node at `height` and `index` of an XMSS tree: a WOTS public key at height zero, an
internal tree node above it. -/
@[expose] def merkleNode (tree : Tree p) (height : Nat) (hheight : height ≤ p.hp)
    (index : Fin (2 ^ (p.hp - height))) : StructuralNode p :=
  if hzero : height = 0 then
    .wotsPk ⟨tree, ⟨index.val, by simpa [hzero] using index.isLt⟩⟩
  else
    .tree tree ⟨height - 1, by omega⟩
      ⟨index.val, by simpa only [Nat.sub_add_cancel (by omega : 1 ≤ height)] using index.isLt⟩

/-- An XMSS tree node at `height` has rank `(p.w + 1) + height`. -/
theorem merkleNode_rank (tree : Tree p) (height : Nat) (hheight : height ≤ p.hp)
    (index : Fin (2 ^ (p.hp - height))) :
    (merkleNode tree height hheight index).rank = (p.w + 1) + height := by
  unfold merkleNode
  split <;> simp_all [StructuralNode.rank]
  omega

/-- A child index `2 * index + side` stays inside the level one below. -/
theorem child_index_lt (height level count : Nat) (hlt : level < height)
    (index : Fin (count * 2 ^ (height - (level + 1)))) (side : Fin 2) :
    2 * index.val + side.val < count * 2 ^ (height - level) := by
  have hexp : height - level = height - (level + 1) + 1 := by omega
  rw [hexp, pow_succ, ← Nat.mul_assoc]
  have := index.isLt
  have := side.isLt
  omega

/-- The `side` child of the internal XMSS node at `height + 1` and `index`. -/
@[expose] def merkleChild (tree : Tree p) (height : Fin p.hp)
    (index : Fin (2 ^ (p.hp - (height.val + 1)))) (side : Fin 2) : StructuralNode p :=
  merkleNode tree height.val (Nat.le_of_lt height.isLt)
    ⟨2 * index.val + side.val, by
      have h := child_index_lt p.hp height.val 1 height.isLt
        ⟨index.val, by simp [index.isLt]⟩ side
      simpa using h⟩

/-- A child of an XMSS node at height `height + 1` has rank `(p.w + 1) + height`. -/
theorem merkleChild_rank (tree : Tree p) (height : Fin p.hp)
    (index : Fin (2 ^ (p.hp - (height.val + 1)))) (side : Fin 2) :
    (merkleChild tree height index side).rank = (p.w + 1) + height.val :=
  merkleNode_rank _ _ _ _

/-- The `side` child of the FORS node at positive `height` and `index`. -/
@[expose] def forsChild (key : ForsKey p) (height : Fin (p.a + 1))
    (hpos : 0 < height.val)
    (index : Fin (p.k * 2 ^ (p.a - height.val))) (side : Fin 2) : StructuralNode p :=
  .forsTree key ⟨height.val - 1, by omega⟩
    ⟨2 * index.val + side.val, by
      have hlevel : height.val - 1 < p.a := by omega
      have hback : height.val - 1 + 1 = height.val := by omega
      exact child_index_lt p.a (height.val - 1) p.k hlevel
        ⟨index.val, by simpa only [hback] using index.isLt⟩ side⟩

/-- The nodes a structural hash call reads, in input order. -/
@[expose] def StructuralNode.children (valid : p.Valid) : StructuralNode p → List (Node p)
  | .wotsPrf _ _ => [.secretSeed]
  | .wotsHash key chain step =>
      if hzero : step.val = 0 then [.structural (.wotsPrf key chain)]
      else [.structural (.wotsHash key chain ⟨step.val - 1, by omega⟩)]
  | .wotsPk key =>
      List.ofFn fun chain : Fin p.len => .structural (.wotsHash key chain ⟨p.w - 2, by
          have hw : 1 < p.w := Nat.one_lt_two_pow (Nat.ne_of_gt valid.lgw_pos)
          omega⟩)
  | .tree location height index =>
      [.structural (merkleChild location height index 0),
        .structural (merkleChild location height index 1)]
  | .forsPrf _ _ => [.secretSeed]
  | .forsTree key height index =>
      if hzero : height.val = 0 then
        [.structural (.forsPrf key ⟨index.val, by simpa [hzero] using index.isLt⟩)]
      else
        [.structural (forsChild key height (by omega) index 0),
          .structural (forsChild key height (by omega) index 1)]
  | .forsRoots key =>
      List.ofFn fun tree : Fin p.k =>
        .structural (.forsTree key ⟨p.a, by omega⟩ ⟨tree.val, by simp [tree.isLt]⟩)

/-- Every child has strictly smaller rank than its parent. -/
theorem StructuralNode.child_rank_lt (valid : p.Valid) (parent : StructuralNode p) (child : Node p)
    (hchild : child ∈ StructuralNode.children valid parent) : child.rank < parent.rank := by
  cases parent with
  | wotsPrf key chain | forsPrf key index =>
      simp only [StructuralNode.children, List.mem_singleton] at hchild
      subst child
      simp [Node.rank, StructuralNode.rank]
  | wotsHash key chain step =>
      simp only [StructuralNode.children] at hchild
      split at hchild <;> simp only [List.mem_singleton] at hchild <;> subst child
      · simp only [Node.rank, StructuralNode.rank]; omega
      · simp only [Node.rank, StructuralNode.rank]
        omega
  | wotsPk key =>
      simp only [StructuralNode.children, List.mem_ofFn] at hchild
      obtain ⟨chain, rfl⟩ := hchild
      simp only [Node.rank, StructuralNode.rank]
      have hw : 1 < p.w := Nat.one_lt_two_pow (Nat.ne_of_gt valid.lgw_pos)
      omega
  | tree tree height index =>
      simp only [StructuralNode.children, List.mem_cons, List.not_mem_nil, or_false] at hchild
      rcases hchild with rfl | rfl <;>
        change (merkleChild tree height index _).rank < p.w + 2 + height.val
      all_goals rw [merkleChild_rank]; omega
  | forsTree key height index =>
      simp only [StructuralNode.children] at hchild
      split at hchild
      · simp only [List.mem_singleton] at hchild
        subst child
        simp only [Node.rank, StructuralNode.rank]
        omega
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hchild
        rcases hchild with rfl | rfl <;>
          simp only [Node.rank, forsChild, StructuralNode.rank] <;> omega
  | forsRoots key =>
      simp only [StructuralNode.children, List.mem_ofFn] at hchild
      obtain ⟨tree, rfl⟩ := hchild
      simp only [Node.rank, StructuralNode.rank]
      omega

end SLHDSA.Graph
