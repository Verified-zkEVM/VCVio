/-
Copyright (c) 2026 Tom Wambsgans. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Wambsgans
-/

module

public import HashSig.SLHDSA.SHAKE128s.Proof.CanonicalGraph.Nodes

/-!
# Children of canonical structural nodes

Ordered child coordinates and a strictly decreasing rank for every dependency.
`StructuralNode.children` lists the nodes each structural hash call reads, in the order of its
input, and `StructuralNode.child_rank_lt` shows every child has strictly smaller rank, so the
canonical graph is well founded.
-/

public section

namespace SlhDsaSecurity.CanonicalGraph

/-- The node at `height` and `index` of an XMSS tree: a WOTS public key at height zero, an
internal tree node above it. -/
@[expose] def merkleNode (tree : Tree) (height : Nat) (hheight : height ≤ subtreeHeight)
    (index : Fin (2 ^ (subtreeHeight - height))) : StructuralNode :=
  if hzero : height = 0 then
    .wotsPk ⟨tree, ⟨index.val, by simpa [hzero] using index.isLt⟩⟩
  else
    .tree tree ⟨height - 1, by omega⟩
      ⟨index.val, by simpa only [Nat.sub_add_cancel (by omega : 1 ≤ height)] using index.isLt⟩

/-- An XMSS tree node at `height` has rank `17 + height`. -/
theorem merkleNode_rank (tree : Tree) (height : Nat) (hheight : height ≤ subtreeHeight)
    (index : Fin (2 ^ (subtreeHeight - height))) :
    (merkleNode tree height hheight index).rank = 17 + height := by
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
@[expose] def merkleChild (tree : Tree) (height : Fin subtreeHeight)
    (index : Fin (2 ^ (subtreeHeight - (height.val + 1)))) (side : Fin 2) : StructuralNode :=
  merkleNode tree height.val (Nat.le_of_lt height.isLt)
    ⟨2 * index.val + side.val, by
      have h := child_index_lt subtreeHeight height.val 1 height.isLt
        ⟨index.val, by simp [index.isLt]⟩ side
      simpa using h⟩

/-- A child of an XMSS node at height `height + 1` has rank `17 + height`. -/
theorem merkleChild_rank (tree : Tree) (height : Fin subtreeHeight)
    (index : Fin (2 ^ (subtreeHeight - (height.val + 1)))) (side : Fin 2) :
    (merkleChild tree height index side).rank = 17 + height.val :=
  merkleNode_rank _ _ _ _

/-- The `side` child of the FORS node at positive `height` and `index`. -/
@[expose] def forsChild (key : ForsKey) (height : Fin (forsHeight + 1))
    (hpos : 0 < height.val)
    (index : Fin (forsTrees * 2 ^ (forsHeight - height.val))) (side : Fin 2) : StructuralNode :=
  .forsTree key ⟨height.val - 1, by omega⟩
    ⟨2 * index.val + side.val, by
      have hlevel : height.val - 1 < forsHeight := by omega
      have hback : height.val - 1 + 1 = height.val := by omega
      exact child_index_lt forsHeight (height.val - 1) forsTrees hlevel
        ⟨index.val, by simpa only [hback] using index.isLt⟩ side⟩

/-- The nodes a structural hash call reads, in input order. -/
@[expose] def StructuralNode.children : StructuralNode → List Node
  | .wotsPrf _ _ => [.secretSeed]
  | .wotsHash key chain step =>
      if hzero : step.val = 0 then [.structural (.wotsPrf key chain)]
      else [.structural (.wotsHash key chain ⟨step.val - 1, by omega⟩)]
  | .wotsPk key =>
      List.ofFn fun chain : Fin chains => .structural (.wotsHash key chain ⟨w - 2, by decide⟩)
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
      List.ofFn fun tree : Fin forsTrees =>
        .structural (.forsTree key ⟨forsHeight, by omega⟩ ⟨tree.val, by simp [tree.isLt]⟩)

/-- Every child has strictly smaller rank than its parent. -/
theorem StructuralNode.child_rank_lt (parent : StructuralNode) (child : Node)
    (hchild : child ∈ parent.children) : child.rank < parent.rank := by
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
      simp [Node.rank, StructuralNode.rank, w, winternitzBits]
  | tree tree height index =>
      simp only [StructuralNode.children, List.mem_cons, List.not_mem_nil, or_false] at hchild
      rcases hchild with rfl | rfl <;>
        change (merkleChild tree height index _).rank < 17 + (height.val + 1)
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
      simp [Node.rank, StructuralNode.rank, forsHeight]

end SlhDsaSecurity.CanonicalGraph
