/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.CryptoFoundations.MerkleTree.Perfect

/-!
# Perfect Merkle Tree Producer Canaries

Executable canaries pin left/right ordering, address production, effect order, path ordering, and
the `Fin`/`Vector`-indexed root interface of `PerfectMerkleTree`.
-/

@[expose] public section

namespace PerfectMerkleTreeTest

open PerfectMerkleTree

/-- A deliberately noncommutative, address-sensitive node callback. -/
def orderedNode (address : Address) (left right : ℕ) : ℕ :=
  1000 * address.height + 100 * address.index + 10 * left + right

def orderedLeaf (index : ℕ) : ℕ := index + 1

/-- The left subtree is evaluated before the right subtree, and the root address is emitted last. -/
example : treeHash orderedLeaf orderedNode 2 0 = 13254 := rfl

/-- Path entries run from the immediate sibling upward. -/
example :
    authenticationPath orderedLeaf orderedNode 0 0 2 =
      (⟨[2, 1134], rfl⟩ : AuthenticationPath ℕ 2) := rfl

/-- A rightmost leaf pins the opposite child orientation at both levels. -/
example :
    authenticationPath orderedLeaf orderedNode 0 3 2 =
      (⟨[3, 1012], rfl⟩ : AuthenticationPath ℕ 2) := rfl

example :
    climb orderedNode 0 3 2 (orderedLeaf 3)
        (authenticationPath orderedLeaf orderedNode 0 3 2) = 13254 := rfl

/-- Root-level callers must provide an in-range leaf index, and receive a path of exactly the root
height. -/
example : AuthenticationPath ℕ 2 :=
  rootAuthenticationPath orderedLeaf orderedNode (2 : LeafIndex 2)

/-- Trace events distinguish effectful leaf production from internal-node hashing. -/
inductive TraceEvent where
  | leaf (index : ℕ)
  | node (address : Address)
deriving DecidableEq, Repr

def tracedLeaf (index : ℕ) : StateM (List TraceEvent) ℕ := do
  modify (· ++ [.leaf index])
  pure (orderedLeaf index)

def tracedNode (address : Address) (left right : ℕ) : StateM (List TraceEvent) ℕ := do
  modify (· ++ [.node address])
  pure (orderedNode address left right)

/-- The effectful engine evaluates leaves and internal nodes in depth-first, left-to-right order,
and supplies the corresponding node addresses. -/
example :
    (treeHashM tracedLeaf tracedNode 2 0).run [] =
      (13254, [.leaf 0, .leaf 1, .node ⟨1, 0⟩, .leaf 2, .leaf 3,
        .node ⟨1, 1⟩, .node ⟨2, 0⟩]) := rfl

/-- The height-zero boundary evaluates exactly one leaf and no internal node. -/
example :
    (rootM tracedLeaf tracedNode 0).run [] = (1, [.leaf 0]) := rfl

/-- A height-zero root has exactly one valid leaf index and an empty authentication path. -/
example :
    rootAuthenticationPath orderedLeaf orderedNode (0 : LeafIndex 0) =
      (List.Vector.nil : AuthenticationPath ℕ 0) := rfl

end PerfectMerkleTreeTest
