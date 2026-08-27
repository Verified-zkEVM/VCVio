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

def tracedLeaf (index : ℕ) : StateM (List Address) ℕ :=
  pure (orderedLeaf index)

def tracedNode (address : Address) (left right : ℕ) : StateM (List Address) ℕ := do
  modify (· ++ [address])
  pure (orderedNode address left right)

/-- The effectful engine invokes internal-node callbacks in left-subtree, right-subtree, root
order, and supplies the corresponding addresses. -/
example :
    (treeHashM tracedLeaf tracedNode 2 0).run [] =
      (13254, [⟨1, 0⟩, ⟨1, 1⟩, ⟨2, 0⟩]) := rfl

end PerfectMerkleTreeTest
