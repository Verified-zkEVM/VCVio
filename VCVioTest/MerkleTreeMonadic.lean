/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import VCVio.CryptoFoundations.MerkleTree.Addressed.NatIndexed.Monadic
public import VCVio.OracleComp.HasQuery.Morphism

/-!
# Effectful addressed-Merkle canaries

These examples pin the monadic engine to the existing natural-number adapter and make its query
schedule observable.  The trace distinguishes leaf production from ordered node hashing, so a
regression in traversal order, child order, address calculation, or authentication-path order is
visible.
-/

@[expose] public section

namespace VCVioTest.MerkleTreeMonadicCanary

open _root_.PerfectMerkleTree

inductive Event where
  | leaf (index : ℕ)
  | node (height index left right : ℕ)
deriving DecidableEq, Repr

abbrev TraceM := StateM (List Event)

def leafM (index : ℕ) : TraceM ℕ := fun trace =>
  (index + 1, trace ++ [.leaf index])

/-- Address-sensitive and noncommutative, matching `PerfectMerkleTreeCanary.orderedHash`. -/
def nodeM (height index left right : ℕ) : TraceM ℕ := fun trace =>
  (1000 * height + 100 * index + 10 * left + right,
    trace ++ [.node height index left right])

/-- The full-tree wrapper retains the same nonzero-subtree addresses and trace as direct root
construction. -/
example :
    let result := Id.run ((treeM leafM nodeM 1 1).run [])
    (result.1.getRootValue, result.2) =
      (1134, [.leaf 2, .leaf 3, .node 1 1 3 4]) := by
  decide

/-- Tree construction is left subtree, right subtree, then parent. -/
example : Id.run ((merkleRootM leafM nodeM 2 0).run []) =
    (13254,
      [.leaf 0, .leaf 1, .node 1 0 1 2,
       .leaf 2, .leaf 3, .node 1 1 3 4,
       .node 2 0 1012 1134]) := by
  decide

/-- Authentication paths retain the canonical leaf-first order. -/
example : Id.run ((authPathM leafM nodeM 0 2).run []) =
    ([2, 1134],
       [.leaf 1, .leaf 2, .leaf 3, .node 1 1 3 4]) := by
  decide

/-- An odd leaf takes the right branch at the bottom level. -/
example : Id.run ((authPathM leafM nodeM 1 2).run []) =
    ([1, 1134],
      [.leaf 0, .leaf 2, .leaf 3, .node 1 1 3 4]) := by
  decide

/-- A mixed path takes the left branch at the bottom and the right branch above it. -/
example : Id.run ((authPathM leafM nodeM 2 2).run []) =
    ([4, 1012],
      [.leaf 3, .leaf 0, .leaf 1, .node 1 0 1 2]) := by
  decide

/-- Root recovery hashes bottom-up, with the opened node on the correct side at each level. -/
example : Id.run ((climbM nodeM 0 1 [2, 1134]).run []) =
    (13254, [.node 1 0 1 2, .node 2 0 1012 1134]) := by
  decide

/-- Root recovery follows the corresponding mixed left/right path. -/
example : Id.run ((climbM nodeM 2 3 [4, 1012]).run []) =
    (13254, [.node 1 1 3 4, .node 2 0 1012 1134]) := by
  decide

/-- Authentication-path construction retains global addresses in a nonzero height-two subtree. -/
example : Id.run ((authPathM leafM nodeM 6 2).run []) =
    ([8, 1256],
      [.leaf 7, .leaf 4, .leaf 5, .node 1 2 5 6]) := by
  decide

/-- Root recovery retains global addresses in a nonzero height-two subtree. -/
example : Id.run ((climbM nodeM 6 7 [8, 1256]).run []) =
    (16038, [.node 1 3 7 8, .node 2 1 1256 1378]) := by
  decide

/-- Height zero performs exactly one leaf effect and no node hashes. -/
example : Id.run ((merkleRootM leafM nodeM 0 7).run []) = (8, [.leaf 7]) := by
  decide

/-- Height-zero paths and climbs are effect-free. -/
example : Id.run ((authPathM leafM nodeM 7 0).run []) = ([], []) := by
  decide

example : Id.run ((climbM nodeM 7 8 []).run []) = (8, []) := by
  decide

/-! ## Query-homomorphism canary -/

inductive Query where
  | leaf
  | node

def querySpec : OracleSpec Query := fun _ => ℕ

/-- The generic monad-homomorphism law specializes directly to the free-oracle fold and uses
`QueryHom.map_query` to preserve each explicit leaf and node query. -/
example {m : Type → Type*} [Monad m] [LawfulMonad m] [HasQuery querySpec m] (z t : ℕ) :
    let F := HasQuery.QueryHom.ofSimulateQ (spec := querySpec) (m := m)
    F.toMonadHom
        (merkleRootM
          (fun _ => HasQuery.query (spec := querySpec)
            (m := OracleComp querySpec) Query.leaf)
          (fun _ _ _ _ => HasQuery.query (spec := querySpec)
            (m := OracleComp querySpec) Query.node) z t) =
      merkleRootM
        (fun _ => HasQuery.query (spec := querySpec) (m := m) Query.leaf)
        (fun _ _ _ _ => HasQuery.query (spec := querySpec) (m := m) Query.node) z t := by
  dsimp only
  apply merkleRootM_natural
  · intro i
    exact HasQuery.map_query
      (HasQuery.QueryHom.ofSimulateQ (spec := querySpec) (m := m)) Query.leaf
  · intro h i l r
    exact HasQuery.map_query
      (HasQuery.QueryHom.ofSimulateQ (spec := querySpec) (m := m)) Query.node

end VCVioTest.MerkleTreeMonadicCanary
