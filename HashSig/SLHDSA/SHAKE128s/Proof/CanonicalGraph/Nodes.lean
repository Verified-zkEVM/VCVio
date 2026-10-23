/-
Copyright (c) 2026 Tom Wambsgans. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Wambsgans
-/

module

public import HashSig.SLHDSA.SHAKE128s.Proof.Hashing
public import HashSig.SLHDSA.SHAKE128s.Proof.Experiment
public import Mathlib.Tactic.DeriveFintype

/-!
# Finite canonical structural coordinates

The layer/tree rectangle includes unused subtree coordinates. It contains every standard
SLH-DSA-SHAKE-128s address and keeps address parsing independent of secret values. Within a tree,
WOTS chain indices and height-dependent Merkle/FORS node indices have their exact bounds.
-/

@[expose] public section

namespace SlhDsaSecurity.CanonicalGraph

structure Tree where
  layer : Fin layers
  tree : Fin (2 ^ (totalHeight - subtreeHeight))
deriving DecidableEq, Fintype

structure WotsKey where
  tree : Tree
  leaf : Fin (2 ^ subtreeHeight)
deriving DecidableEq, Fintype

structure ForsKey where
  tree : Fin (2 ^ (totalHeight - subtreeHeight))
  leaf : Fin (2 ^ subtreeHeight)
deriving DecidableEq, Fintype

def Tree.address (tree : Tree) : Address :=
  Hypertree.address tree.layer.val tree.tree.val

def WotsKey.address (key : WotsKey) : Address :=
  Merkle.wotsAddress key.tree.address key.leaf.val

def ForsKey.address (key : ForsKey) : Address :=
  { (Hypertree.address 0 key.tree.val).setTypeAndClear .forsTree with
    keyPair := BitVec.ofNat 32 key.leaf.val }

inductive StructuralNode where
  | wotsPrf (key : WotsKey) (chain : Fin chains)
  | wotsHash (key : WotsKey) (chain : Fin chains) (step : Fin (w - 1))
  | wotsPk (key : WotsKey)
  | tree (tree : Tree) (height : Fin subtreeHeight)
      (index : Fin (2 ^ (subtreeHeight - (height.val + 1))))
  | forsPrf (key : ForsKey) (index : Fin (forsTrees * 2 ^ forsHeight))
  | forsTree (key : ForsKey) (height : Fin (forsHeight + 1))
      (index : Fin (forsTrees * 2 ^ (forsHeight - height.val)))
  | forsRoots (key : ForsKey)
deriving DecidableEq, Fintype

inductive Node where
  | secretSeed
  | structural (node : StructuralNode)
deriving DecidableEq, Fintype

def StructuralNode.address : StructuralNode → Address
  | .wotsPrf key chain => Wots.secretAddress key.address chain
  | .wotsHash key chain step =>
      { key.address with
        chainOrHeight := BitVec.ofNat 32 chain.val
        hashOrIndex := BitVec.ofNat 32 step.val }
  | .wotsPk key => Wots.publicKeyAddress key.address
  | .tree location height index => Merkle.nodeAddress location.address (height.val + 1) index.val
  | .forsPrf key index => Fors.secretAddress key.address index.val
  | .forsTree key height index => Fors.nodeAddress key.address height.val index.val
  | .forsRoots key =>
      { key.address.setTypeAndClear .forsRoots with keyPair := key.address.keyPair }

def StructuralNode.rank : StructuralNode → Nat
  | .wotsPrf _ _ => 1
  | .wotsHash _ _ step => 2 + step.val
  | .wotsPk _ => 17
  | .tree _ height _ => 17 + (height.val + 1)
  | .forsPrf _ _ => 1
  | .forsTree _ height _ => 2 + height.val
  | .forsRoots _ => 15

def Node.rank : Node → Nat
  | .secretSeed => 0
  | .structural node => node.rank

end SlhDsaSecurity.CanonicalGraph
