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

The nodes of the canonical computation graph of an SLH-DSA-SHAKE-128s key: `Node` is either the
secret seed or a `StructuralNode`, a WOTS+ secret or chain value, a WOTS+ public key, an XMSS
Merkle node, a FORS secret or tree node, or a compressed FORS public key, each located by finite
coordinates. `StructuralNode.address` gives the ADRS under which a node is hashed and
`Node.rank` its depth in the graph.

The layer/tree rectangle `Tree` includes unused subtree coordinates. It contains every standard
SLH-DSA-SHAKE-128s address and keeps address parsing independent of secret values. Within a tree,
WOTS chain indices and height-dependent Merkle/FORS node indices have their exact bounds.
-/

@[expose] public section

namespace SlhDsaSecurity.CanonicalGraph

/-- The location of an XMSS tree in the hypertree: a layer and a tree index, ranging over the
full rectangle of tree indices at every layer. -/
structure Tree where
  /-- The hypertree layer. -/
  layer : Fin layers
  /-- The index of the tree within its layer. -/
  tree : Fin (2 ^ (totalHeight - subtreeHeight))
deriving DecidableEq, Fintype

/-- A WOTS+ key pair: an XMSS tree and the leaf it occupies. -/
structure WotsKey where
  /-- The XMSS tree holding the key pair. -/
  tree : Tree
  /-- The leaf index of the key pair in its tree. -/
  leaf : Fin (2 ^ subtreeHeight)
deriving DecidableEq, Fintype

/-- A FORS key pair, attached to a leaf of a bottom-layer XMSS tree. -/
structure ForsKey where
  /-- The index of the bottom-layer XMSS tree. -/
  tree : Fin (2 ^ (totalHeight - subtreeHeight))
  /-- The leaf of that tree the FORS key pair signs under. -/
  leaf : Fin (2 ^ subtreeHeight)
deriving DecidableEq, Fintype

/-- The hypertree address of an XMSS tree. -/
def Tree.address (tree : Tree) : Address :=
  Hypertree.address tree.layer.val tree.tree.val

/-- The WOTS+ hash address of a WOTS+ key pair. -/
def WotsKey.address (key : WotsKey) : Address :=
  Merkle.wotsAddress key.tree.address key.leaf.val

/-- The FORS tree address of a FORS key pair. -/
def ForsKey.address (key : ForsKey) : Address :=
  { (Hypertree.address 0 key.tree.val).setTypeAndClear .forsTree with
    keyPair := BitVec.ofNat 32 key.leaf.val }

/-- A node of the computation graph other than the secret seed, located by finite
coordinates. -/
inductive StructuralNode where
  /-- The secret start value of a WOTS+ chain, derived from the secret seed. -/
  | wotsPrf (key : WotsKey) (chain : Fin chains)
  /-- The value of a WOTS+ chain after the hash at position `step`. -/
  | wotsHash (key : WotsKey) (chain : Fin chains) (step : Fin (w - 1))
  /-- The compressed WOTS+ public key, an XMSS leaf. -/
  | wotsPk (key : WotsKey)
  /-- An inner XMSS node at height `height + 1`. -/
  | tree (tree : Tree) (height : Fin subtreeHeight)
      (index : Fin (2 ^ (subtreeHeight - (height.val + 1))))
  /-- A FORS secret value, derived from the secret seed. -/
  | forsPrf (key : ForsKey) (index : Fin (forsTrees * 2 ^ forsHeight))
  /-- A FORS tree node at height `height`, indexed across all `forsTrees` trees. -/
  | forsTree (key : ForsKey) (height : Fin (forsHeight + 1))
      (index : Fin (forsTrees * 2 ^ (forsHeight - height.val)))
  /-- The compressed FORS public key. -/
  | forsRoots (key : ForsKey)
deriving DecidableEq, Fintype

/-- A node of the computation graph: the secret seed or a structural node. -/
inductive Node where
  /-- The secret seed, the root of the graph. -/
  | secretSeed
  /-- A structural node. -/
  | structural (node : StructuralNode)
deriving DecidableEq, Fintype

/-- The address under which a structural node is computed. -/
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

/-- The depth of a structural node: the number of hash steps from the secret seed. -/
def StructuralNode.rank : StructuralNode → Nat
  | .wotsPrf _ _ => 1
  | .wotsHash _ _ step => 2 + step.val
  | .wotsPk _ => 17
  | .tree _ height _ => 17 + (height.val + 1)
  | .forsPrf _ _ => 1
  | .forsTree _ height _ => 2 + height.val
  | .forsRoots _ => 15

/-- The depth of a node in the computation graph, zero for the secret seed. -/
def Node.rank : Node → Nat
  | .secretSeed => 0
  | .structural node => node.rank

end SlhDsaSecurity.CanonicalGraph
