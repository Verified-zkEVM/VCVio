/-
Copyright (c) 2026 Tom Wambsgans, Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Wambsgans, Alexander Hicks
-/

module
public import HashSig.SLHDSA.Params
public import HashSig.SLHDSA.Address
public import Mathlib.Basic.Finite.Prod
public import Mathlib.Basic.Finite.Sigma
public import Mathlib.Basic.Finite.Sum

/-!
# Finite parameterized SLH-DSA structural coordinates

The secret seed and seven structural node families use the complete tree rectangle at every
hypertree layer. Coordinates are finite without materializing an enumeration. Addresses retain
natural fields; byte representability is a separate property of the chosen parameters.
-/

public section

namespace SLHDSA.Graph

variable {p : Params}

/-- The location of an XMSS tree in the hypertree: a layer and a tree index, ranging over the
full rectangle of tree indices at every layer. -/
structure Tree (p : Params) where
  /-- The hypertree layer. -/
  layer : Fin p.d
  /-- The index of the tree within its layer. -/
  tree : Fin (2 ^ (p.h - p.hp))
deriving DecidableEq

/-- A WOTS+ key pair: an XMSS tree and the leaf it occupies. -/
structure WotsKey (p : Params) where
  /-- The XMSS tree holding the key pair. -/
  tree : Tree p
  /-- The leaf index of the key pair in its tree. -/
  leaf : Fin (2 ^ p.hp)
deriving DecidableEq

/-- A FORS key pair, attached to a leaf of a bottom-layer XMSS tree. -/
structure ForsKey (p : Params) where
  /-- The index of the bottom-layer XMSS tree. -/
  tree : Fin (2 ^ (p.h - p.hp))
  /-- The leaf of that tree the FORS key pair signs under. -/
  leaf : Fin (2 ^ p.hp)
deriving DecidableEq

/-- The canonical natural-field base address of an XMSS tree. -/
@[expose] def Tree.address (tree : Tree p) : Adrs :=
  ⟨tree.layer, tree.tree, 0, 0, 0, 0⟩

/-- The natural-field WOTS hash address of a key pair. -/
@[expose] def WotsKey.address (key : WotsKey p) : Adrs :=
  ⟨key.tree.layer, key.tree.tree, 0, key.leaf, 0, 0⟩

/-- The natural-field FORS tree address of a bottom-layer key pair. -/
@[expose] def ForsKey.address (key : ForsKey p) : Adrs :=
  ⟨0, key.tree, 3, key.leaf, 0, 0⟩

/-- A node of the computation graph other than the secret seed, located by finite
coordinates. -/
inductive StructuralNode (p : Params) where
  /-- The secret start value of a WOTS+ chain, derived from the secret seed. -/
  | wotsPrf (key : WotsKey p) (chain : Fin p.len)
  /-- The value of a WOTS+ chain after the hash at position `step`. -/
  | wotsHash (key : WotsKey p) (chain : Fin p.len) (step : Fin (p.w - 1))
  /-- The compressed WOTS+ public key, an XMSS leaf. -/
  | wotsPk (key : WotsKey p)
  /-- An inner XMSS node at height `height + 1`. -/
  | tree (tree : Tree p) (height : Fin p.hp)
      (index : Fin (2 ^ (p.hp - (height.val + 1))))
  /-- A FORS secret value, derived from the secret seed. -/
  | forsPrf (key : ForsKey p) (index : Fin (p.k * 2 ^ p.a))
  /-- A FORS tree node at height `height`, indexed across all `p.k` trees. -/
  | forsTree (key : ForsKey p) (height : Fin (p.a + 1))
      (index : Fin (p.k * 2 ^ (p.a - height.val)))
  /-- The compressed FORS public key. -/
  | forsRoots (key : ForsKey p)
deriving DecidableEq

/-- A node of the computation graph: the secret seed or a structural node. -/
inductive Node (p : Params) where
  /-- The secret seed, the root of the graph. -/
  | secretSeed
  /-- A structural node. -/
  | structural (node : StructuralNode p)
deriving DecidableEq

/-- Natural fields retain exact coordinates before any byte serialization. -/
@[expose] def StructuralNode.address : StructuralNode p → Adrs
  | .wotsPrf key chain => ⟨key.tree.layer, key.tree.tree, 5, key.leaf, chain, 0⟩
  | .wotsHash key chain step => ⟨key.tree.layer, key.tree.tree, 0, key.leaf, chain, step⟩
  | .wotsPk key => ⟨key.tree.layer, key.tree.tree, 1, key.leaf, 0, 0⟩
  | .tree location height index =>
      ⟨location.layer, location.tree, 2, 0, height.val + 1, index⟩
  | .forsPrf key index => ⟨0, key.tree, 6, key.leaf, 0, index⟩
  | .forsTree key height index => ⟨0, key.tree, 3, key.leaf, height, index⟩
  | .forsRoots key => ⟨0, key.tree, 4, key.leaf, 0, 0⟩

/-- Structural dependency rank, with positive XMSS height represented by its predecessor. -/
@[expose] def StructuralNode.rank : StructuralNode p → Nat
  | .wotsPrf _ _ => 1
  | .wotsHash _ _ step => 2 + step.val
  | .wotsPk _ => p.w + 1
  | .tree _ height _ => p.w + 2 + height.val
  | .forsPrf _ _ => 1
  | .forsTree _ height _ => 2 + height.val
  | .forsRoots _ => p.a + 3

/-! ## Finiteness

Each coordinate type injects into a sum of products of finite types. The `Finite` instances
build no enumeration; consumers may obtain one explicitly through `Fintype.ofFinite`.
-/

/-- A tree is determined by its layer and index. -/
instance : Finite (Tree p) :=
  Finite.of_injective (fun tree : Tree p => (tree.layer, tree.tree)) <| by
    rintro ⟨⟩ ⟨⟩ h
    simp_all

/-- A WOTS+ key pair is determined by its tree and leaf. -/
instance : Finite (WotsKey p) :=
  Finite.of_injective (fun key : WotsKey p => (key.tree, key.leaf)) <| by
    rintro ⟨⟩ ⟨⟩ h
    simp_all

/-- A FORS key pair is determined by its tree index and leaf. -/
instance : Finite (ForsKey p) :=
  Finite.of_injective (fun key : ForsKey p => (key.tree, key.leaf)) <| by
    rintro ⟨⟩ ⟨⟩ h
    simp_all

/-- The fields of a structural node, one summand per constructor. -/
private def StructuralNode.fields : StructuralNode p →
    ((WotsKey p) × Fin p.len) ⊕ ((WotsKey p) × Fin p.len × Fin (p.w - 1)) ⊕ (WotsKey p) ⊕
      ((Tree p) × (height : Fin p.hp) × Fin (2 ^ (p.hp - (height.val + 1)))) ⊕
      ((ForsKey p) × Fin (p.k * 2 ^ p.a)) ⊕
      ((ForsKey p) × (height : Fin (p.a + 1)) ×
        Fin (p.k * 2 ^ (p.a - height.val))) ⊕ (ForsKey p)
  | .wotsPrf key chain => .inl (key, chain)
  | .wotsHash key chain step => .inr (.inl (key, chain, step))
  | .wotsPk key => .inr (.inr (.inl key))
  | .tree location height index => .inr (.inr (.inr (.inl (location, ⟨height, index⟩))))
  | .forsPrf key index => .inr (.inr (.inr (.inr (.inl (key, index)))))
  | .forsTree key height index => .inr (.inr (.inr (.inr (.inr (.inl (key, ⟨height, index⟩))))))
  | .forsRoots key => .inr (.inr (.inr (.inr (.inr (.inr key)))))

/-- A structural node is determined by its constructor and fields. -/
instance : Finite (StructuralNode p) :=
  Finite.of_injective StructuralNode.fields <| by
    intro left right h
    cases left <;> cases right <;> simp_all [StructuralNode.fields]

/-- A node is the secret seed or a structural node. -/
instance : Finite (Node p) :=
  Finite.of_injective
    (fun node : Node p => match node with
      | .secretSeed => (none : Option (StructuralNode p))
      | .structural node => some node) <| by
    intro left right h
    cases left <;> cases right <;> simp_all

/-- The depth of a node in the computation graph, zero for the secret seed. -/
@[expose] def Node.rank : Node p → Nat
  | .secretSeed => 0
  | .structural node => node.rank

end SLHDSA.Graph
