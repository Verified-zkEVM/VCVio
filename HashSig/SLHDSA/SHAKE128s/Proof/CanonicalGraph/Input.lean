/-
Copyright (c) 2026 Tom Wambsgans. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Wambsgans
-/

module

public import HashSig.SLHDSA.SHAKE128s.Proof.CanonicalGraph.Children
public import HashSig.SLHDSA.SHAKE128s.Proof.CanonicalGraph.Address

/-!
# Canonical byte inputs

A cell assignment `Cells` gives a digest to every node of the canonical graph. The canonical
input of a structural node (`canonicalInput`) is the tweakable-hash input formed from the public
seed, the node's address and the concatenated digests of its ordered children (`childBytes`); it
depends on nothing else. The file shows that canonical inputs determine the seed, the parent and
the child cells (`canonicalInput_eq_iff`), and that the full hash output of a node splits into its
cell and an independent padding (`fullOutput`, `truncate_fullOutput`).
-/

public section

namespace SlhDsaSecurity.CanonicalGraph

/-- An assignment of a digest to every node of the canonical graph. -/
abbrev Cells := Node → Digest
/-- The trailing bytes of every structural node's full hash output, beyond its digest cell. -/
abbrev Padding := StructuralNode → BitVec (8 * (messageDigestBytes - n))

/-- The concatenated big-endian encodings of the cells of the given children, in order. -/
@[expose] def childBytes (cells : Cells) (children : List Node) : Bytes :=
  (children.map fun child => bytesBE n (cells child)).flatten

/-- The tweakable-hash input of a structural node: the public seed, the node's address and the
encoded cells of its ordered children. -/
@[expose]
def canonicalInput (publicSeed : Digest) (cells : Cells) (parent : StructuralNode) : Bytes :=
  Hashing.tweakableInput publicSeed parent.address (childBytes cells parent.children)

/-- The full 30-byte response consists of its 16-byte cell and an independent 14-byte suffix. -/
@[expose]
def fullOutput (cells : Cells) (padding : Padding) (parent : StructuralNode) : HashOutput :=
  cells (.structural parent) ++ padding parent

/-- Truncating a node's full output recovers its cell. -/
@[simp] theorem truncate_fullOutput (cells : Cells) (padding : Padding)
    (parent : StructuralNode) :
    Hashing.truncate (fullOutput cells padding parent) = cells (.structural parent) :=
  BitVec.extractLsb'_append_eq_left

/-- The child encodings agree exactly when the cells of all listed children agree. -/
theorem childBytes_eq_iff (left right : Cells) (children : List Node) :
    childBytes left children = childBytes right children ↔
      ∀ child ∈ children, left child = right child := by
  induction children with
  | nil => simp [childBytes]
  | cons child children ih =>
      simp only [childBytes, List.map_cons, List.flatten_cons]
      constructor
      · intro h
        obtain ⟨hchild, hrest⟩ := List.append_inj h (by simp)
        have hvalue := bytesBE_injective n hchild
        have hvalues := ih.mp hrest
        intro index hindex
        rcases List.mem_cons.mp hindex with rfl | hindex
        · exact hvalue
        · exact hvalues index hindex
      · intro h
        have hvalue := h child (by simp)
        have hvalues := ih.mpr (fun index hi => h index (by simp [hi]))
        change bytesBE n (left child) ++ childBytes left children =
          bytesBE n (right child) ++ childBytes right children
        rw [hvalue, hvalues]

/-- Two canonical inputs coincide exactly when their seeds and parents coincide and the cells
agree on the parent's children. -/
theorem canonicalInput_eq_iff {publicSeed publicSeed' : Digest}
    {left right : Cells} {parent parent' : StructuralNode} :
    canonicalInput publicSeed left parent = canonicalInput publicSeed' right parent' ↔
      publicSeed = publicSeed' ∧ parent = parent' ∧
        ∀ child ∈ parent.children, left child = right child := by
  constructor
  · intro h
    obtain ⟨hseed, haddress, hpayload⟩ := Hashing.tweakableInput_injective h
    have hparent := StructuralNode.address_injective haddress
    subst parent'
    exact ⟨hseed, rfl, (childBytes_eq_iff _ _ _).mp hpayload⟩
  · rintro ⟨rfl, rfl, hchildren⟩
    unfold canonicalInput
    rw [(childBytes_eq_iff _ _ _).mpr hchildren]

/-- A canonical input determines its parent node. -/
theorem canonicalInput_parent {publicSeed publicSeed' : Digest}
    {left right : Cells} {parent parent' : StructuralNode}
    (h : canonicalInput publicSeed left parent = canonicalInput publicSeed' right parent') :
    parent = parent' := (canonicalInput_eq_iff.mp h).2.1

/-- The canonical input of a parent depends only on the cells of its children. -/
theorem canonicalInput_congr (publicSeed : Digest) (left right : Cells)
    (parent : StructuralNode)
    (hchildren : ∀ child ∈ parent.children, left child = right child) :
    canonicalInput publicSeed left parent = canonicalInput publicSeed right parent :=
  canonicalInput_eq_iff.mpr ⟨rfl, rfl, hchildren⟩

end SlhDsaSecurity.CanonicalGraph
