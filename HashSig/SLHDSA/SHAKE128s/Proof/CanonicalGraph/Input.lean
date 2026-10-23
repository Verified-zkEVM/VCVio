/-
Copyright (c) 2026 Tom Wambsgans. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Wambsgans
-/

module

public import HashSig.SLHDSA.SHAKE128s.Proof.CanonicalGraph.Children
public import HashSig.SLHDSA.SHAKE128s.Proof.CanonicalGraph.Address

/-! Canonical byte inputs use only their public address and ordered child digest cells. -/

@[expose] public section

namespace SlhDsaSecurity.CanonicalGraph

abbrev Cells := Node → Digest
abbrev Padding := StructuralNode → BitVec (8 * (messageDigestBytes - n))

def childBytes (cells : Cells) (children : List Node) : Bytes :=
  (children.map fun child => bytesBE n (cells child)).flatten

def canonicalInput (publicSeed : Digest) (cells : Cells) (parent : StructuralNode) : Bytes :=
  Hashing.tweakableInput publicSeed parent.address (childBytes cells parent.children)

/-- The full 30-byte response consists of its 16-byte cell and an independent 14-byte suffix. -/
def fullOutput (cells : Cells) (padding : Padding) (parent : StructuralNode) : HashOutput :=
  cells (.structural parent) ++ padding parent

@[simp] theorem truncate_fullOutput (cells : Cells) (padding : Padding)
    (parent : StructuralNode) :
    Hashing.truncate (fullOutput cells padding parent) = cells (.structural parent) :=
  BitVec.extractLsb'_append_eq_left

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

theorem canonicalInput_parent {publicSeed publicSeed' : Digest}
    {left right : Cells} {parent parent' : StructuralNode}
    (h : canonicalInput publicSeed left parent = canonicalInput publicSeed' right parent') :
    parent = parent' := (canonicalInput_eq_iff.mp h).2.1

theorem canonicalInput_congr (publicSeed : Digest) (left right : Cells)
    (parent : StructuralNode)
    (hchildren : ∀ child ∈ parent.children, left child = right child) :
    canonicalInput publicSeed left parent = canonicalInput publicSeed right parent :=
  canonicalInput_eq_iff.mpr ⟨rfl, rfl, hchildren⟩

end SlhDsaSecurity.CanonicalGraph
