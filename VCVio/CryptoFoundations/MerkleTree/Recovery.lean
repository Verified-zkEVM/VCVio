/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.CryptoFoundations.MerkleTree.OrderedResolver
public import VCVio.CryptoFoundations.MerkleTree.Extractor
public import Mathlib.Data.Set.Card

/-!
# Decoded node support and extraction stability

Each supported oracle input decodes to at most two child labels. This gives the half-preimage
bound, independently of collisions and of overlap with the leaf-input encoding. A resolver
unchanged at reached labels reconstructs exactly the same partial tree.
-/

public section

open BinaryTree MerkleTreeHashing
namespace MerkleTreeExtractor
universe u v w
variable {X : Type u} {Y : Type v} {Address : Type w}

/-- Child components of successfully decoded supported node inputs. -/
@[expose]
def halfPreimages (decode : X → Option (Y × Y)) (D : X → Option Y) : Set Y :=
  {u | ∃ x c, D x ≠ none ∧ decode x = some c ∧ (u = c.1 ∨ u = c.2)}

/-- A supported input contributes at most its two decoded child components. -/
theorem ncard_halfPreimages_le (decode : X → Option (Y × Y)) (D : X → Option Y)
    (hD : {x | D x ≠ none}.Finite) :
    (halfPreimages decode D).ncard ≤ 2 * {x | D x ≠ none}.ncard := by
  classical
  let P : Set (Y × Y) := Option.some ⁻¹' (decode '' {x | D x ≠ none})
  have hfin : P.Finite := (hD.image decode).preimage (fun _ _ _ _ h => Option.some.inj h)
  have hcard : P.ncard ≤ {x | D x ≠ none}.ncard :=
    (Set.ncard_le_ncard_of_injOn Option.some (fun _ hc => hc)
      (fun _ _ _ _ h => Option.some.inj h) (hD.image decode)).trans (Set.ncard_image_le hD)
  have hsub : halfPreimages decode D ⊆ Prod.fst '' P ∪ Prod.snd '' P := by
    rintro y ⟨x, c, hx, hd, hy | hy⟩
    · exact Or.inl ⟨c, ⟨x, hx, hd⟩, hy.symm⟩
    · exact Or.inr ⟨c, ⟨x, hx, hd⟩, hy.symm⟩
  calc (halfPreimages decode D).ncard
      ≤ (Prod.fst '' P ∪ Prod.snd '' P).ncard :=
        Set.ncard_le_ncard hsub ((hfin.image _).union (hfin.image _))
    _ ≤ (Prod.fst '' P).ncard + (Prod.snd '' P).ncard := Set.ncard_union_le _ _
    _ ≤ P.ncard + P.ncard := add_le_add (Set.ncard_image_le hfin) (Set.ncard_image_le hfin)
    _ ≤ 2 * {x | D x ≠ none}.ncard := by omega

/-- Every recovered label belongs to a set containing the root and closed under resolved
children. -/
theorem treeWith_get_mem (resolve : Address → Y → Option (Y × Y)) (S : Set Y)
    (hclosed : ∀ address u, u ∈ S → ∀ c, resolve address u = some c → c.1 ∈ S ∧ c.2 ∈ S)
    (s : Skeleton) (addressKey : SkeletonInternalIndex s → Address) (root : Y)
    (hroot : root ∈ S) (i : SkeletonNodeIndex s) {u : Y}
    (h : (treeWith resolve s addressKey root).get i = some u) : u ∈ S := by
  induction s generalizing root u with
  | leaf => cases i; cases h; exact hroot
  | internal l r ihl ihr =>
      cases hc : resolve (addressKey .ofInternal) root with
      | none =>
          cases i with
          | ofInternal =>
              simp only [treeWith, hc, FullData.get_internal, Option.some.injEq] at h
              exact h ▸ hroot
          | ofLeft i =>
              simp only [treeWith, hc, FullData.get_internal_ofLeft] at h
              have hn := populateDown_none_get_eq_none (fun _ : Option Y => (none, none)) rfl i
              rw [hn] at h
              cases h
          | ofRight i =>
              simp only [treeWith, hc, FullData.get_internal_ofRight] at h
              have hn := populateDown_none_get_eq_none (fun _ : Option Y => (none, none)) rfl i
              rw [hn] at h
              cases h
      | some c =>
          have hmem := hclosed _ root hroot c hc
          cases i with
          | ofInternal =>
              simp only [treeWith, hc, FullData.get_internal, Option.some.injEq] at h
              exact h ▸ hroot
          | ofLeft i =>
              exact ihl (fun a => addressKey (.ofLeft a)) c.1 hmem.1 i (by
                simpa only [treeWith, hc, FullData.get_internal_ofLeft] using h)
          | ofRight i =>
              exact ihr (fun a => addressKey (.ofRight a)) c.2 hmem.2 i (by
                simpa only [treeWith, hc, FullData.get_internal_ofRight] using h)

/-- Resolvers agreeing at every reached label reconstruct the same partial tree. -/
theorem treeWith_eq_of_eqOn (before after : Address → Y → Option (Y × Y)) (S : Set Y)
    (hclosed : ∀ address u, u ∈ S → ∀ c, before address u = some c → c.1 ∈ S ∧ c.2 ∈ S)
    (heq : ∀ address u, u ∈ S → after address u = before address u)
    (s : Skeleton) (addressKey : SkeletonInternalIndex s → Address) (root : Y) (hroot : root ∈ S) :
    treeWith after s addressKey root = treeWith before s addressKey root := by
  induction s generalizing root with
  | leaf => rfl
  | internal l r ihl ihr =>
      simp only [treeWith, heq _ root hroot]
      cases hc : before (addressKey .ofInternal) root with
      | none => rfl
      | some c =>
          have hm := hclosed _ root hroot c hc
          rcases c with ⟨a, b⟩
          dsimp only at hm ⊢
          rw [ihl (fun a => addressKey (.ofLeft a)) a hm.1,
            ihr (fun a => addressKey (.ofRight a)) b hm.2]

end MerkleTreeExtractor
