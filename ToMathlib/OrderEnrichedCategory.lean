/-
Copyright (c) 2025 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import Mathlib.CategoryTheory.Enriched.Basic
public import Mathlib.Order.Category.Preord
public import Mathlib.Order.Monotone.Basic

/-! # Order enriched category

We show that the general definition of an enriched category over a monoidal category specializes to
an order-enriched category when the monoidal category is the category of preorders.
-/

open CategoryTheory

@[expose] public section

universe w v u u₁ u₂

namespace Preord

/-- The category of preorders is monoidal. -/
instance : MonoidalCategory (Preord.{u}) where
  tensorObj X Y := ⟨X.carrier × Y.carrier⟩
  whiskerLeft X Y := fun f => ofHom ⟨fun x => (x.1, f.1 x.2),
      by
        intro a b hab
        exact ⟨hab.1, f.hom.2 hab.2⟩⟩
  whiskerRight f Y := ofHom ⟨fun y => (f.hom y.1, y.2),
      by
        intro a b hab
        exact ⟨f.hom.2 hab.1, hab.2⟩⟩
  tensorUnit := ⟨PUnit⟩
  associator X Y Z := {
    hom := ofHom ⟨fun ⟨⟨x, y⟩, z⟩ => ⟨x, ⟨y, z⟩⟩, by
      simp only [Monotone, Prod.mk_le_mk, Prod.forall, and_imp]
      intro _ _ _ _ _ _ h1 h2 h3; exact ⟨h1, h2, h3⟩⟩
    inv := ofHom ⟨fun ⟨x, ⟨y, z⟩⟩ => ⟨⟨x, y⟩, z⟩, by
      simp only [Monotone, Prod.mk_le_mk, Prod.forall, and_imp]
      intro _ _ _ _ _ _ h1 h2 h3; exact ⟨⟨h1, h2⟩, h3⟩⟩ }
  leftUnitor X := {
    hom := ofHom ⟨Prod.snd, (by simp [Monotone])⟩
    inv := ofHom ⟨fun x => (PUnit.unit, x), by simp [Monotone]⟩ }
  rightUnitor X := {
    hom := ofHom ⟨Prod.fst, (by simp [Monotone])⟩
    inv := ofHom ⟨fun x => (x, PUnit.unit), by simp [Monotone]⟩ }
  tensorHom_def f g := rfl
  -- tensor_id _ _ := rfl
  tensorHom_comp_tensorHom f₁ f₂ g₁ g₂ := rfl
  whiskerLeft_id _ _ := rfl
  id_whiskerRight _ _ := rfl
  associator_naturality f₁ f₂ f₃ := rfl
  leftUnitor_naturality f := rfl
  rightUnitor_naturality f := rfl
  pentagon _ _ _ _ := rfl
  triangle _ _ := rfl

end Preord

namespace CategoryTheory

open MonoidalCategory

/-- Categories enriched over the monoidal category of preorders are preorder-enriched categories. -/
abbrev PreordEnrichedCategory (C : Type u) := EnrichedCategory (Preord.{v}) C

-- TODO: simplify the enriched category definition to see the order-enriched category structure.

end CategoryTheory
