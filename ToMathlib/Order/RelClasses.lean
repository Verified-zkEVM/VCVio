/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module

public import Mathlib.Order.PropInstances
public import Mathlib.Order.RelClasses

/-!
# Order classes of the total relation

The top element `⊤ : α → α → Prop` of the lattice of binary relations relates every pair of
elements, so it is a preorder.
-/

public section

/-- The total relation `⊤`, which relates every pair of elements, is a preorder. -/
instance {α : Type*} : IsPreorder α (⊤ : α → α → Prop) where
  refl _ := trivial
  trans _ _ _ _ _ := trivial
