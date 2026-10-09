/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module
public import ToMathlib.Data.Heap

/-!
# Typed heap defaults and framing

Heap-specific initialization must not select defaults for ordinary function types.
Updates retain the defaults of other cells, including across the sum decomposition.
-/

public section

namespace VCVioTest.ModuleAPI.Heap

local instance : CellSpec Bool where
  type _ := Nat
  default _ := 7

example : (default : Bool → Nat) false = 0 := rfl

example : (Heap.empty : Heap Bool).get false = 7 := by simp

example : ((Heap.empty : Heap Bool).update false 11).get true = 7 := by simp

example :
    ((Heap.split Bool Bool).symm
      ((Heap.empty : Heap Bool).update false 11, Heap.empty)).get (.inr false) = 7 := by
  simp [Heap.get]

example :
    ((Heap.split Bool Bool).symm
      ((Heap.empty : Heap Bool).update false 11, Heap.empty)).get (.inl false) = 11 := by
  simp [Heap.get]

universe u v

example {Ident : Type u} [CellSpec.{u, v} Ident] (h : Heap Ident) :
    Heap.ofFn h.toFn = h := by simp

example {Ident : Type u} [CellSpec.{u, v} Ident]
    (f : (i : Ident) → CellSpec.type i) : (Heap.ofFn f).toFn = f := by simp

end VCVioTest.ModuleAPI.Heap
