/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module
public import ToMathlib.Data.ByteArray
public import Mathlib.Data.FinEnum
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fintype.Sigma
public import Mathlib.Basic.Finite.Sigma

/-!
# Byte arrays with bounded length

`ByteArray.Bounded B` contains every byte array of length at most `B`. Its finite-register
representation retains both the length and every byte, including the empty array. It imposes
no parsing or domain-separation condition on its contents.
-/

public section

namespace ByteArray

/-- Every byte array of length at most `B`. -/
abbrev Bounded (B : ℕ) := {x : ByteArray // x.size ≤ B}

namespace Bounded

variable {B C : ℕ}

instance : DecidableEq (Bounded B) := inferInstanceAs (DecidableEq {x : ByteArray // x.size ≤ B})

/-- Forget the length bound, retaining exactly the original byte array. -/
@[expose]
def toByteArray (x : Bounded B) : ByteArray := x.val

/-- Forgetting the bound is injective. -/
theorem toByteArray_injective : Function.Injective (toByteArray (B := B)) :=
  fun _ _ h ↦ Subtype.ext h

/-- The retained byte array satisfies the bound. -/
theorem size_toByteArray_le (x : Bounded B) : x.toByteArray.size ≤ B := x.property

/-- Bounded byte arrays are their exact length together with that many bytes. -/
@[expose]
def equivSigma (B : ℕ) : Bounded B ≃ Σ k : Fin (B + 1), Vector UInt8 k.val where
  toFun x := ⟨⟨x.val.size, Nat.lt_succ_of_le x.property⟩, ⟨x.val.data, rfl⟩⟩
  invFun x := ⟨⟨x.2.toArray⟩, by
    change x.2.toArray.size ≤ B
    rw [x.2.size_toArray]
    exact Nat.le_of_lt_succ x.1.isLt⟩
  left_inv x := by cases x; rfl
  right_inv x := by
    rcases x with ⟨⟨k, hk⟩, ⟨a, ha⟩⟩
    cases ha
    rfl

instance : Finite (Bounded B) := by
  let (k : Fin (B + 1)) : Finite (Vector UInt8 k.val) :=
    Finite.of_injective (fun v : Vector UInt8 k.val ↦ fun i : Fin k.val ↦ v[i])
      (by intro x y h; exact Vector.ext fun i hi ↦ congrFun h ⟨i, hi⟩)
  exact Finite.of_equiv _ (equivSigma B).symm

noncomputable instance : Fintype (Bounded B) := Fintype.ofFinite _

instance : Inhabited (Bounded B) := ⟨⟨ByteArray.empty, by simp⟩⟩

/-- A byte array in a smaller window remains the same byte array in a larger window. -/
@[expose]
def widen (h : B ≤ C) (x : Bounded B) : Bounded C := ⟨x.val, x.property.trans h⟩

@[simp]
theorem toByteArray_widen (h : B ≤ C) (x : Bounded B) :
    (widen h x).toByteArray = x.toByteArray := rfl

end Bounded
end ByteArray
