/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Data.Fintype.Fin

/-!
# Keccak state-coordinate conversions

These total coordinate maps transcribe `toState` and `toString` from Foundation's
`algorithms/Keccak/StateConversions.cry` at revision
`7d0528bd998682788f4e23661f2829298f9e47db`. States are indexed by x, then y, then
the lane bit; strings put all bits of lane `(x,y)` at offset `(5*y+x)*w`.
Both inverse laws hold for every finite lane width, including zero, and every
element type. They are component theorems for the transcribed indexing equations;
no correspondence from the imported source AST is assumed.
-/

public section

namespace Cryptol.Bridge.KeccakCodec

/-- The nonnegative theta predecessor agrees with Euclidean wraparound on all five lanes.
`tmod` models reference remainder; `%` on `Int` is Lean's Euclidean remainder. -/
theorem theta_predecessor (x : Fin 5) :
    Int.tmod ((x.val : Int) + 4) 5 = ((x.val : Int) - 1) % 5 := by
  fin_cases x <;> decide

/-- The portable theta predecessor always supplies a valid lane index. -/
theorem theta_predecessor_range (x : Fin 5) :
    0 ≤ Int.tmod ((x.val : Int) + 4) 5 ∧ Int.tmod ((x.val : Int) + 4) 5 < 5 := by
  fin_cases x <;> decide

/-- A Keccak state with explicit x, y and lane coordinates. -/
abbrev State (w : Nat) (α : Type*) := Fin 5 → Fin 5 → Fin w → α

/-- Flatten the y-major lane order followed by the bit coordinate. -/
@[expose] def offset {w : Nat} (x y : Fin 5) (z : Fin w) : Fin (25 * w) :=
  finProdFinEquiv (finProdFinEquiv (y, x), z)

/-- The string offset is exactly the equation used by Foundation's `split` and indexing. -/
theorem offset_val {w : Nat} (x y : Fin 5) (z : Fin w) :
    (offset x y z).val = (5 * y.val + x.val) * w + z.val := by
  change z.val + w * (x.val + 5 * y.val) = (5 * y.val + x.val) * w + z.val
  simp only [Nat.add_comm, Nat.mul_comm]

/-- Split a flat string into its x/y/lane-bit coordinates. -/
@[expose] def toState {w : Nat} {α : Type*} (bits : Fin (25 * w) → α) : State w α :=
  fun x y z => bits (offset x y z)

/-- Join lanes with y as the outer generator and x as the inner generator. -/
@[expose] def toString {w : Nat} {α : Type*} (state : State w α) : Fin (25 * w) → α :=
  fun i =>
    let laneBit := finProdFinEquiv.symm i
    let yx := finProdFinEquiv.symm laneBit.1
    state yx.2 yx.1 laneBit.2

/-- Splitting a joined state preserves every coordinate. -/
@[simp] theorem toState_toString {w : Nat} {α : Type*} (state : State w α) :
    toState (toString state) = state := by
  funext x y z
  simp [toState, toString, offset]

/-- Joining a split string preserves every bit, also at width zero. -/
@[simp] theorem toString_toState {w : Nat} {α : Type*} (bits : Fin (25 * w) → α) :
    toString (toState bits) = bits := by
  funext i
  simp only [toString, toState, offset, Equiv.apply_symm_apply, Prod.eta]

/-- The state/string correspondence is an equivalence for arbitrary finite lane width. -/
@[expose] def equivalence (w : Nat) (α : Type*) : (Fin (25 * w) → α) ≃ State w α where
  toFun := toState
  invFun := toString
  left_inv := toString_toState
  right_inv := toState_toString

end Cryptol.Bridge.KeccakCodec
