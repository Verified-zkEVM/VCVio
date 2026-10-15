/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Interop.Cryptol.Model.NativePrimitives

/-!
# Native equations for represented operands

These equations are the total-value API for the direct reference semantics.
They complement the partial-input lowering equations and avoid unfolding
continuous-map implementations in consumer proofs.
-/

public section

namespace Interop.Cryptol.Semantics

variable {n : Nat}

@[simp] theorem wordNot_value (x : BitVec n) :
    wordNot n (.value (wordValue x)) = .value (wordValue (~~~x)) := by
  have h := Expr.denote_wordNot (.word x : Expr [] _) Environment.empty x
    (Expr.denote_word x Environment.empty)
  simpa only [Expr.denote_wordNot_sem, Expr.denote_word] using h

@[simp] theorem wordLogic_values (op : BitOp) (x y : BitVec n) :
    wordLogic n op (.value (wordValue x)) (.value (wordValue y)) =
      .value (wordValue (match op with
        | .and => x &&& y | .or => x ||| y | .xor => x ^^^ y)) := by
  have h := Expr.denote_wordBitOp op (.word x : Expr [] _) (.word y) Environment.empty x y
    (Expr.denote_word x Environment.empty) (Expr.denote_word y Environment.empty)
  cases op <;> simpa only [Expr.denote_wordLogic_sem, Expr.denote_word] using h

@[simp] theorem wordEq_values (x y : BitVec n) :
    wordEq n (.value (wordValue x)) (.value (wordValue y)) = .value ⟨x == y⟩ := by
  have h := Expr.denote_wordEq (.word x : Expr [] _) (.word y) Environment.empty x y
    (Expr.denote_word x Environment.empty) (Expr.denote_word y Environment.empty)
  simpa only [Expr.denote_wordEq_sem, Expr.denote_word] using h

@[simp] theorem wordAdd_values (x y : BitVec n) :
    wordArithmetic n .add (.value (wordValue x)) (.value (wordValue y)) =
      .value (wordValue (x + y)) := by
  have h := Expr.denote_wordAdd (.word x : Expr [] _) (.word y) Environment.empty x y
    (Expr.denote_word x Environment.empty) (Expr.denote_word y Environment.empty)
  simpa only [Expr.denote_wordArithmetic_sem, Expr.denote_word] using h

@[simp] theorem wordSub_values (x y : BitVec n) :
    wordArithmetic n .sub (.value (wordValue x)) (.value (wordValue y)) =
      .value (wordValue (x - y)) := by
  have h := Expr.denote_wordSub (.word x : Expr [] _) (.word y) Environment.empty x y
    (Expr.denote_word x Environment.empty) (Expr.denote_word y Environment.empty)
  simpa only [Expr.denote_wordArithmetic_sem, Expr.denote_word] using h

@[simp] theorem wordMul_values (x y : BitVec n) :
    wordArithmetic n .mul (.value (wordValue x)) (.value (wordValue y)) =
      .value (wordValue (x * y)) := by
  have h := Expr.denote_wordMul (.word x : Expr [] _) (.word y) Environment.empty x y
    (Expr.denote_word x Environment.empty) (Expr.denote_word y Environment.empty)
  simpa only [Expr.denote_wordArithmetic_sem, Expr.denote_word] using h

@[simp] theorem shiftFixed_value (op : ShiftOp) (amount : Nat) (x : BitVec n) :
    shiftFixed op n amount (.value (wordValue x)) =
      .value (wordValue (match op with
        | .left => x <<< amount | .right => x >>> amount
        | .rotateLeft => x.rotateLeft amount | .rotateRight => x.rotateRight amount)) := by
  have h : (Expr.shiftFixed op amount (.word x : Expr [] _)).denote Environment.empty =
      .value (wordValue (match op with
        | .left => x <<< amount | .right => x >>> amount
        | .rotateLeft => x.rotateLeft amount | .rotateRight => x.rotateRight amount)) := by
    cases op with
    | left => exact Expr.denote_shiftLeft _ _ _ _ (Expr.denote_word x Environment.empty)
    | right => exact Expr.denote_shiftRight _ _ _ _ (Expr.denote_word x Environment.empty)
    | rotateLeft => exact Expr.denote_rotateLeft _ _ _ _ (Expr.denote_word x Environment.empty)
    | rotateRight => exact Expr.denote_rotateRight _ _ _ _ (Expr.denote_word x Environment.empty)
  simpa only [Expr.denote_shiftFixed, Expr.denote_word] using h

end Interop.Cryptol.Semantics
