/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Interop.Cryptol.Model.WordOps
public import Interop.Cryptol.Model.Laws

/-!
# Unsigned conversion and modular word arithmetic

Conversion demands the complete operand in most-significant-bit order.
Representation theorems apply at every width, including empty words.
-/

public section

namespace Interop.Cryptol

/-- Extending a big-endian prefix doubles its value and adds the next bit. -/
theorem word_prefix_step {n : Nat} (x : BitVec n) (k : Nat) (hk : k < n) :
    x.toNat / 2 ^ (n - k) * 2 + (x.getMsbD k).toNat =
      x.toNat / 2 ^ (n - (k + 1)) := by
  rw [BitVec.getMsbD_eq_getLsbD]
  simp only [hk, decide_true, Bool.true_and, BitVec.getLsbD, Nat.toNat_testBit]
  have he : n - k = (n - (k + 1)) + 1 := by omega
  have he' : n - 1 - k = n - (k + 1) := by omega
  rw [he, he', Nat.pow_succ, ← Nat.div_div_eq_div_mul]
  omega

/-- A represented prefix has the corresponding unsigned high-bit value. -/
theorem Expr.denote_wordPrefix {Γ : List ClosedTy} {n : Nat}
    (xs : Expr Γ (.seq (.finite n) .bit)) (η : Environment Γ) (x : BitVec n)
    (hx : xs.denote η = .value (wordValue x)) (k : Nat) (hk : k ≤ n) :
    (xs.wordPrefix k).denote η = .value ⟨(x.toNat / 2 ^ (n - k) : Nat)⟩ := by
  induction k with
  | zero => simp [wordPrefix, Nat.div_eq_of_lt x.isLt, Expr.denote]
  | succ k ih =>
      have hkn : k < n := by omega
      change Semantics.binary IntOp.add.eval
        (Semantics.binary IntOp.mul.eval ((xs.wordPrefix k).denote η) (.value ⟨2⟩))
        (Semantics.conditional (a := .integer) (.value ⟨1⟩, .value ⟨0⟩)
          ((Expr.index xs (.integer k)).denote η)) = _
      rw [ih (by omega), Expr.denote_index_word xs η x hx ⟨k, hkn⟩ _ rfl]
      have hs := word_prefix_step x k hkn
      cases hb : x.getMsbD k <;>
        simp only [hb, Bool.toNat_false, Bool.toNat_true] at hs
      all_goals
        change (DomainResult.value ⟨_⟩ : Computation .integer) = _
        congr 2
        simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
          congrArg (fun q : Nat => (q : Int)) hs

/-- Unsigned conversion returns the native value of every represented word. -/
theorem Expr.denote_wordToInteger {Γ : List ClosedTy} {n : Nat}
    (xs : Expr Γ (.seq (.finite n) .bit)) (η : Environment Γ) (x : BitVec n)
    (hx : xs.denote η = .value (wordValue x)) :
    xs.wordToInteger.denote η = .value ⟨(x.toNat : Int)⟩ := by
  simp only [wordToInteger, denote_force, denote_letE, hx, DomainResult.force_value]
  rw [Expr.denote_wordPrefix _ _ x (by rfl) n le_rfl]
  simp

/-- Two truncating remainders implement a nonnegative remainder for a positive modulus. -/
theorem tmod_normalize (x m : Int) (hm : 0 < m) :
    (x.tmod m + m).tmod m = x % m := by
  rw [Int.tmod_eq_emod_of_nonneg (by have := Int.lt_tmod_of_pos x hm; omega)]
  simp only [Int.add_emod_right]
  rw [Int.tmod_eq_emod]
  split <;> simp [Int.natCast_natAbs, abs_of_pos hm]

theorem Expr.denote_euclideanMod {Γ : List ClosedTy} (value : Expr Γ .integer)
    (η : Environment Γ) (x : Int) (hx : value.denote η = .value ⟨x⟩)
    (m : Nat) (hm : 0 < m) :
    (euclideanMod m value).denote η = .value ⟨x % m⟩ := by
  have hn : (m : Int) ≠ 0 := by omega
  simp only [euclideanMod, denote_intOp, denote_integer, hx]
  rw [Semantics.intOp_values]
  simp only [IntOp.eval, hn, ↓reduceIte, ofExcept]
  rw [Semantics.intOp_values]
  change Semantics.binary IntOp.mod.eval
    (.value ⟨x.tmod m + m⟩ : Computation .integer) (.value ⟨(m : Int)⟩) = _
  rw [Semantics.intOp_values]
  simp only [IntOp.eval, hn, ↓reduceIte, ofExcept, tmod_normalize x m (by omega)]

theorem Expr.denote_integerBit {Γ : List ClosedTy} (value : Expr Γ .integer)
    (η : Environment Γ) (x : Nat) (hx : value.denote η = .value ⟨(x : Int)⟩)
    (lsb : Nat) : (integerBit value lsb).denote η = .value ⟨x.testBit lsb⟩ := by
  simp only [integerBit, denote_intEq, denote_intOp, denote_integer, hx]
  rw [Semantics.intOp_values]
  simp only [IntOp.eval, pow_ne_zero _ (by decide : (2 : Int) ≠ 0), ↓reduceIte, ofExcept]
  rw [Semantics.intOp_values]
  change (DomainResult.value ⟨((x : Int).tdiv (2 ^ lsb)).tmod 2 == 1⟩ :
    Computation .bit) = _
  congr 2
  rw [show (2 : Int) ^ lsb = ((2 ^ lsb : Nat) : Int) by simp,
    ← Int.ofNat_tdiv]
  change (((x / 2 ^ lsb % 2 : Nat) : Int) == 1) = x.testBit lsb
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq, Nat.testBit_eq_decide_div_mod_eq, decide_eq_true_eq]
  exact_mod_cast (Iff.rfl : x / 2 ^ lsb % 2 = 1 ↔ x / 2 ^ lsb % 2 = 1)

/-- Integer-to-word conversion represents the modular native bitvector. -/
theorem Expr.denote_integerToWord {Γ : List ClosedTy} (value : Expr Γ .integer)
    (η : Environment Γ) (x : Int) (hx : value.denote η = .value ⟨x⟩) (n : Nat) :
    (integerToWord n value).denote η = .value (wordValue (BitVec.ofInt n x)) := by
  simp only [integerToWord, denote_force, denote_letE, hx, DomainResult.force_value]
  rw [denote_euclideanMod value η x hx (2 ^ n) (Nat.two_pow_pos n)]
  apply congrArg DomainResult.value
  funext i
  change (select ((List.finRange n).map fun j =>
    integerBit (.var (.succ .zero)) (n - 1 - j.val)) (.var .zero)).denote
      ((η.extend (a := .integer) (.value ⟨x % (2 ^ n : Nat)⟩)).extend
        (a := .integer) (.value ⟨(i.val : Int)⟩)) = _
  rw [denote_select _ _ i.val (by simp) _ rfl]
  simp only [List.getElem_map, List.getElem_finRange]
  have hm : 0 ≤ x % (2 ^ n : Nat) := Int.emod_nonneg _
    (by exact_mod_cast (Nat.ne_of_gt (Nat.two_pow_pos n)))
  rw [denote_integerBit _ _ (x % (2 ^ n : Nat)).toNat
    (by
      change (DomainResult.value ⟨x % (2 ^ n : Nat)⟩ : Computation .integer) =
        .value ⟨((x % (2 ^ n : Nat)).toNat : Int)⟩
      rw [Int.toNat_of_nonneg hm])]
  simp [wordValue, BitVec.getMsbD_eq_getLsbD, i.isLt, BitVec.getLsbD, BitVec.toNat_ofInt]

/-- Arithmetic computes an integer result before exposing the output word. -/
theorem Expr.denote_wordOp {Γ : List ClosedTy} {n : Nat} (op : IntOp)
    (left right : Expr Γ (.seq (.finite n) .bit)) (η : Environment Γ)
    (x y : BitVec n) (hx : left.denote η = .value (wordValue x))
    (hy : right.denote η = .value (wordValue y)) (z : Int)
    (hz : op.eval x.toNat y.toNat = .ok z) :
    (wordOp op left right).denote η = .value (wordValue (BitVec.ofInt n z)) := by
  apply denote_integerToWord
  simp only [denote_intOp, denote_wordToInteger _ _ _ hx, denote_wordToInteger _ _ _ hy]
  rw [Semantics.intOp_values, hz]
  rfl

theorem Expr.denote_wordAdd {Γ : List ClosedTy} {n : Nat}
    (left right : Expr Γ (.seq (.finite n) .bit)) (η : Environment Γ)
    (x y : BitVec n) (hx : left.denote η = .value (wordValue x))
    (hy : right.denote η = .value (wordValue y)) :
    (wordOp .add left right).denote η = .value (wordValue (x + y)) := by
  rw [denote_wordOp _ _ _ _ _ _ hx hy _ rfl, BitVec.ofInt_add]
  simp

theorem Expr.denote_wordMul {Γ : List ClosedTy} {n : Nat}
    (left right : Expr Γ (.seq (.finite n) .bit)) (η : Environment Γ)
    (x y : BitVec n) (hx : left.denote η = .value (wordValue x))
    (hy : right.denote η = .value (wordValue y)) :
    (wordOp .mul left right).denote η = .value (wordValue (x * y)) := by
  rw [denote_wordOp _ _ _ _ _ _ hx hy _ rfl, BitVec.ofInt_mul]
  simp

/-- Subtraction wraps modulo the word size, including underflow. -/
theorem Expr.denote_wordSub {Γ : List ClosedTy} {n : Nat}
    (left right : Expr Γ (.seq (.finite n) .bit)) (η : Environment Γ)
    (x y : BitVec n) (hx : left.denote η = .value (wordValue x))
    (hy : right.denote η = .value (wordValue y)) :
    (wordOp .sub left right).denote η = .value (wordValue (x - y)) := by
  rw [denote_wordOp _ _ _ _ _ _ hx hy _ rfl]
  simp only [sub_eq_add_neg, BitVec.ofInt_add, BitVec.ofInt_neg]
  simp

/-- Unsigned division agrees with native division when the divisor is nonzero. -/
theorem Expr.denote_wordDiv {Γ : List ClosedTy} {n : Nat}
    (left right : Expr Γ (.seq (.finite n) .bit)) (η : Environment Γ)
    (x y : BitVec n) (hx : left.denote η = .value (wordValue x))
    (hy : right.denote η = .value (wordValue y)) (hy0 : y ≠ 0) :
    (wordOp .div left right).denote η = .value (wordValue (x / y)) := by
  have h : (y.toNat : Int) ≠ 0 := by
    intro h
    apply hy0
    apply BitVec.eq_of_toNat_eq
    simpa using h
  rw [denote_wordOp _ _ _ _ _ _ hx hy ((x.toNat : Int).tdiv y.toNat)
    (by simp only [IntOp.eval, h, ↓reduceIte])]
  rw [← Int.ofNat_tdiv, ← BitVec.toNat_udiv]
  rw [BitVec.ofInt_natCast, BitVec.ofNat_toNat]
  simp only [BitVec.setWidth_eq]

/-- Unsigned remainder agrees with native remainder when the divisor is nonzero. -/
theorem Expr.denote_wordMod {Γ : List ClosedTy} {n : Nat}
    (left right : Expr Γ (.seq (.finite n) .bit)) (η : Environment Γ)
    (x y : BitVec n) (hx : left.denote η = .value (wordValue x))
    (hy : right.denote η = .value (wordValue y)) (hy0 : y ≠ 0) :
    (wordOp .mod left right).denote η = .value (wordValue (x % y)) := by
  have h : (y.toNat : Int) ≠ 0 := by
    intro h
    apply hy0
    apply BitVec.eq_of_toNat_eq
    simpa using h
  rw [denote_wordOp _ _ _ _ _ _ hx hy ((x.toNat : Int).tmod y.toNat)
    (by simp only [IntOp.eval, h, ↓reduceIte])]
  rw [← Int.ofNat_tmod, ← BitVec.toNat_umod]
  rw [BitVec.ofInt_natCast, BitVec.ofNat_toNat]
  simp only [BitVec.setWidth_eq]

end Interop.Cryptol
