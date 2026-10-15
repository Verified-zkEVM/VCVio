/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Interop.Cryptol.Model.Syntax
public import Mathlib.Data.BitVec

/-!
# Finite descriptions of sequence and word constructions

These constructors expand into the checked lazy core. They never quote Lean
functions or inspect semantic values. Words use Cryptol's most-significant
bit first convention. Word arithmetic first demands all operand bits through
`wordToInteger`; elementwise Boolean operations remain lazy in each element.
-/

public section

namespace Interop.Cryptol.Expr

variable {Γ : List ClosedTy} {a b : ClosedTy}

/-- Shift an expression under one fresh binder. -/
@[expose] def weaken (e : Expr Γ a) : Expr (b :: Γ) a := e.rename Var.succ

/-- A divergent expression at any type. -/
@[expose] def diverge : Expr Γ a := .fix (.var .zero)

/-- Select a suspended list element by a zero-based integer index. -/
@[expose] def select (xs : List (Expr Γ a)) (i : Expr Γ .integer) : Expr Γ a :=
  match xs with
  | [] => .error (.user "invalid list index")
  | x :: xs => .ite (.intEq i (.integer 0)) x
      (select xs (.intOp .sub i (.integer 1)))

/-- A finite sequence literal whose elements remain suspended. -/
@[expose] def list (xs : List (Expr Γ a)) : Expr Γ (.seq (.finite xs.length) a) :=
  .generate (.finite xs.length) (select (xs.map weaken) (.var .zero))

/-- Map a function over a finite or infinite sequence. -/
@[expose] def map {l : Length} (f : Expr Γ (.arrow a b)) (xs : Expr Γ (.seq l a)) :
    Expr Γ (.seq l b) :=
  .generate l (.app f.weaken (.index xs.weaken (.var .zero)))

/-- A parallel comprehension stops at the shorter input. -/
@[expose] def zipWith {l m : Length} (f : Expr Γ (.arrow a (.arrow b a)))
    (xs : Expr Γ (.seq l a)) (ys : Expr Γ (.seq m b)) : Expr Γ (.seq (l.min m) a) :=
  .generate (l.min m) (.app (.app f.weaken (.index xs.weaken (.var .zero)))
    (.index ys.weaken (.var .zero)))

/-- Concatenation after a finite prefix, including an infinite suffix. -/
@[expose] def append {n : Nat} {m : Length} (xs : Expr Γ (.seq (.finite n) a))
    (ys : Expr Γ (.seq m a)) : Expr Γ (.seq ((Length.finite n).add m) a) :=
  .generate ((Length.finite n).add m) (.ite (.intLt (.var .zero) (.integer n))
    (.index xs.weaken (.var .zero))
    (.index ys.weaken (.intOp .sub (.var .zero) (.integer n))))

/-- A finite observation window into a sequence or stream. -/
@[expose] def observePrefix {l : Length} (n : Nat) (xs : Expr Γ (.seq l a)) :
    Expr Γ (.seq (.finite n) a) :=
  .generate (.finite n) (.index xs.weaken (.var .zero))

/-- A concrete bitvector as a lazy, most-significant-bit-first sequence. -/
@[expose] def word {n : Nat} (bits : BitVec n) : Expr Γ (.seq (.finite n) .bit) :=
  .generate (.finite n) (select
    ((List.finRange n).map fun i => Expr.bit (bits.getMsbD i.val)) (.var .zero))

/-- Demand a prefix of a word, accumulating its unsigned big-endian value. -/
@[expose] def wordPrefix {n : Nat} (xs : Expr Γ (.seq (.finite n) .bit)) :
    Nat → Expr Γ .integer
  | 0 => .integer 0
  | k + 1 => .intOp .add (.intOp .mul (wordPrefix xs k) (.integer 2))
      (.ite (.index xs (.integer k)) (.integer 1) (.integer 0))

/-- Demand all bits before exposing a word's unsigned integer value. -/
@[expose] def wordToInteger {n : Nat} (xs : Expr Γ (.seq (.finite n) .bit)) : Expr Γ .integer :=
  .force xs (.letE xs (wordPrefix (.var .zero) n))

/-- Extract one bit from a nonnegative integer using a fixed power of two. -/
@[expose] def integerBit (value : Expr Γ .integer) (lsb : Nat) : Expr Γ .bit :=
  .intEq (.intOp .mod (.intOp .div value (.integer (2 ^ lsb))) (.integer 2)) (.integer 1)

/-- Normalize an integer to its nonnegative residue for a positive modulus,
using the core's truncating remainder. -/
@[expose] def euclideanMod (modulus : Nat) (value : Expr Γ .integer) : Expr Γ .integer :=
  .intOp .mod (.intOp .add (.intOp .mod value (.integer modulus)) (.integer modulus))
    (.integer modulus)

/-- Encode an integer modulo the word width, demanding it even at width zero. -/
@[expose] def integerToWord (n : Nat) (value : Expr Γ .integer) :
    Expr Γ (.seq (.finite n) .bit) :=
  .force value (.letE (euclideanMod (2 ^ n) value)
    (.generate (.finite n) (select ((List.finRange n).map fun i =>
    integerBit (.var (.succ .zero)) (n - 1 - i.val)) (.var .zero))))

/-- Fixed-width arithmetic on finite words, by unsigned conversion and modular reduction. -/
@[expose] def wordOp {n : Nat} (op : IntOp) (x y : Expr Γ (.seq (.finite n) .bit)) :
    Expr Γ (.seq (.finite n) .bit) :=
  integerToWord n (.intOp op (wordToInteger x) (wordToInteger y))

/-- A logical left shift by a fixed natural amount, filling with zero. -/
@[expose] def shiftLeft {n : Nat} (amount : Nat) (xs : Expr Γ (.seq (.finite n) .bit)) :
    Expr Γ (.seq (.finite n) .bit) :=
  .generate (.finite n) (.ite (.intLt (.intOp .add (.var .zero) (.integer amount)) (.integer n))
    (.index xs.weaken (.intOp .add (.var .zero) (.integer amount))) (.bit false))

/-- A logical right shift by a fixed natural amount, filling with zero. -/
@[expose] def shiftRight {n : Nat} (amount : Nat) (xs : Expr Γ (.seq (.finite n) .bit)) :
    Expr Γ (.seq (.finite n) .bit) :=
  .generate (.finite n) (.ite (.intLt (.var .zero) (.integer amount)) (.bit false)
    (.index xs.weaken (.intOp .sub (.var .zero) (.integer amount))))

/-- Rotate a finite word to the left. At width zero the input computation is
preserved, including an outer error or divergence, as in Cryptol's reference evaluator. -/
@[expose] def rotateLeft {n : Nat} (amount : Nat) (xs : Expr Γ (.seq (.finite n) .bit)) :
    Expr Γ (.seq (.finite n) .bit) :=
  if n = 0 then xs else
    .generate (.finite n) (.index xs.weaken
      (.intOp .mod (.intOp .add (.var .zero) (.integer amount)) (.integer n)))

/-- Rotate a finite word to the right with the same zero-width convention. -/
@[expose] def rotateRight {n : Nat} (amount : Nat) (xs : Expr Γ (.seq (.finite n) .bit)) :
    Expr Γ (.seq (.finite n) .bit) :=
  rotateLeft (n - amount % n) xs

end Interop.Cryptol.Expr
