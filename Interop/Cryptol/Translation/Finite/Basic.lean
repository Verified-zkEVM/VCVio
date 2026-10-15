/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Interop.Cryptol.Model.Primitives
public import PolyFun.IPFunctor.Scoped.Interpretation
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Data.BitVec

/-!
# Native syntax and evaluation of finite descriptions

This typed source language has an independent interpretation in Lean functions,
Booleans and bitvectors. Correctness modules supply lowering and a logical
relation to the lazy core.
No source-language parser, type inference, or Haskell correctness assumption
occurs in these theorems.
-/

public section

namespace Interop.Cryptol.Finite

/-- Types of the total, monomorphic word fragment. -/
inductive Ty where
  | bit
  | word (width : Nat)
  | prod (left right : Ty)
  | seq (length : Nat) (element : Ty)
  | arrow (argument result : Ty)
  deriving DecidableEq, Repr

/-- The corresponding lazy-core type. -/
@[expose, implicit_reducible] def Ty.core : Ty → ClosedTy
  | .bit => .bit
  | .word n => .seq (.finite n) .bit
  | .prod a b => .prod a.core b.core
  | .seq n a => .seq (.finite n) a.core
  | .arrow a b => .arrow a.core b.core

/-- Independent, total meanings of source types.
Implicit reduction keeps products and arrays usable in ordinary-import rewrite lemmas. -/
@[expose, implicit_reducible] def Ty.Native : Ty → Type
  | .bit => Bool
  | .word n => BitVec n
  | .prod a b => a.Native × b.Native
  | .seq n a => Fin n → a.Native
  | .arrow a b => a.Native → b.Native

/-- Translate a typed variable to the corresponding core context. -/
@[expose] def lowerVar {Γ : List Ty} {a : Ty} : Var Γ a → Var (Γ.map Ty.core) a.core
  | .zero => .zero
  | .succ v => .succ (lowerVar v)

/-- Arithmetic operations that are total on every word. -/
inductive ArithOp where
  | add | sub | mul
  deriving DecidableEq, Repr

/-- The corresponding partial-language integer operation. -/
@[expose] def ArithOp.core : ArithOp → IntOp
  | .add => .add | .sub => .sub | .mul => .mul

/-- Independent modular arithmetic on native words. -/
@[expose] def ArithOp.eval {n : Nat} : ArithOp → BitVec n → BitVec n → BitVec n
  | .add, x, y => x + y
  | .sub, x, y => x - y
  | .mul, x, y => x * y

/-- Operations carry parameters and types; child syntax lives in the shared polynomial. -/
inductive Op : Ty → Type where
  | bit (b : Bool) : Op .bit
  | word {n : Nat} (x : BitVec n) : Op (.word n)
  | pair {a b : Ty} : Op (.prod a b)
  | fst {a b : Ty} : Op a
  | snd {a b : Ty} : Op b
  | sequence {a : Ty} (n : Nat) : Op (.seq n a)
  | snoc {a : Ty} {n : Nat} : Op (.seq (n + 1) a)
  | index {a : Ty} {n : Nat} (i : Fin n) : Op a
  | arithmetic {n : Nat} (op : ArithOp) : Op (.word n)
  | lam {a b : Ty} : Op (.arrow a b)
  | app {a b : Ty} : Op b
  | letE {a b : Ty} : Op b
  | bitNot : Op .bit
  | bitOp (op : BitOp) : Op .bit
  | wordNot {n : Nat} : Op (.word n)
  | wordOp {n : Nat} (op : BitOp) : Op (.word n)
  | wordEq (n : Nat) : Op .bit
  | shiftLeft {n : Nat} (amount : Nat) : Op (.word n)
  | shiftRight {n : Nat} (amount : Nat) : Op (.word n)
  | rotateLeft {n : Nat} (amount : Nat) : Op (.word n)
  | rotateRight {n : Nat} (amount : Nat) : Op (.word n)

/-- Number of arguments, including all entries of an explicit sequence literal. -/
@[expose, reducible] def Op.arity : {a : Ty} → Op a → Nat
  | _, .bit _ => 0
  | _, .word _ => 0
  | _, .pair => 2
  | _, .fst => 1
  | _, .snd => 1
  | _, .sequence n => n
  | _, .snoc => 2
  | _, .index _ => 1
  | _, .arithmetic _ => 2
  | _, .lam => 1
  | _, .app => 2
  | _, .letE => 2
  | _, .bitNot => 1
  | _, .bitOp _ => 2
  | _, .wordNot => 1
  | _, .wordOp _ => 2
  | _, .wordEq _ => 2
  | _, .shiftLeft _ => 1
  | _, .shiftRight _ => 1
  | _, .rotateLeft _ => 1
  | _, .rotateRight _ => 1

/-- Each child retains its binder list and result type. -/
@[expose, reducible] def Op.child : {a : Ty} → (op : Op a) → Fin op.arity → List Ty × Ty
  | _, .bit _ => fun p => nomatch p
  | _, .word _ => fun p => nomatch p
  | _, @Op.pair a b => Fin.cases ([], a) (fun _ => ([], b))
  | _, @Op.fst a b => fun _ => ([], .prod a b)
  | _, @Op.snd a b => fun _ => ([], .prod a b)
  | _, @Op.sequence a _ => fun _ => ([], a)
  | _, @Op.snoc a n => Fin.cases ([], .seq n a) (fun _ => ([], a))
  | _, @Op.index a n _ => fun _ => ([], .seq n a)
  | _, @Op.arithmetic n _ => Fin.cases ([], .word n) (fun _ => ([], .word n))
  | _, @Op.lam a b => fun _ => ([a], b)
  | _, @Op.app a b => Fin.cases ([], .arrow a b) (fun _ => ([], a))
  | _, @Op.letE a b => Fin.cases ([], a) (fun _ => ([a], b))
  | _, .bitNot => fun _ => ([], .bit)
  | _, .bitOp _ => Fin.cases ([], .bit) (fun _ => ([], .bit))
  | _, @Op.wordNot n => fun _ => ([], .word n)
  | _, @Op.wordOp n _ => Fin.cases ([], .word n) (fun _ => ([], .word n))
  | _, .wordEq n => Fin.cases ([], .word n) (fun _ => ([], .word n))
  | _, @Op.shiftLeft n _ => fun _ => ([], .word n)
  | _, @Op.shiftRight n _ => fun _ => ([], .word n)
  | _, @Op.rotateLeft n _ => fun _ => ([], .word n)
  | _, @Op.rotateRight n _ => fun _ => ([], .word n)

/-- A native binding signature, independent of Cryptol's partial semantics. -/
@[expose, reducible] def signature : IPFunctor.ScopedSignature Ty where
  Op := Op
  Arg op := Fin op.arity
  binders op p := (op.child p).1
  sort op p := (op.child p).2

/-- Native descriptions use the shared free scoped carrier. -/
abbrev Term := signature.Term

namespace Term

/-- Construct a native `var` expression. -/
@[expose] def var {Γ a} (v : Var Γ a) : Term Γ a :=
  .pure v

/-- Construct a native `bit` expression. -/
@[expose] def bit {Γ} (b : Bool) : Term Γ .bit :=
  .liftBind (.bit b) (fun p => nomatch p)

/-- Construct a native `word` expression. -/
@[expose] def word {Γ n} (x : BitVec n) : Term Γ (.word n) :=
  .liftBind (.word x) (fun p => nomatch p)

/-- Construct a native `pair` expression. -/
@[expose] def pair {Γ a b} (x : Term Γ a) (y : Term Γ b) : Term Γ (.prod a b) :=
  .liftBind (.pair) (Fin.cases x (fun _ => y))

/-- Construct a native `fst` expression. -/
@[expose] def fst {Γ a b} (x : Term Γ (.prod a b)) : Term Γ a :=
  .liftBind (.fst (b := b)) (fun _ => x)

/-- Construct a native `snd` expression. -/
@[expose] def snd {Γ a b} (x : Term Γ (.prod a b)) : Term Γ b :=
  .liftBind (.snd (a := a)) (fun _ => x)

/-- Construct a native `sequence` expression. -/
@[expose] def sequence {Γ a} (n : Nat) (items : Fin n → Term Γ a) : Term Γ (.seq n a) :=
  .liftBind (.sequence n) items

/-- Append one entry without copying the prefix into syntax. -/
@[expose] def snoc {Γ : List Ty} {a : Ty} {n : Nat}
    (xs : Term Γ (.seq n a)) (x : Term Γ a) : Term Γ (.seq (n + 1) a) :=
  .liftBind .snoc (Fin.cases xs (fun _ => x))

/-- Construct a native `index` expression. -/
@[expose] def index {Γ a n} (xs : Term Γ (.seq n a)) (i : Fin n) : Term Γ a :=
  .liftBind (.index i) (fun _ => xs)

/-- Construct a native `arithmetic` expression. -/
@[expose] def arithmetic {Γ n} (op : ArithOp) (x y : Term Γ (.word n)) : Term Γ (.word n) :=
  .liftBind (.arithmetic op) (Fin.cases x (fun _ => y))

/-- Construct a native `lam` expression. -/
@[expose] def lam {Γ a b} (body : Term (a :: Γ) b) : Term Γ (.arrow a b) :=
  .liftBind (.lam) (fun _ => body)

/-- Construct a native `app` expression. -/
@[expose] def app {Γ a b} (f : Term Γ (.arrow a b)) (x : Term Γ a) : Term Γ b :=
  .liftBind (.app (a := a)) (Fin.cases f (fun _ => x))

/-- Construct a native `letE` expression. -/
@[expose] def letE {Γ a b} (x : Term Γ a) (body : Term (a :: Γ) b) : Term Γ b :=
  .liftBind (.letE (a := a)) (Fin.cases x (fun _ => body))

/-- Construct a native `bitNot` expression. -/
@[expose] def bitNot {Γ} (x : Term Γ .bit) : Term Γ .bit :=
  .liftBind (.bitNot) (fun _ => x)

/-- Construct a native `bitOp` expression. -/
@[expose] def bitOp {Γ} (op : BitOp) (x y : Term Γ .bit) : Term Γ .bit :=
  .liftBind (.bitOp op) (Fin.cases x (fun _ => y))

/-- Construct a native `wordNot` expression. -/
@[expose] def wordNot {Γ n} (x : Term Γ (.word n)) : Term Γ (.word n) :=
  .liftBind (.wordNot) (fun _ => x)

/-- Construct a native `wordOp` expression. -/
@[expose] def wordOp {Γ n} (op : BitOp) (x y : Term Γ (.word n)) : Term Γ (.word n) :=
  .liftBind (.wordOp op) (Fin.cases x (fun _ => y))

/-- Construct a native `wordEq` expression. -/
@[expose] def wordEq {Γ n} (x y : Term Γ (.word n)) : Term Γ .bit :=
  .liftBind (.wordEq n) (Fin.cases x (fun _ => y))

/-- Construct a native `shiftLeft` expression. -/
@[expose] def shiftLeft {Γ n} (amount : Nat) (x : Term Γ (.word n)) : Term Γ (.word n) :=
  .liftBind (.shiftLeft amount) (fun _ => x)

/-- Construct a native `shiftRight` expression. -/
@[expose] def shiftRight {Γ n} (amount : Nat) (x : Term Γ (.word n)) : Term Γ (.word n) :=
  .liftBind (.shiftRight amount) (fun _ => x)

/-- Construct a native `rotateLeft` expression. -/
@[expose] def rotateLeft {Γ n} (amount : Nat) (x : Term Γ (.word n)) : Term Γ (.word n) :=
  .liftBind (.rotateLeft amount) (fun _ => x)

/-- Construct a native `rotateRight` expression. -/
@[expose] def rotateRight {Γ n} (amount : Nat) (x : Term Γ (.word n)) : Term Γ (.word n) :=
  .liftBind (.rotateRight amount) (fun _ => x)

end Term

/-- An environment of total source values. -/
abbrev Env (Γ : List Ty) := ∀ a, Var Γ a → a.Native

/-- Extend a native environment. -/
@[expose] def Env.extend {Γ : List Ty} {a : Ty} (ρ : Env Γ) (x : a.Native) :
    Env (a :: Γ) := fun _ v =>
  IPFunctor.ScopedSignature.Env.cons x (fun v => ρ _ v) v

/-- The empty native environment. -/
@[expose] def Env.empty : Env [] := fun _ v => nomatch v

@[simp] theorem Env.extend_zero {Γ : List Ty} {a : Ty} (ρ : Env Γ) (x : a.Native) :
    ρ.extend x a .zero = x := rfl

@[simp] theorem Env.extend_succ {Γ : List Ty} {a b : Ty} (ρ : Env Γ) (x : a.Native)
    (v : Var Γ b) : ρ.extend x b (.succ v) = ρ b v := rfl

/-- Total, native word logic. -/
@[expose] def wordOp {n : Nat} : BitOp → BitVec n → BitVec n → BitVec n
  | .and, x, y => x &&& y
  | .or, x, y => x ||| y
  | .xor, x, y => x ^^^ y

/-- Constructor meanings receive child functions over just their newly bound values. -/
@[expose] def nativeAlgebra : IPFunctor.ScopedSignature.Interpretation signature Ty.Native
  | _, .bit b, _ => b
  | _, .word x, _ => x
  | _, .pair, next => (next 0 IPFunctor.ScopedSignature.Env.empty,
      next 1 IPFunctor.ScopedSignature.Env.empty)
  | _, .fst, next => (next 0 IPFunctor.ScopedSignature.Env.empty).1
  | _, .snd, next => (next 0 IPFunctor.ScopedSignature.Env.empty).2
  | _, .sequence _, next => fun i => next i IPFunctor.ScopedSignature.Env.empty
  | _, .snoc, next => Fin.snoc (next 0 IPFunctor.ScopedSignature.Env.empty)
      (next 1 IPFunctor.ScopedSignature.Env.empty)
  | _, .index i, next => next 0 IPFunctor.ScopedSignature.Env.empty i
  | _, .arithmetic op, next => op.eval (next 0 IPFunctor.ScopedSignature.Env.empty)
      (next 1 IPFunctor.ScopedSignature.Env.empty)
  | _, .lam, next => fun x => next 0
      (IPFunctor.ScopedSignature.Env.cons x IPFunctor.ScopedSignature.Env.empty)
  | _, .app, next => next 0 IPFunctor.ScopedSignature.Env.empty
      (next 1 IPFunctor.ScopedSignature.Env.empty)
  | _, .letE, next => next 1 (IPFunctor.ScopedSignature.Env.cons
      (next 0 IPFunctor.ScopedSignature.Env.empty) IPFunctor.ScopedSignature.Env.empty)
  | _, .bitNot, next => !(next 0 IPFunctor.ScopedSignature.Env.empty)
  | _, .bitOp op, next => op.eval (next 0 IPFunctor.ScopedSignature.Env.empty)
      (next 1 IPFunctor.ScopedSignature.Env.empty)
  | _, .wordNot, next => BitVec.not (next 0 IPFunctor.ScopedSignature.Env.empty)
  | _, .wordOp op, next => wordOp op (next 0 IPFunctor.ScopedSignature.Env.empty)
      (next 1 IPFunctor.ScopedSignature.Env.empty)
  | _, .wordEq n, next => @BEq.beq (BitVec n) inferInstance
      (next 0 IPFunctor.ScopedSignature.Env.empty) (next 1 IPFunctor.ScopedSignature.Env.empty)
  | _, .shiftLeft k, next => BitVec.shiftLeft (next 0 IPFunctor.ScopedSignature.Env.empty) k
  | _, .shiftRight k, next => BitVec.ushiftRight (next 0 IPFunctor.ScopedSignature.Env.empty) k
  | _, .rotateLeft k, next => (next 0 IPFunctor.ScopedSignature.Env.empty).rotateLeft k
  | _, .rotateRight k, next => (next 0 IPFunctor.ScopedSignature.Env.empty).rotateRight k

/-- Native meaning uses the shared interpreter, with an explicit-argument environment facade. -/
@[expose] def Term.denote {Γ : List Ty} {a : Ty} (t : Term Γ a) (ρ : Env Γ) : a.Native :=
  IPFunctor.ScopedSignature.Term.denote nativeAlgebra t (fun v => ρ _ v)

/-- Native renaming reuses the generic semantic law. -/
theorem Term.denote_rename {Γ Δ : List Ty} {a : Ty} (t : Term Γ a)
    (ren : IPFunctor.ScopedSignature.Renaming Γ Δ) (ρ : Env Δ) :
    Term.denote (t.rename ren) ρ = t.denote (fun a v => ρ a (ren v)) :=
  IPFunctor.ScopedSignature.Term.denote_rename nativeAlgebra t ren (fun v => ρ _ v)

/-- Native substitution reuses the generic semantic law. -/
theorem Term.denote_subst {Γ Δ : List Ty} {a : Ty} (t : Term Γ a)
    (sub : signature.Substitution Γ Δ) (ρ : Env Δ) :
    Term.denote (t.subst sub) ρ = t.denote (fun _ v => Term.denote (sub v) ρ) :=
  IPFunctor.ScopedSignature.Term.denote_subst nativeAlgebra t sub (fun v => ρ _ v)

@[simp] theorem Term.denote_letE {Γ : List Ty} {a b : Ty} (x : Term Γ a)
    (body : Term (a :: Γ) b) (ρ : Env Γ) :
    (Term.letE x body).denote ρ = body.denote (ρ.extend (x.denote ρ)) := rfl

@[simp] theorem Term.denote_sequence {Γ : List Ty} {a : Ty} (n : Nat)
    (xs : Fin n → Term Γ a) (ρ : Env Γ) :
    (Term.sequence n xs).denote ρ = fun i => (xs i).denote ρ := rfl

@[simp] theorem Term.denote_snoc {Γ : List Ty} {a : Ty} {n : Nat}
    (xs : Term Γ (.seq n a)) (x : Term Γ a) (ρ : Env Γ) :
    (Term.snoc xs x).denote ρ = Fin.snoc (xs.denote ρ) (x.denote ρ) := rfl

@[simp] theorem Term.denote_index {Γ : List Ty} {a : Ty} {n : Nat}
    (xs : Term Γ (.seq n a)) (i : Fin n) (ρ : Env Γ) :
    (Term.index xs i).denote ρ = xs.denote ρ i := rfl

@[simp] theorem Term.denote_var {Γ : List Ty} {a : Ty} (v : Var Γ a) (ρ : Env Γ) :
    (Term.var v).denote ρ = ρ _ v := rfl

@[simp] theorem Term.denote_bit {Γ : List Ty} (b : Bool) (ρ : Env Γ) :
    (Term.bit b).denote ρ = b := rfl

@[simp] theorem Term.denote_word {Γ : List Ty} {n : Nat} (x : BitVec n) (ρ : Env Γ) :
    (Term.word x).denote ρ = x := rfl

@[simp] theorem Term.denote_lam {Γ : List Ty} {a b : Ty}
    (body : Term (a :: Γ) b) (ρ : Env Γ) :
    (Term.lam body).denote ρ = fun x => body.denote (ρ.extend x) := rfl

@[simp] theorem Term.denote_app {Γ : List Ty} {a b : Ty}
    (f : Term Γ (.arrow a b)) (x : Term Γ a) (ρ : Env Γ) :
    (Term.app f x).denote ρ = f.denote ρ (x.denote ρ) := rfl

@[simp] theorem Term.denote_pair {Γ : List Ty} {a b : Ty}
    (x : Term Γ a) (y : Term Γ b) (ρ : Env Γ) :
    (Term.pair x y).denote ρ = (x.denote ρ, y.denote ρ) := rfl

@[simp] theorem Term.denote_fst {Γ : List Ty} {a b : Ty}
    (x : Term Γ (.prod a b)) (ρ : Env Γ) : (Term.fst x).denote ρ = (x.denote ρ).1 := rfl

@[simp] theorem Term.denote_snd {Γ : List Ty} {a b : Ty}
    (x : Term Γ (.prod a b)) (ρ : Env Γ) : (Term.snd x).denote ρ = (x.denote ρ).2 := rfl

@[simp] theorem Term.denote_arithmetic {Γ : List Ty} {n : Nat} (op : ArithOp)
    (x y : Term Γ (.word n)) (ρ : Env Γ) :
    (Term.arithmetic op x y).denote ρ = op.eval (x.denote ρ) (y.denote ρ) := rfl

@[simp] theorem Term.denote_wordNot {Γ : List Ty} {n : Nat}
    (x : Term Γ (.word n)) (ρ : Env Γ) : (Term.wordNot x).denote ρ = BitVec.not (x.denote ρ) := rfl

@[simp] theorem Term.denote_bitNot {Γ : List Ty} (x : Term Γ .bit) (ρ : Env Γ) :
    (Term.bitNot x).denote ρ = !(x.denote ρ) := rfl

@[simp] theorem Term.denote_bitOp {Γ : List Ty} (op : BitOp)
    (x y : Term Γ .bit) (ρ : Env Γ) :
    (Term.bitOp op x y).denote ρ = op.eval (x.denote ρ) (y.denote ρ) := rfl

@[simp] theorem Term.denote_wordEq {Γ : List Ty} {n : Nat}
    (x y : Term Γ (.word n)) (ρ : Env Γ) :
    (Term.wordEq x y).denote ρ = @BEq.beq (BitVec n) inferInstance (x.denote ρ) (y.denote ρ) := rfl

@[simp] theorem Term.denote_wordOp {Γ : List Ty} {n : Nat} (op : BitOp)
    (x y : Term Γ (.word n)) (ρ : Env Γ) :
    (Term.wordOp op x y).denote ρ = Finite.wordOp op (x.denote ρ) (y.denote ρ) := rfl

@[simp] theorem Term.denote_rotateLeft {Γ : List Ty} {n : Nat}
    (k : Nat) (x : Term Γ (.word n)) (ρ : Env Γ) :
    (Term.rotateLeft k x).denote ρ = BitVec.rotateLeft (x.denote ρ) k := rfl

@[simp] theorem Term.denote_rotateRight {Γ : List Ty} {n : Nat}
    (k : Nat) (x : Term Γ (.word n)) (ρ : Env Γ) :
    (Term.rotateRight k x).denote ρ = BitVec.rotateRight (x.denote ρ) k := rfl

@[simp] theorem Term.denote_shiftLeft {Γ : List Ty} {n : Nat}
    (k : Nat) (x : Term Γ (.word n)) (ρ : Env Γ) :
    (Term.shiftLeft k x).denote ρ = BitVec.shiftLeft (x.denote ρ) k := rfl

@[simp] theorem Term.denote_shiftRight {Γ : List Ty} {n : Nat}
    (k : Nat) (x : Term Γ (.word n)) (ρ : Env Γ) :
    (Term.shiftRight k x).denote ρ = BitVec.ushiftRight (x.denote ρ) k := rfl

end Interop.Cryptol.Finite
