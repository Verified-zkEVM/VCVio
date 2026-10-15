/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Interop.Cryptol.Model.Types
public import Mathlib.Data.Nat.Log

/-!
# Partial numeric functions of the Cryptol reference language

The equations follow `Cryptol.TypeCheck.Solver.InfNat` at Cryptol 3.6.0.
Undefined arithmetic is `none`, distinct from finite zero and infinity. Numeric
substitution is interpreted over partial assignments, so an unused undefined
parameter does not invalidate an otherwise defined expression.
-/

public section

namespace Interop.Cryptol

/-- Unary numeric functions, with logarithms rounded upward. -/
inductive NumericUnary where
  | width
  | lg2
  deriving DecidableEq, Repr

/-- Binary numeric functions, including the two distinct rounding conventions. -/
inductive NumericBinary where
  | add | sub | mul | div | mod | exp | min | max | ceilDiv | ceilMod
  deriving DecidableEq, Repr

/-- Evaluate a unary function on a finite size or infinity. -/
@[expose] def NumericUnary.eval : NumericUnary → Length → Length
  | _, .infinite => .infinite
  | .width, .finite n => .finite (if n = 0 then 0 else n.log2 + 1)
  | .lg2, .finite n => .finite (if n ≤ 1 then 0 else (n - 1).log2 + 1)

/-- Evaluate a numeric function, rejecting its undefined argument combinations. -/
@[expose] def NumericBinary.eval : NumericBinary → Length → Length → Option Length
  | .add, a, b => some (a.add b)
  | .mul, a, b => some (a.mul b)
  | .min, a, b => some (a.min b)
  | .max, .finite a, .finite b => some (.finite (Nat.max a b))
  | .max, _, _ => some .infinite
  | .sub, .infinite, .finite _ => some .infinite
  | .sub, .finite a, .finite b => if b ≤ a then some (.finite (a - b)) else none
  | .sub, _, _ => none
  | .div, _, .finite 0 | .mod, _, .finite 0 => none
  | .div, .infinite, _ | .mod, .infinite, _ => none
  | .div, .finite a, .finite b => some (.finite (a / b))
  | .mod, .finite a, .finite b => some (.finite (a % b))
  | .div, .finite _, .infinite => some (.finite 0)
  | .mod, .finite a, .infinite => some (.finite a)
  | .ceilDiv, _, .infinite | .ceilMod, _, .infinite => none
  | .ceilDiv, _, .finite 0 | .ceilMod, _, .finite 0 => none
  | .ceilDiv, .infinite, .finite _ => some .infinite
  | .ceilMod, .infinite, .finite _ => some (.finite 0)
  | .ceilDiv, .finite a, .finite b => some (.finite ((a + b - 1) / b))
  | .ceilMod, .finite a, .finite b => some (.finite ((b - a % b) % b))
  | .exp, _, .finite 0 => some (.finite 1)
  | .exp, .infinite, _ => some .infinite
  | .exp, .finite 0, .infinite => some (.finite 0)
  | .exp, .finite 1, .infinite => some (.finite 1)
  | .exp, .finite _, .infinite => some .infinite
  | .exp, .finite a, .finite b => some (.finite (a ^ b))

/-- Length of an inclusive enumeration; equal first and second values are undefined. -/
@[expose] def numericRangeLength : Length → Length → Length → Option Length
  | .finite first, .finite next, .finite last =>
      if first = next then none
      else if first < next then
        some (.finite (if last < first then 0 else (last - first) / (next - first) + 1))
      else some (.finite (if first < last then 0 else (first - last) / (first - next) + 1))
  | _, _, _ => none

/-- Finite numeric syntax with every reference numeric operation explicit. -/
inductive NumericExpr (n : Nat) where
  | var (index : Fin n)
  | finite (value : Nat)
  | infinite
  | unary (op : NumericUnary) (argument : NumericExpr n)
  | binary (op : NumericBinary) (left right : NumericExpr n)
  | rangeLength (first next last : NumericExpr n)
  deriving DecidableEq, Repr

namespace NumericExpr

/-- Simultaneously substitute numeric expressions without evaluating them. -/
@[expose] def subst {n m : Nat} (σ : Fin n → NumericExpr m) : NumericExpr n → NumericExpr m
  | .var i => σ i
  | .finite k => .finite k
  | .infinite => .infinite
  | .unary op a => .unary op (a.subst σ)
  | .binary op a b => .binary op (a.subst σ) (b.subst σ)
  | .rangeLength a b c => .rangeLength (a.subst σ) (b.subst σ) (c.subst σ)

/-- Evaluate under possibly undefined parameters, propagating demanded failures. -/
@[expose] def eval {n : Nat} (ρ : Fin n → Option Length) : NumericExpr n → Option Length
  | .var i => ρ i
  | .finite k => some (.finite k)
  | .infinite => some .infinite
  | .unary op a => op.eval <$> a.eval ρ
  | .binary op a b => do op.eval (← a.eval ρ) (← b.eval ρ)
  | .rangeLength a b c => do numericRangeLength (← a.eval ρ) (← b.eval ρ) (← c.eval ρ)

/-- Evaluate a source numeric expression at ordinary finite/infinite parameters. -/
@[expose] def eval? {n : Nat} (ρ : Fin n → Length) (e : NumericExpr n) : Option Length :=
  e.eval (some ∘ ρ)

/-- A checked numeric expression retains its actual value and successful evaluation. -/
structure Evaluation {n : Nat} (ρ : Fin n → Length) (e : NumericExpr n) where
  /-- The resulting finite size or infinity. -/
  value : Length
  /-- Undefined expressions have no such witness. -/
  valid : e.eval? ρ = some value

/-- Successful evaluation determines a unique numeric result. -/
theorem Evaluation.unique {n : Nat} {ρ : Fin n → Length} {e : NumericExpr n}
    (a b : e.Evaluation ρ) : a.value = b.value :=
  Option.some.inj (a.valid.symm.trans b.valid)

@[simp] theorem subst_id {n : Nat} (e : NumericExpr n) : e.subst .var = e := by
  induction e <;> simp_all [subst]

/-- Numeric substitution composes before any partial operation is evaluated. -/
theorem subst_subst {n m k : Nat} (e : NumericExpr n) (σ : Fin n → NumericExpr m)
    (τ : Fin m → NumericExpr k) :
    (e.subst σ).subst τ = e.subst (fun i => (σ i).subst τ) := by
  induction e <;> simp_all [subst]

/-- Partial numeric evaluation commutes with substitution, including undefined images. -/
theorem eval_subst {n m : Nat} (e : NumericExpr n) (σ : Fin n → NumericExpr m)
    (ρ : Fin m → Option Length) :
    (e.subst σ).eval ρ = e.eval (fun i => (σ i).eval ρ) := by
  induction e <;> simp_all [subst, eval]

/-- Substitute checked numeric arguments without introducing default values. -/
theorem eval?_subst {n m : Nat} (e : NumericExpr n) (σ : Fin n → NumericExpr m)
    (ρ : Fin m → Length) (η : Fin n → Length)
    (valid : ∀ i, (σ i).eval? ρ = some (η i)) :
    (e.subst σ).eval? ρ = e.eval? η := by
  unfold eval?
  rw [eval_subst]
  congr 1
  funext i
  exact valid i

end NumericExpr

/-- Embed the total numeric fragment into partial reference numeric syntax. -/
@[expose] def NumExpr.numeric {n : Nat} : NumExpr n → NumericExpr n
  | .var i => .var i
  | .finite k => .finite k
  | .infinite => .infinite
  | .add a b => .binary .add a.numeric b.numeric
  | .mul a b => .binary .mul a.numeric b.numeric
  | .min a b => .binary .min a.numeric b.numeric

/-- The total fragment has the same meaning in reference numeric semantics. -/
@[simp] theorem NumExpr.eval?_numeric {n : Nat} (e : NumExpr n) (ρ : Fin n → Length) :
    e.numeric.eval? ρ = some (e.eval ρ) := by
  induction e with
  | var | finite | infinite => rfl
  | add a b ha hb | mul a b ha hb | min a b ha hb =>
      simp_all [numeric, NumericExpr.eval?, NumericExpr.eval, eval, NumericBinary.eval]

end Interop.Cryptol
