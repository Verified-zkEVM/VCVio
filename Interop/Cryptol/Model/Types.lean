/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.IPFunctor.Scoped.Basic
public import ToCslib.Data.Fin.Cases

/-!
# Kinds, lengths, and types of the Cryptol core

Numeric and value variables inhabit separate scopes. A schema records its
quantifiers and constraints explicitly; instantiation carries evidence for
those constraints. No inference or constraint solver is part of this model.
Infinite lengths are separate from finite lengths, including zero.
-/

public section

namespace Interop.Cryptol

/-- The numeric kind contains finite sizes and infinity. -/
inductive Length where
  | finite (size : Nat)
  | infinite
  deriving DecidableEq, Repr

namespace Length

/-- Positions in a sequence, with no position in an empty finite sequence.
Implicit reduction exposes the position type in dependent public equations. -/
@[expose, implicit_reducible] def Index : Length → Type
  | .finite n => Fin n
  | .infinite => Nat

/-- Addition of numeric lengths. -/
@[expose] def add : Length → Length → Length
  | .finite n, .finite m => .finite (n + m)
  | _, _ => .infinite

/-- Multiplication of lengths, with an empty dimension annihilating infinity. -/
@[expose] def mul : Length → Length → Length
  | .finite 0, _ | _, .finite 0 => .finite 0
  | .finite n, .finite m => .finite (n * m)
  | _, _ => .infinite

@[simp] theorem mul_finite_zero (l : Length) : l.mul (.finite 0) = .finite 0 := by
  cases l with
  | finite n => cases n <;> rfl
  | infinite => rfl

/-- Length of a parallel comprehension. -/
@[expose] def min : Length → Length → Length
  | .finite n, .finite m => .finite (Nat.min n m)
  | .finite n, .infinite => .finite n
  | .infinite, n => n

/-- Convert a valid typed sequence position to its natural-number index. -/
@[expose] def indexNat : {l : Length} → l.Index → Nat
  | .finite _, i => i.val
  | .infinite, i => i

/-- A position in a flattened sequence implies a nonempty row width. -/
theorem each_pos_of_index (parts : Length) (each : Nat)
    (i : (parts.mul (.finite each)).Index) : 0 < each := by
  cases each with
  | zero =>
      have h : (parts.mul (.finite 0)).Index = Fin 0 := by rw [mul_finite_zero]; rfl
      exact Fin.elim0 (h ▸ i)
  | succ each => exact Nat.zero_lt_succ _

/-- Check a possibly negative integer against a finite or infinite length. -/
@[expose] def checkIndex (l : Length) (i : Int) : Option l.Index :=
  if 0 ≤ i then
    match l with
    | .finite n => if h : i.toNat < n then some ⟨i.toNat, h⟩ else none
    | .infinite => some i.toNat
  else none

/-- A successful bounds check retains the original nonnegative index. -/
theorem indexNat_checkIndex (l : Length) (i : Int) (j : l.Index)
    (h : l.checkIndex i = some j) : (indexNat j : Int) = i := by
  cases l with
  | finite n =>
      simp only [checkIndex] at h
      split at h
      · rename_i hi
        split at h
        · cases Option.some.inj h
          exact Int.toNat_of_nonneg hi
        · cases h
      · cases h
  | infinite =>
      simp only [checkIndex] at h
      split at h
      · rename_i hi
        cases Option.some.inj h
        exact Int.toNat_of_nonneg hi
      · cases h

end Length

/-- Numeric expressions retained at runtime for sizes and primitive arguments. -/
inductive NumExpr (n : Nat) where
  | var (index : Fin n)
  | finite (value : Nat)
  | infinite
  | add (left right : NumExpr n)
  | mul (left right : NumExpr n)
  | min (left right : NumExpr n)
  deriving DecidableEq, Repr

/-- Evaluate numeric arguments under an explicit numeric instantiation. -/
@[expose] def NumExpr.eval {n : Nat} (ρ : Fin n → Length) : NumExpr n → Length
  | .var i => ρ i
  | .finite m => .finite m
  | .infinite => .infinite
  | .add a b => Length.add (a.eval ρ) (b.eval ρ)
  | .mul a b => Length.mul (a.eval ρ) (b.eval ρ)
  | .min a b => Length.min (a.eval ρ) (b.eval ρ)

/-- Value types; products also encode finite tuples and named record spines. -/
inductive Ty (N V : Type) where
  | var (index : V)
  | bit
  | integer
  | unit
  | seq (length : N) (element : Ty N V)
  | prod (left right : Ty N V)
  | arrow (argument result : Ty N V)
  deriving DecidableEq, Repr

/-- Closed semantic types with evaluated numeric arguments. -/
abbrev ClosedTy := Ty Length Empty

/-- Symbolic types scoped by numeric and value quantifiers. -/
abbrev PolyTy (n v : Nat) := Ty (NumExpr n) (Fin v)

/-- Interpret a type at an explicit assignment to both kinds of variables. -/
@[expose] def Ty.instantiate {N V M W : Type} (ρ : N → M) (θ : V → Ty M W) :
    Ty N V → Ty M W
  | .var i => θ i
  | .bit => .bit
  | .integer => .integer
  | .unit => .unit
  | .seq l a => .seq (ρ l) (a.instantiate ρ θ)
  | .prod a b => .prod (a.instantiate ρ θ) (b.instantiate ρ θ)
  | .arrow a b => .arrow (a.instantiate ρ θ) (b.instantiate ρ θ)

/-- Explicit numeric constraints supported by the pilot. -/
inductive Constraint (n : Nat) where
  | fin (length : NumExpr n)
  | eq (left right : NumExpr n)
  deriving DecidableEq, Repr

/-- Satisfaction of a checked numeric constraint. -/
@[expose] def Constraint.Holds {n : Nat} (ρ : Fin n → Length) : Constraint n → Prop
  | .fin l => ∃ k, l.eval ρ = .finite k
  | .eq a b => a.eval ρ = b.eval ρ

/-- A prenex polymorphic type with explicit constraints. -/
structure Schema where
  /-- Number of numeric parameters. -/
  numericArity : Nat
  /-- Number of value-type parameters. -/
  typeArity : Nat
  /-- Assumptions checked at each instantiation. -/
  constraints : List (Constraint numericArity)
  /-- The quantified type. -/
  body : PolyTy numericArity typeArity
  deriving Repr

/-- A valid schema instantiation, with numeric arguments retained. -/
structure Schema.Instantiation (schema : Schema) where
  /-- Actual numeric arguments. -/
  numbers : Fin schema.numericArity → Length
  /-- Actual value types. -/
  types : Fin schema.typeArity → ClosedTy
  /-- Evidence for every declared constraint. -/
  valid : ∀ c ∈ schema.constraints, c.Holds numbers

/-- Typed variables use PolyFun's shared scoped representation. -/
abbrev Var {α : Type} : List α → α → Type := @IPFunctor.ScopedVar α

namespace Var
export IPFunctor.ScopedVar (zero succ index)
end Var


end Interop.Cryptol
