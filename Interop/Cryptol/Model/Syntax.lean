/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Interop.Cryptol.Model.Types

/-!
# Typed, finite descriptions of lazy programs

Binders use typed de Bruijn variables. Sequence construction stores a finite
generator body with an integer index binder, even for an infinite sequence.
General recursion is explicit. A recursive group can be represented by a
fixed point at a product type, with lazy projections for its members.
-/

public section

namespace Interop.Cryptol

/-- Observable evaluation errors, separate from running out of fuel. -/
inductive EvalError where
  | user (message : String)
  | invalidIndex (index : Int)
  | divideByZero
  deriving DecidableEq, Repr

/-- Strict binary operations on integers. -/
inductive IntOp where
  | add | sub | mul | div | mod
  deriving DecidableEq, Repr

/-- Strict binary bit operations. -/
inductive BitOp where
  | and | or | xor
  deriving DecidableEq, Repr

/-- An intrinsically typed core expression, abstract over numeric arguments
and value-type variables. Every recursive child is finite syntax. -/
inductive Expr {N V : Type} : List (Ty N V) → Ty N V → Type where
  | var {Γ a} (index : Var Γ a) : Expr Γ a
  | bit {Γ} (value : Bool) : Expr Γ .bit
  | integer {Γ} (value : Int) : Expr Γ .integer
  | unit {Γ} : Expr Γ .unit
  | error {Γ a} (error : EvalError) : Expr Γ a
  | lam {Γ a b} (body : Expr (a :: Γ) b) : Expr Γ (.arrow a b)
  | app {Γ a b} (function : Expr Γ (.arrow a b)) (argument : Expr Γ a) : Expr Γ b
  | letE {Γ a b} (value : Expr Γ a) (body : Expr (a :: Γ) b) : Expr Γ b
  /-- Demand an outer value without demanding its lazy components. -/
  | force {Γ a b} (value : Expr Γ a) (next : Expr Γ b) : Expr Γ b
  | pair {Γ a b} (left : Expr Γ a) (right : Expr Γ b) : Expr Γ (.prod a b)
  | fst {Γ a b} (pair : Expr Γ (.prod a b)) : Expr Γ a
  | snd {Γ a b} (pair : Expr Γ (.prod a b)) : Expr Γ b
  | generate {Γ a} (length : N) (body : Expr (.integer :: Γ) a) : Expr Γ (.seq length a)
  | index {Γ a length} (sequence : Expr Γ (.seq length a)) (index : Expr Γ .integer) :
      Expr Γ a
  | ite {Γ a} (condition : Expr Γ .bit) (yes no : Expr Γ a) : Expr Γ a
  | fix {Γ a} (body : Expr (a :: Γ) a) : Expr Γ a
  | bitNot {Γ} (value : Expr Γ .bit) : Expr Γ .bit
  | bitOp {Γ} (op : BitOp) (left right : Expr Γ .bit) : Expr Γ .bit
  | intOp {Γ} (op : IntOp) (left right : Expr Γ .integer) : Expr Γ .integer
  | intEq {Γ} (left right : Expr Γ .integer) : Expr Γ .bit
  | intLt {Γ} (left right : Expr Γ .integer) : Expr Γ .bit

/-- Core expressions after all numeric and value-type parameters are instantiated. -/
abbrev ClosedExpr (Γ : List ClosedTy) (a : ClosedTy) := Expr Γ a

namespace Expr

variable {N V : Type} {Γ Δ Ξ : List (Ty N V)} {a b : Ty N V}

/-- A type-preserving map between variable scopes. -/
abbrev Renaming (Γ Δ : List (Ty N V)) := ∀ {a}, Var Γ a → Var Δ a

/-- Extend a renaming under a binder. -/
@[expose] def Renaming.lift (ρ : Renaming Γ Δ) : Renaming (a :: Γ) (a :: Δ)
  | _, .zero => .zero
  | _, .succ x => .succ (ρ x)

/-- Capture-avoiding variable renaming. -/
@[expose] def rename {Γ Δ : List (Ty N V)} {a : Ty N V}
    (ρ : Renaming Γ Δ) : Expr Γ a → Expr Δ a
  | .var x => .var (ρ x)
  | .bit x => .bit x
  | .integer x => .integer x
  | .unit => .unit
  | .error e => .error e
  | .lam e => .lam (e.rename ρ.lift)
  | .app f x => .app (f.rename ρ) (x.rename ρ)
  | .letE x e => .letE (x.rename ρ) (e.rename ρ.lift)
  | .force x e => .force (x.rename ρ) (e.rename ρ)
  | .pair x y => .pair (x.rename ρ) (y.rename ρ)
  | .fst x => .fst (x.rename ρ)
  | .snd x => .snd (x.rename ρ)
  | .generate n e => .generate n (e.rename ρ.lift)
  | .index xs i => .index (xs.rename ρ) (i.rename ρ)
  | .ite p x y => .ite (p.rename ρ) (x.rename ρ) (y.rename ρ)
  | .fix e => .fix (e.rename ρ.lift)
  | .bitNot x => .bitNot (x.rename ρ)
  | .bitOp op x y => .bitOp op (x.rename ρ) (y.rename ρ)
  | .intOp op x y => .intOp op (x.rename ρ) (y.rename ρ)
  | .intEq x y => .intEq (x.rename ρ) (y.rename ρ)
  | .intLt x y => .intLt (x.rename ρ) (y.rename ρ)

/-- A simultaneous substitution of suspended expressions for variables. -/
abbrev Substitution (Γ Δ : List (Ty N V)) := ∀ {a}, Var Γ a → Expr Δ a

/-- Extend substitution under a binder, shifting all suspended expressions. -/
@[expose] def Substitution.lift (σ : Substitution Γ Δ) : Substitution (a :: Γ) (a :: Δ)
  | _, .zero => .var .zero
  | _, .succ x => (σ x).rename Var.succ

/-- Capture-avoiding simultaneous substitution. -/
@[expose] def subst {Γ Δ : List (Ty N V)} {a : Ty N V}
    (σ : Substitution Γ Δ) : Expr Γ a → Expr Δ a
  | .var x => σ x
  | .bit x => .bit x
  | .integer x => .integer x
  | .unit => .unit
  | .error e => .error e
  | .lam e => .lam (e.subst σ.lift)
  | .app f x => .app (f.subst σ) (x.subst σ)
  | .letE x e => .letE (x.subst σ) (e.subst σ.lift)
  | .force x e => .force (x.subst σ) (e.subst σ)
  | .pair x y => .pair (x.subst σ) (y.subst σ)
  | .fst x => .fst (x.subst σ)
  | .snd x => .snd (x.subst σ)
  | .generate n e => .generate n (e.subst σ.lift)
  | .index xs i => .index (xs.subst σ) (i.subst σ)
  | .ite p x y => .ite (p.subst σ) (x.subst σ) (y.subst σ)
  | .fix e => .fix (e.subst σ.lift)
  | .bitNot x => .bitNot (x.subst σ)
  | .bitOp op x y => .bitOp op (x.subst σ) (y.subst σ)
  | .intOp op x y => .intOp op (x.subst σ) (y.subst σ)
  | .intEq x y => .intEq (x.subst σ) (y.subst σ)
  | .intLt x y => .intLt (x.subst σ) (y.subst σ)

/-- Replace the innermost bound variable with a suspended expression. -/
@[expose] def substOne (body : Expr (a :: Γ) b) (argument : Expr Γ a) : Expr Γ b :=
  body.subst (fun {t} (x : Var (a :: Γ) t) => match x with
    | .zero => argument
    | .succ x => .var x)

/-- Instantiate both kinds of parameters, preserving variable scopes and types. -/
@[expose] def instantiate {M W : Type} (ρ : N → M) (θ : V → Ty M W) :
    {Γ : List (Ty N V)} → {a : Ty N V} →
    Expr Γ a → Expr (Γ.map (Ty.instantiate ρ θ)) (a.instantiate ρ θ)
  | _, _, .var x => .var (varMap x)
  | _, _, .bit x => .bit x
  | _, _, .integer x => .integer x
  | _, _, .unit => .unit
  | _, _, .error e => .error e
  | _, _, .lam e => .lam (e.instantiate ρ θ)
  | _, _, .app f x => .app (f.instantiate ρ θ) (x.instantiate ρ θ)
  | _, _, .letE x e => .letE (x.instantiate ρ θ) (e.instantiate ρ θ)
  | _, _, .force x e => .force (x.instantiate ρ θ) (e.instantiate ρ θ)
  | _, _, .pair x y => .pair (x.instantiate ρ θ) (y.instantiate ρ θ)
  | _, _, .fst x => .fst (x.instantiate ρ θ)
  | _, _, .snd x => .snd (x.instantiate ρ θ)
  | _, _, .generate n e => .generate (ρ n) (e.instantiate ρ θ)
  | _, _, .index xs i => .index (xs.instantiate ρ θ) (i.instantiate ρ θ)
  | _, _, .ite p x y => .ite (p.instantiate ρ θ) (x.instantiate ρ θ) (y.instantiate ρ θ)
  | _, _, .fix e => .fix (e.instantiate ρ θ)
  | _, _, .bitNot x => .bitNot (x.instantiate ρ θ)
  | _, _, .bitOp op x y => .bitOp op (x.instantiate ρ θ) (y.instantiate ρ θ)
  | _, _, .intOp op x y => .intOp op (x.instantiate ρ θ) (y.instantiate ρ θ)
  | _, _, .intEq x y => .intEq (x.instantiate ρ θ) (y.instantiate ρ θ)
  | _, _, .intLt x y => .intLt (x.instantiate ρ θ) (y.instantiate ρ θ)
where
  /-- Instantiation preserves de Bruijn positions while replacing their types. -/
  varMap {Γ a} : Var Γ a → Var (Γ.map (Ty.instantiate ρ θ)) (a.instantiate ρ θ)
    | .zero => .zero
    | .succ x => .succ (varMap x)

end Expr

/-- A type abstraction with a checked schema and a finite typed body. -/
structure Definition (schema : Schema) where
  /-- The expression under the schema's numeric and value-type binders. -/
  body : Expr [] schema.body

/-- Type application to a checked schema instantiation. -/
@[expose] def Definition.instantiate {schema : Schema} (definition : Definition schema)
    (arguments : schema.Instantiation) :
    Expr [] (schema.body.instantiate (NumExpr.eval arguments.numbers) arguments.types) :=
  definition.body.instantiate (NumExpr.eval arguments.numbers) arguments.types

end Interop.Cryptol
