/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Interop.Cryptol.Model.Types

/-!
# Substitution of numeric and value-type parameters

Parameters of the two kinds have separate de Bruijn scopes. Substitution retains
numeric expressions, acts on types and constraints, and commutes with evaluation.
Lifting under either kind of quantifier protects its newly bound parameter.
-/

public section

namespace Interop.Cryptol

namespace NumExpr

/-- Simultaneously replace the numeric variables of an expression. -/
@[expose] def subst {n m : Nat} (σ : Fin n → NumExpr m) : NumExpr n → NumExpr m
  | .var i => σ i
  | .finite k => .finite k
  | .infinite => .infinite
  | .add a b => .add (a.subst σ) (b.subst σ)
  | .mul a b => .mul (a.subst σ) (b.subst σ)
  | .min a b => .min (a.subst σ) (b.subst σ)

/-- Rename numeric variables without changing their expressions. -/
@[expose] def rename {n m : Nat} (ρ : Fin n → Fin m) (e : NumExpr n) : NumExpr m :=
  e.subst (fun i => .var (ρ i))

@[simp] theorem subst_var {n m : Nat} (σ : Fin n → NumExpr m) (i : Fin n) :
    (var i).subst σ = σ i := rfl

@[simp] theorem subst_id {n : Nat} (e : NumExpr n) : e.subst .var = e := by
  induction e <;> simp_all [subst]

/-- Numeric substitutions compose before evaluation. -/
theorem subst_subst {n m k : Nat} (e : NumExpr n)
    (σ : Fin n → NumExpr m) (τ : Fin m → NumExpr k) :
    (e.subst σ).subst τ = e.subst (fun i => (σ i).subst τ) := by
  induction e <;> simp_all [subst]

/-- Evaluate a substituted numeric expression by composing its assignments. -/
theorem eval_subst {n m : Nat} (e : NumExpr n) (σ : Fin n → NumExpr m)
    (ρ : Fin m → Length) : (e.subst σ).eval ρ = e.eval (fun i => (σ i).eval ρ) := by
  induction e <;> simp_all [subst, eval]

end NumExpr

namespace Ty

@[simp] theorem instantiate_id {N V : Type} (a : Ty N V) :
    a.instantiate id .var = a := by
  induction a <;> simp_all [instantiate]

/-- Type instantiation composes its numeric maps and substituted value types. -/
theorem instantiate_instantiate {N V M W K U : Type} (a : Ty N V)
    (ρ : N → M) (θ : V → Ty M W) (τ : M → K) (ψ : W → Ty K U) :
    (a.instantiate ρ θ).instantiate τ ψ =
      a.instantiate (τ ∘ ρ) (fun i => (θ i).instantiate τ ψ) := by
  induction a <;> simp_all [instantiate]

end Ty

/-- Simultaneous substitution of the two parameter kinds. -/
structure ParameterSubstitution (n v m w : Nat) where
  /-- Numeric arguments, still represented as finite symbolic expressions. -/
  numbers : Fin n → NumExpr m
  /-- Value-type arguments in the target parameter scopes. -/
  types : Fin v → PolyTy m w

namespace ParameterSubstitution

/-- Apply a parameter substitution to a symbolic type. -/
@[expose] def apply {n v m w : Nat} (σ : ParameterSubstitution n v m w)
    (a : PolyTy n v) : PolyTy m w := a.instantiate (NumExpr.subst σ.numbers) σ.types

/-- Identity parameter substitution. -/
@[expose] def id (n v : Nat) : ParameterSubstitution n v n v := ⟨.var, .var⟩

/-- First apply the left substitution, then the right substitution. -/
@[expose] def comp {n v m w k u : Nat} (σ : ParameterSubstitution n v m w)
    (τ : ParameterSubstitution m w k u) : ParameterSubstitution n v k u :=
  ⟨fun i => (σ.numbers i).subst τ.numbers, fun i => τ.apply (σ.types i)⟩

@[simp] theorem apply_id {n v : Nat} (a : PolyTy n v) : (id n v).apply a = a := by
  change a.instantiate (NumExpr.subst .var) .var = a
  rw [show NumExpr.subst (@NumExpr.var n) = _root_.id from funext NumExpr.subst_id]
  exact Ty.instantiate_id a

theorem apply_comp {n v m w k u : Nat} (σ : ParameterSubstitution n v m w)
    (τ : ParameterSubstitution m w k u) (a : PolyTy n v) :
    (σ.comp τ).apply a = τ.apply (σ.apply a) := by
  simp only [apply, comp, Ty.instantiate_instantiate]
  congr 1
  funext e
  exact (NumExpr.subst_subst e σ.numbers τ.numbers).symm

/-- Enter one numeric parameter, shifting only the older numeric arguments. -/
@[expose] def weakenNum (n v : Nat) : ParameterSubstitution n v (n + 1) v :=
  ⟨fun i => .var i.succ, .var⟩

/-- Enter one value-type parameter, shifting only the older value-type arguments. -/
@[expose] def weakenType (n v : Nat) : ParameterSubstitution n v n (v + 1) :=
  ⟨.var, fun i => .var i.succ⟩

/-- Lift a substitution past a freshly bound numeric variable. -/
@[expose] def liftNum {n v m w : Nat} (σ : ParameterSubstitution n v m w) :
    ParameterSubstitution (n + 1) v (m + 1) w where
  numbers := Fin.cases (.var 0) (fun i => (σ.numbers i).rename Fin.succ)
  types i := (weakenNum m w).apply (σ.types i)

/-- Lift a substitution past a freshly bound value-type variable. -/
@[expose] def liftType {n v m w : Nat} (σ : ParameterSubstitution n v m w) :
    ParameterSubstitution n (v + 1) m (w + 1) where
  numbers := σ.numbers
  types := Fin.cases (.var 0) (fun i => (weakenType m w).apply (σ.types i))

/-- Replace the nearest numeric variable. -/
@[expose] def singleNum {n v : Nat} (e : NumExpr n) :
    ParameterSubstitution (n + 1) v n v := ⟨Fin.cases e .var, .var⟩

/-- Replace the nearest value-type variable. -/
@[expose] def singleType {n v : Nat} (a : PolyTy n v) :
    ParameterSubstitution n (v + 1) n v := ⟨.var, Fin.cases a .var⟩

/-- A substitution is determined by its numeric and value-type components. -/
@[ext] theorem ext {n v m w : Nat} {σ τ : ParameterSubstitution n v m w}
    (hn : σ.numbers = τ.numbers) (ht : σ.types = τ.types) : σ = τ := by
  cases σ
  cases τ
  cases hn
  cases ht
  rfl

@[simp] theorem id_comp {n v m w : Nat} (σ : ParameterSubstitution n v m w) :
    (id n v).comp σ = σ := by
  ext <;> rfl

@[simp] theorem comp_id {n v m w : Nat} (σ : ParameterSubstitution n v m w) :
    σ.comp (id m w) = σ := by
  apply ext
  · funext i
    exact NumExpr.subst_id _
  · funext i
    exact apply_id _

/-- Composition of parameter substitutions is associative. -/
theorem comp_assoc {n v m w k u l t : Nat} (σ : ParameterSubstitution n v m w)
    (τ : ParameterSubstitution m w k u) (υ : ParameterSubstitution k u l t) :
    (σ.comp τ).comp υ = σ.comp (τ.comp υ) := by
  apply ext
  · funext i
    exact NumExpr.subst_subst _ _ _
  · funext i
    exact (apply_comp _ _ _).symm

@[simp] theorem liftNum_id (n v : Nat) : (id n v).liftNum = id (n + 1) v := by
  apply ext
  · funext i
    cases i using Fin.cases <;> rfl
  · rfl

@[simp] theorem liftType_id (n v : Nat) : (id n v).liftType = id n (v + 1) := by
  apply ext
  · rfl
  · funext i
    cases i using Fin.cases <;> rfl

end ParameterSubstitution

/-- A semantic assignment to both parameter scopes. -/
structure ParameterAssignment (n v : Nat) where
  /-- Evaluated numeric parameters. -/
  numbers : Fin n → Length
  /-- Closed value types. -/
  types : Fin v → ClosedTy

namespace ParameterAssignment

/-- Interpret a symbolic type under the assignment. -/
@[expose] def apply {n v : Nat} (ρ : ParameterAssignment n v) (a : PolyTy n v) : ClosedTy :=
  a.instantiate (NumExpr.eval ρ.numbers) ρ.types

/-- Pull an assignment back along a symbolic substitution. -/
@[expose] def pull {n v m w : Nat} (ρ : ParameterAssignment m w)
    (σ : ParameterSubstitution n v m w) : ParameterAssignment n v where
  numbers i := (σ.numbers i).eval ρ.numbers
  types i := ρ.apply (σ.types i)

/-- Type interpretation commutes with parameter substitution. -/
theorem apply_subst {n v m w : Nat} (ρ : ParameterAssignment m w)
    (σ : ParameterSubstitution n v m w) (a : PolyTy n v) :
    ρ.apply (σ.apply a) = (ρ.pull σ).apply a := by
  simp only [apply, ParameterSubstitution.apply, Ty.instantiate_instantiate, pull]
  congr 1
  funext e
  exact NumExpr.eval_subst e σ.numbers ρ.numbers

/-- Extend the numeric assignment at the nearest binder. -/
@[expose] def extendNum {n v : Nat} (ρ : ParameterAssignment n v) (l : Length) :
    ParameterAssignment (n + 1) v := ⟨Fin.cases l ρ.numbers, ρ.types⟩

/-- Extend the value-type assignment at the nearest binder. -/
@[expose] def extendType {n v : Nat} (ρ : ParameterAssignment n v) (a : ClosedTy) :
    ParameterAssignment n (v + 1) := ⟨ρ.numbers, Fin.cases a ρ.types⟩

end ParameterAssignment

namespace Constraint

/-- Substitute the numeric parameters in a supported constraint. -/
@[expose] def subst {n m : Nat} (σ : Fin n → NumExpr m) : Constraint n → Constraint m
  | .fin e => .fin (e.subst σ)
  | .eq a b => .eq (a.subst σ) (b.subst σ)

/-- Constraint evidence transports by the same assignment composition as numeric evaluation. -/
theorem holds_subst {n m : Nat} (c : Constraint n) (σ : Fin n → NumExpr m)
    (ρ : Fin m → Length) : (c.subst σ).Holds ρ ↔ c.Holds (fun i => (σ i).eval ρ) := by
  cases c <;> simp only [subst, Holds, NumExpr.eval_subst]

end Constraint
end Interop.Cryptol
