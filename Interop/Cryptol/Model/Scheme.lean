/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Interop.Cryptol.Model.ParameterLaws
public import Interop.Cryptol.Model.ParameterSubstitutionLaws
public import Interop.Cryptol.Model.Domain
public import PolyFun.Control.Domain.Pointed

/-!
# Ordered schemes and staged polymorphic domains

Numeric and value-type quantifiers retain their order. Each quantifier adds one
outer suspension; proof assumptions introduce only an erased proof argument.
The leaf domain is the existing lazy computation domain at an instantiated type.
-/

public section

namespace Interop.Cryptol.Polymorphic

/-- A rank-one scheme under open numeric and value-type parameter scopes. -/
inductive Scheme : Nat → Nat → Type where
  | mono {n v} (type : PolyTy n v) : Scheme n v
  | allNum {n v} (body : Scheme (n + 1) v) : Scheme n v
  | allType {n v} (body : Scheme n (v + 1)) : Scheme n v
  | guard {n v} (constraint : Constraint n) (body : Scheme n v) : Scheme n v

namespace Scheme

/-- Substitute parameters, lifting under each quantifier of the appropriate kind. -/
@[expose] def subst {n v m w : Nat} (σ : ParameterSubstitution n v m w) :
    Scheme n v → Scheme m w
  | .mono a => .mono (σ.apply a)
  | .allNum s => .allNum (s.subst σ.liftNum)
  | .allType s => .allType (s.subst σ.liftType)
  | .guard c s => .guard (c.subst σ.numbers) (s.subst σ)

@[simp] theorem subst_id {n v : Nat} (s : Scheme n v) :
    s.subst (ParameterSubstitution.id n v) = s := by
  induction s with
  | mono a => rw [subst, ParameterSubstitution.apply_id]
  | allNum s ih => rw [subst, ParameterSubstitution.liftNum_id, ih]
  | allType s ih => rw [subst, ParameterSubstitution.liftType_id, ih]
  | guard c s ih =>
      change guard (c.subst .var) (s.subst (ParameterSubstitution.id _ _)) = guard c s
      rw [Constraint.subst_id, ih]

/-- Ordered schemes preserve composition, including below mixed quantifiers. -/
theorem subst_subst {n v m w k u : Nat} (s : Scheme n v)
    (σ : ParameterSubstitution n v m w) (τ : ParameterSubstitution m w k u) :
    (s.subst σ).subst τ = s.subst (σ.comp τ) := by
  induction s generalizing m w k u with
  | mono a => simp only [subst, ParameterSubstitution.apply_comp]
  | allNum s ih => simp only [subst, ih, ParameterSubstitution.liftNum_comp]
  | allType s ih => simp only [subst, ih, ParameterSubstitution.liftType_comp]
  | guard c s ih => simp only [subst, ih, Constraint.subst_subst, ParameterSubstitution.comp]

/-- The lazy computation domain of a scheme at an assignment of its free parameters. -/
@[expose, implicit_reducible] noncomputable def domain {n v : Nat} :
    Scheme n v → ParameterAssignment n v → PointedDomain
  | .mono a, ρ => .ofType (Computation (ρ.apply a))
  | .allNum s, ρ => .result EvalError (.pi Length (fun l => s.domain (ρ.extendNum l)))
  | .allType s, ρ => .result EvalError (.pi ClosedTy (fun a => s.domain (ρ.extendType a)))
  | .guard c s, ρ => .pi (PLift (c.Holds ρ.numbers)) (fun _ => s.domain ρ)

/-- A scheme computation retains every stage's bottom and errors. -/
abbrev Meaning {n v : Nat} (s : Scheme n v) (ρ : ParameterAssignment n v) : Type := s.domain ρ

/-- Numeric and type substitution preserve the interpreted domain, including its order. -/
theorem domain_subst {n v m w : Nat} (s : Scheme n v)
    (σ : ParameterSubstitution n v m w) (ρ : ParameterAssignment m w) :
    (s.subst σ).domain ρ = s.domain (ρ.pull σ) := by
  induction s generalizing m w with
  | mono a =>
      change PointedDomain.ofType (Computation (ρ.apply (σ.apply a))) = _
      rw [ParameterAssignment.apply_subst]
      rfl
  | allNum s ih =>
      change PointedDomain.result EvalError (PointedDomain.pi Length _) =
        PointedDomain.result EvalError (PointedDomain.pi Length _)
      congr 2
      funext l
      rw [ih, ParameterAssignment.pull_liftNum]
  | allType s ih =>
      change PointedDomain.result EvalError (PointedDomain.pi ClosedTy _) =
        PointedDomain.result EvalError (PointedDomain.pi ClosedTy _)
      congr 2
      funext a
      rw [ih, ParameterAssignment.pull_liftType]
  | guard c s ih =>
      change PointedDomain.pi (PLift ((c.subst σ.numbers).Holds ρ.numbers)) _ =
        PointedDomain.pi (PLift (c.Holds (ρ.pull σ).numbers)) _
      have hc : (c.subst σ.numbers).Holds ρ.numbers = c.Holds (ρ.pull σ).numbers :=
        propext (Constraint.holds_subst c σ.numbers ρ.numbers)
      simp only [ih]
      exact congrArg (fun p : Prop => PointedDomain.pi (PLift p)
        (fun _ => s.domain (ρ.pull σ))) hc

/-- Errors propagate through erased proof assumptions without adding a suspension. -/
@[expose] noncomputable def error {n v : Nat} :
    (s : Scheme n v) → (ρ : ParameterAssignment n v) → EvalError → s.Meaning ρ
  | .mono _, _, e => .error e
  | .allNum _, _, e => .error e
  | .allType _, _, e => .error e
  | .guard _ s, ρ, e => fun _ => s.error ρ e

end Scheme
end Interop.Cryptol.Polymorphic
