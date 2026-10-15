/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Interop.Cryptol.Model.Syntax
public import PolyFun.Control.Domain.Result

/-!
# Lazy semantic domains

Sequence elements and tuple components are computations. Function values are
continuous maps from computations to computations, so an unused argument
need not return. The outer computation separately records bottom, an error,
or the availability of the value's outer constructor.
-/

public section

open OmegaCompletePartialOrder

namespace Interop.Cryptol

/-- A value carrier with its information order and increasing suprema. -/
structure ValueDomain where
  /-- The semantic values. -/
  Carrier : Type
  /-- Their information order. -/
  order : OmegaCompletePartialOrder Carrier

attribute [instance] ValueDomain.order

instance : CoeSort ValueDomain Type := ⟨ValueDomain.Carrier⟩

/-- The value domain of a closed type. Its reduction computes the carrier
types of fields, arguments, and sequence positions in dependent APIs. -/
@[expose, implicit_reducible] noncomputable def valueDomain : ClosedTy → ValueDomain
  | .var e => e.elim
  | .bit => ⟨DiscreteOrder Bool, inferInstance⟩
  | .integer => ⟨DiscreteOrder Int, inferInstance⟩
  | .unit => ⟨DiscreteOrder Unit, inferInstance⟩
  | .seq l a => ⟨l.Index → DomainResult EvalError (valueDomain a), inferInstance⟩
  | .prod a b =>
      ⟨DomainResult EvalError (valueDomain a) × DomainResult EvalError (valueDomain b),
        inferInstance⟩
  | .arrow a b =>
      ⟨DomainResult EvalError (valueDomain a) →𝒄 DomainResult EvalError (valueDomain b),
        inferInstance⟩

/-- Semantic values at a type. -/
abbrev Value (a : ClosedTy) : Type := valueDomain a

/-- Possibly divergent or erroneous computations at a type. -/
abbrev Computation (a : ClosedTy) : Type := DomainResult EvalError (Value a)

/-- A semantic environment supplies a suspended computation for each variable. -/
abbrev Environment (Γ : List ClosedTy) := ∀ a, Var Γ a → Computation a

namespace Environment

/-- Extend an environment with one suspended computation. -/
@[expose] def extend {Γ : List ClosedTy} {a : ClosedTy} (ρ : Environment Γ)
    (x : Computation a) : Environment (a :: Γ) := fun _ v => match v with
  | .zero => x
  | .succ v => ρ _ v

@[simp] theorem extend_zero {Γ : List ClosedTy} {a : ClosedTy} (ρ : Environment Γ)
    (x : Computation a) : ρ.extend x a .zero = x := rfl

@[simp] theorem extend_succ {Γ : List ClosedTy} {a b : ClosedTy} (ρ : Environment Γ)
    (x : Computation a) (v : Var Γ b) : ρ.extend x b (.succ v) = ρ b v := rfl

/-- Extending environments is jointly continuous. -/
@[expose] noncomputable def extendContinuous {Γ : List ClosedTy} {a : ClosedTy} :
    (Environment Γ × Computation a) →𝒄 Environment (a :: Γ) :=
  .ofFun (fun p => extend p.1 p.2) (by
    apply ωScottContinuous.of_apply₂
    intro b
    apply ωScottContinuous.of_apply₂
    intro v
    cases v with
    | zero => exact Prod.ωScottContinuous_snd
    | succ v =>
        exact (ωScottContinuous.apply v).comp
          ((ωScottContinuous.apply b).comp Prod.ωScottContinuous_fst))

/-- Continuous environment extension has the ordinary lookup equations. -/
@[simp] theorem extendContinuous_apply {Γ : List ClosedTy} {a : ClosedTy}
    (p : Environment Γ × Computation a) : extendContinuous p = p.1.extend p.2 := rfl

/-- The unique environment of a closed term. -/
@[expose] def empty : Environment [] := fun _ v => nomatch v

end Environment

end Interop.Cryptol
