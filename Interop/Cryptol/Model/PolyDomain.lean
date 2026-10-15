/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Interop.Cryptol.Model.PolyScope
public import PolyFun.IPFunctor.Scoped.Domain

/-!
# Continuous environments and staged instantiation

Entering a parameter binder transports existing local values. Applying a
quantifier demands exactly its outer suspension. Constraint application passes
proof evidence and introduces no suspension of its own.
-/

public section

open OmegaCompletePartialOrder

namespace Interop.Cryptol.Polymorphic

/-- Values of local schemes at one valid parameter assignment. -/
abbrev Env {w : Scope} (ρ : w.Assignment) (Γ : List w.ValueSort) :=
  IPFunctor.ScopedDomain.Env (fun s => s.domain ρ.val) Γ

namespace Env

variable {w : Scope} (ρ : w.Assignment) {Γ : List w.ValueSort}

/-- The empty local environment. -/
@[expose] noncomputable def empty : Env ρ [] := IPFunctor.ScopedDomain.Env.empty _

/-- Normalize the identity context map at a constructor child. -/
@[expose] noncomputable def same : Env ρ Γ →𝒄 Env ρ (Γ.map id) :=
  IPFunctor.ScopedDomain.Env.reindex _ _ id (fun _ => rfl)

/-- Add a local suspended value. -/
@[expose] noncomputable def cons {s : w.ValueSort} :
    (Env ρ Γ × s.Meaning ρ.val) →𝒄 Env ρ (s :: Γ) :=
  (IPFunctor.ScopedDomain.Env.consContinuous _).comp (.ofFun (fun p => (p.2, p.1)))

/-- Add a whole recursive group of suspended values. -/
@[expose] noncomputable def append {Ξ : List w.ValueSort} :
    (Env ρ Ξ × Env ρ Γ) →𝒄 Env ρ (Ξ ++ Γ) :=
  IPFunctor.ScopedDomain.Env.appendContinuous _

/-- Enter a numeric abstraction without forcing any existing value. -/
@[expose] noncomputable def enterNum (l : Length) :
    Env ρ Γ →𝒄 Env (ρ.extendNum l)
      (Γ.map (Scheme.subst (ParameterSubstitution.weakenNum w.numbers w.types))) :=
  IPFunctor.ScopedDomain.Env.reindex _ _ _ (fun s => by
    rw [Scheme.domain_subst]
    change s.domain ((ρ.val.extendNum l).pull _) = s.domain ρ.val
    rw [ParameterAssignment.pull_weakenNum])

/-- Enter a value-type abstraction without forcing any existing value. -/
@[expose] noncomputable def enterType (a : ClosedTy) :
    Env ρ Γ →𝒄 Env (ρ.extendType a)
      (Γ.map (Scheme.subst (ParameterSubstitution.weakenType w.numbers w.types))) :=
  IPFunctor.ScopedDomain.Env.reindex _ _ _ (fun s => by
    rw [Scheme.domain_subst]
    change s.domain ((ρ.val.extendType a).pull _) = s.domain ρ.val
    rw [ParameterAssignment.pull_weakenType])

/-- Enter an erased proof abstraction. -/
@[expose] noncomputable def assume {c : Constraint w.numbers} (h : c.Holds ρ.val.numbers) :
    Env ρ Γ →𝒄 Env (ρ.assume h) (Γ.map id) := same ρ

end Env

namespace Scheme

/-- Domain equality for one numeric application. -/
theorem domain_singleNum {n v : Nat} (s : Scheme (n + 1) v)
    (a : NumExpr n) (ρ : ParameterAssignment n v) :
    (s.subst (ParameterSubstitution.singleNum a)).domain ρ =
      s.domain (ρ.extendNum (a.eval ρ.numbers)) := by
  rw [domain_subst, ParameterAssignment.pull_singleNum]

/-- Domain equality for one value-type application. -/
theorem domain_singleType {n v : Nat} (s : Scheme n (v + 1))
    (a : PolyTy n v) (ρ : ParameterAssignment n v) :
    (s.subst (ParameterSubstitution.singleType a)).domain ρ =
      s.domain (ρ.extendType (ρ.apply a)) := by
  rw [domain_subst, ParameterAssignment.pull_singleType]

/-- Demand a numeric abstraction and select its suspended body instance. -/
@[expose] noncomputable def applyNum {n v : Nat} (s : Scheme (n + 1) v)
    (a : NumExpr n) (ρ : ParameterAssignment n v) :
    (allNum s).Meaning ρ →𝒄 (s.subst (ParameterSubstitution.singleNum a)).Meaning ρ :=
  (PointedDomain.cast (domain_singleNum s a ρ).symm).comp
    (DomainResult.elim (s.error (ρ.extendNum (a.eval ρ.numbers)))
      (.ofFun (fun f => f (a.eval ρ.numbers))))

/-- Demand a type abstraction and select its suspended body instance. -/
@[expose] noncomputable def applyType {n v : Nat} (s : Scheme n (v + 1))
    (a : PolyTy n v) (ρ : ParameterAssignment n v) :
    (allType s).Meaning ρ →𝒄 (s.subst (ParameterSubstitution.singleType a)).Meaning ρ :=
  (PointedDomain.cast (domain_singleType s a ρ).symm).comp
    (DomainResult.elim (s.error (ρ.extendType (ρ.apply a)))
      (.ofFun (fun f => f (ρ.apply a))))

/-- Conditional evaluation at any scheme, including a proof-guarded scheme. -/
@[expose] noncomputable def conditional {n v : Nat} (s : Scheme n v)
    (ρ : ParameterAssignment n v) :
    (s.Meaning ρ × s.Meaning ρ) →𝒄 (Computation .bit →𝒄 s.Meaning ρ) :=
  (DomainResult.elimContinuous (s.error ρ)).comp
    ((DiscreteOrder.continuousMap fun b : Bool =>
      if b then (ContinuousHom.ofFun Prod.fst :
        (s.Meaning ρ × s.Meaning ρ) →𝒄 s.Meaning ρ)
      else ContinuousHom.ofFun Prod.snd).swapArgs)

end Scheme
end Interop.Cryptol.Polymorphic
