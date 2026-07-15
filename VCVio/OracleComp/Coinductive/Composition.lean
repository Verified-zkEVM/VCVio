/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import VCVio.OracleComp.Coinductive.Machine

/-!
# Composition of Implementing Oracle Machines

This file specializes PolyFun's fuel-exact sequential composition of pointed machines to
`OracleComp`. Machines implementing two program stages compose into a machine implementing their
monadic bind, with the two query budgets added.
-/

universe u

open OracleSpec PFunctor

variable {ι : Type u} {spec : OracleSpec.{u, u} ι} {α mid β : Type u}

namespace OracleMachine

/-- Sequential composition of implementing machines implements the bind of their programs. -/
theorem Implements.seqComp {M₁ : OracleMachine spec α mid} {M₂ : OracleMachine spec mid β}
    {oa : α → OracleComp spec mid} {ob : mid → OracleComp spec β} {k₁ k₂ : ℕ}
    (h₁ : M₁ ⊨[k₁] oa) (h₂ : M₂ ⊨[k₂] ob) :
    M₁ ⨟ M₂ ⊨[k₁ + k₂] fun x => oa x >>= ob := by
  apply Implements.of_runK_eq
  intro m _ _ H x
  rw [show OracleMachine.runK (M₁ ⨟ M₂) H (k₁ + k₂) ((M₁ ⨟ M₂).init x) =
      (M₁ ⨟ M₂).runWith H (k₁ + k₂) ((M₁ ⨟ M₂).init x) from rfl,
    PFunctor.DynSystem.IOMachine.runWith_seqComp_init M₁ M₂ H k₂ x
      (PFunctor.DynSystem.IOMachine.Implements.resolvesIn h₁ x)
      (fun y => PFunctor.DynSystem.IOMachine.Implements.resolvesIn h₂ y),
    show M₁.runWith H k₁ (M₁.init x) = M₁.runK H k₁ (M₁.init x) from rfl,
    h₁.runK_eq H x, simulateQ_bind, map_eq_bind_pure_comp, bind_assoc, map_bind]
  refine bind_congr fun a => ?_
  rw [Function.comp_apply, pure_bind]
  exact h₂.runK_eq H a

end OracleMachine
