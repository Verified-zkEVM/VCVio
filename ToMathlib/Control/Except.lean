/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module
public import Mathlib.Init
public import Mathlib.Basic.Countable.Basic

/-!
# Exceptional monad equations and countability

Binding a successful result runs its continuation; binding an error preserves that error.
Both equations normalize exceptional programs with `simp` and `grind`.
Countable error and value types give a countable exceptional outcome type.
-/

public section

namespace Except

universe u v

variable {ε : Type u} {α β : Type v}

/-- Exceptions over countable error and value types are countable. -/
instance [Countable ε] [Countable α] : Countable (Except ε α) :=
  Function.Injective.countable (f := fun x : Except ε α => match x with
    | .error err => (Sum.inl err : ε ⊕ α)
    | .ok value => Sum.inr value) (by
      intro x y h
      cases x <;> cases y <;> simp_all)

/-- Pure exceptional computations are successful results. -/
@[simp, grind =]
lemma pure_apply (x : α) : (pure x : Except ε α) = Except.ok x := rfl

/-- Binding a successful exceptional result runs the continuation. -/
@[simp, grind =]
lemma bind_ok (x : α) (f : α → Except ε β) : (Except.ok x : Except ε α) >>= f = f x := rfl

/-- Binding an error preserves the error without running the continuation. -/
@[simp, grind =]
lemma bind_error (error : ε) (f : α → Except ε β) :
    (Except.error error : Except ε α) >>= f = Except.error error := rfl

end Except

/-- A direct core monad lift returns a successful exceptional result. -/
@[simp]
theorem ExceptT.run_core_monadLift.{v} {m : Type → Type v} [Monad m] {ε α : Type} (x : m α) :
    (MonadLift.monadLift x : ExceptT ε m α).run = Except.ok <$> x := rfl
