/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import PolyFun.Control.Monad.Algebra.Relational

/-!
# Automatic transformer algebras for relational laws

PolyFun provides the generic relational algebra, laws, and named transformer constructions.
This module installs its state, optional, and exception constructions for typeclass search.
-/

public section

universe u v₁ v₂

namespace MAlgRelOrdered

section State

variable {m₁ : Type u → Type v₁} {m₂ : Type u → Type v₂} {l : Type u}
  [Monad m₁] [Monad m₂] [LawfulMonad m₁] [LawfulMonad m₂] [Preorder l]
  [MAlgRelOrdered m₁ m₂ l]

/-- Left state transformer algebra. -/
noncomputable instance instStateTLeft (σ : Type u) :
    MAlgRelOrdered (StateT σ m₁) m₂ (σ → l) := stateTLeft σ

/-- Right state transformer algebra. -/
noncomputable instance instStateTRight (σ : Type u) :
    MAlgRelOrdered m₁ (StateT σ m₂) (σ → l) := stateTRight σ

/-- Two-sided state transformer algebra with explicit state order. -/
noncomputable instance instStateTBoth (σ₁ σ₂ : Type u) :
    MAlgRelOrdered (StateT σ₁ m₁) (StateT σ₂ m₂) (σ₁ → σ₂ → l) := stateTBoth σ₁ σ₂

end State

section Failure

variable {m₁ : Type u → Type v₁} {m₂ : Type u → Type v₂} {l : Type u}
  [Monad m₁] [Monad m₂] [LawfulMonad m₁] [LawfulMonad m₂] [Preorder l] [OrderBot l]
  [MAlgRelOrdered m₁ m₂ l]

/-- Right optional transformer algebra observing absent outputs as bottom. -/
noncomputable instance instOptionTRight : MAlgRelOrdered m₁ (OptionT m₂) l := optionTRight

/-- Left optional transformer algebra observing absent outputs as bottom. -/
noncomputable instance instOptionTLeft : MAlgRelOrdered (OptionT m₁) m₂ l := optionTLeft

/-- Right exception transformer algebra observing errors as bottom. -/
noncomputable instance instExceptTRight (ε : Type u) :
    MAlgRelOrdered m₁ (ExceptT ε m₂) l := exceptTRight ε

/-- Left exception transformer algebra observing errors as bottom. -/
noncomputable instance instExceptTLeft (ε : Type u) :
    MAlgRelOrdered (ExceptT ε m₁) m₂ l := exceptTLeft ε

end Failure

section Strict

variable {m₁ : Type u → Type v₁} {m₂ : Type u → Type v₂} {l : Type u}
  [Monad m₁] [Monad m₂] [LawfulMonad m₁] [LawfulMonad m₂] [Preorder l]
  [MAlgRelOrdered m₁ m₂ l] [StrictBind m₁ m₂ l]

/-- Strictness of the left state transformer algebra. -/
instance instStrictBindStateTLeft (σ : Type u) :
    StrictBind (StateT σ m₁) m₂ (σ → l) := strictBindStateTLeft σ

/-- Strictness of the right state transformer algebra. -/
instance instStrictBindStateTRight (σ : Type u) :
    StrictBind m₁ (StateT σ m₂) (σ → l) := strictBindStateTRight σ

/-- Strictness of the two-sided state transformer algebra. -/
instance instStrictBindStateTBoth (σ₁ σ₂ : Type u) :
    StrictBind (StateT σ₁ m₁) (StateT σ₂ m₂) (σ₁ → σ₂ → l) := strictBindStateTBoth σ₁ σ₂

end Strict

end MAlgRelOrdered
