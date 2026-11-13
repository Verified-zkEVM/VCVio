/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module
public import VCVio.OracleComp.SimSemantics.Append.Core

/-!
# Handler sums and ordinary function types

`QueryImpl spec m` is reducibly the function type `(t : spec.Domain) → m (spec.Range t)`, so an
`HAdd` instance stated for handlers would also be a candidate for `+` on ordinary functions.
Handlers for a sum specification combine with `+ₛ` (`QueryImpl.add`) instead: importing them
leaves `+` on functions pointwise, and `impl₁ +ₛ impl₂` answers left queries with `impl₁` and
right queries with `impl₂`.
-/

public section

namespace VCVioTest.ModuleAPI.QueryImplSum

example (f g : ℕ → Multiset ℕ) : (f + g) 0 = f 0 + g 0 := rfl

/-- A handler for the singleton specification `ℕ →ₒ ℕ`, answering `n` with `n + 1`. -/
def succImpl : QueryImpl (ℕ →ₒ ℕ) Option := fun n => some (n + 1)

/-- A handler for the singleton specification `Bool →ₒ Bool`, answering `b` with `!b`. -/
def notImpl : QueryImpl (Bool →ₒ Bool) Option := fun b => some (!b)

example : (succImpl +ₛ notImpl) (.inl 3) = some (4 : ℕ) := rfl

example : (succImpl +ₛ notImpl) (.inr true) = some false := rfl

example : (succImpl +ₛ notImpl +ₛ succImpl) (.inr 0) = some (1 : ℕ) := rfl

variable {ι₁ ι₂ : Type} {spec₁ : OracleSpec ι₁} {spec₂ : OracleSpec ι₂} {m : Type → Type}

example (impl₁ : QueryImpl spec₁ m) (impl₂ : QueryImpl spec₂ m) (t : spec₁.Domain) :
    (impl₁ +ₛ impl₂) (.inl t) = impl₁ t := by
  simp

example (impl₁ : QueryImpl spec₁ m) (impl₂ : QueryImpl spec₂ m) (t : spec₂.Domain) :
    (impl₁ +ₛ impl₂) (.inr t) = impl₂ t := by
  simp

end VCVioTest.ModuleAPI.QueryImplSum
