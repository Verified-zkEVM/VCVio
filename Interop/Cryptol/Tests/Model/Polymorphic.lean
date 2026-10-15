/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Interop.Cryptol.Model.Polymorphic

/-!
# A recursive call at a different numeric instantiation

The domain includes an unbounded family of numeric instances. Unfolding the
recursive body produces a polymorphic value immediately, although applying
any instance diverges. This distinguishes the family semantics from either
eager specialization or identifying a returned family with outer bottom.
-/

public section

namespace Interop.Cryptol.Tests.Polymorphic

open OmegaCompletePartialOrder

/-- A schema with a numeric parameter and an integer result. -/
@[expose, reducible] def familySchema : Schema := ⟨1, 0, [], .integer⟩

/-- Recursive calls move from a finite parameter to its successor. -/
@[expose] def nextInstance (i : familySchema.Instantiation) : familySchema.Instantiation where
  numbers _ := match i.numbers 0 with
    | .finite n => .finite (n + 1)
    | .infinite => .infinite
  types := i.types
  valid := fun _ h => nomatch h

/-- Return a family whose instance calls the recursively bound family at the next parameter. -/
@[expose] noncomputable def body : familySchema.Suspended →𝒄 familySchema.Suspended :=
  DomainResult.valueContinuous.comp (.ofFun (fun env i =>
    familySchema.apply (nextInstance i) env))

/-- The least solution has an outer value and divergent instances. -/
theorem body_fix : body.fix = .value (⊥ : familySchema.Family) := by
  apply le_antisymm
  · exact body.fix_le le_rfl
  · exact body.approximants_le_fix 1

/-- Every instance diverges, even though the polymorphic expression has returned. -/
theorem apply_body_fix (i : familySchema.Instantiation) :
    familySchema.apply i body.fix = ⊥ := by
  rw [body_fix]
  rfl

/-- Outer forcing can distinguish the family from divergence. -/
theorem body_fix_ne_bot : body.fix ≠ ⊥ := by
  rw [body_fix]
  exact familySchema.value_bottom_ne_bot

end Interop.Cryptol.Tests.Polymorphic
