/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Interop.Cryptol.Model.Scheme

/-! # Parameter scopes and checked context changes -/

public section

namespace Interop.Cryptol.Polymorphic

/-- The free parameter scopes and available numeric assumptions of an expression. -/
structure Scope where
  /-- Number of numeric parameters. -/
  numbers : Nat
  /-- Number of value-type parameters. -/
  types : Nat
  /-- Checked numeric assumptions. -/
  constraints : List (Constraint numbers)

namespace Scope

/-- Schemes well scoped in this parameter context. -/
abbrev ValueSort (w : Scope) := Scheme w.numbers w.types

/-- Assignments satisfying the ambient assumptions. -/
@[expose] def Valid (w : Scope) (ρ : ParameterAssignment w.numbers w.types) : Prop :=
  ∀ c ∈ w.constraints, c.Holds ρ.numbers

/-- A checked assignment used to interpret an open expression. -/
abbrev Assignment (w : Scope) := {ρ : ParameterAssignment w.numbers w.types // w.Valid ρ}

/-- A numeric assumption follows from every valid ambient assignment. -/
@[expose] def Entails (w : Scope) (c : Constraint w.numbers) : Prop :=
  ∀ ρ : w.Assignment, c.Holds ρ.val.numbers

/-- The empty parameter context. -/
@[expose, reducible] def empty : Scope := ⟨0, 0, []⟩

/-- Enter a numeric binder, shifting existing assumptions. -/
@[expose, reducible] def bindNum (w : Scope) : Scope :=
  ⟨w.numbers + 1, w.types,
    w.constraints.map (Constraint.subst
      (ParameterSubstitution.weakenNum w.numbers w.types).numbers)⟩

/-- Enter a value-type binder; numeric assumptions are unchanged. -/
@[expose, reducible] def bindType (w : Scope) : Scope :=
  ⟨w.numbers, w.types + 1, w.constraints⟩

/-- Make a proof assumption available to the body of its abstraction. -/
@[expose, reducible] def assume (w : Scope) (c : Constraint w.numbers) : Scope :=
  ⟨w.numbers, w.types, c :: w.constraints⟩

/-- Extend a checked assignment with an arbitrary numeric argument. -/
@[expose] def Assignment.extendNum {w : Scope} (ρ : w.Assignment) (l : Length) :
    w.bindNum.Assignment := ⟨ρ.val.extendNum l, by
  intro c hc
  obtain ⟨d, hd, he⟩ := List.mem_map.mp hc
  subst c
  rw [Constraint.holds_subst]
  exact ρ.property d hd⟩

/-- Extend a checked assignment with an arbitrary closed value type. -/
@[expose] def Assignment.extendType {w : Scope} (ρ : w.Assignment) (a : ClosedTy) :
    w.bindType.Assignment := ⟨ρ.val.extendType a, ρ.property⟩

/-- Enter an erased proof binder. -/
@[expose] def Assignment.assume {w : Scope} (ρ : w.Assignment) {c : Constraint w.numbers}
    (h : c.Holds ρ.val.numbers) : (w.assume c).Assignment := ⟨ρ.val, by
  intro d hd
  rcases List.mem_cons.mp hd with he | hd
  · exact he.symm ▸ h
  · exact ρ.property d hd⟩

/-- The nearest proof assumption is available without a solver. -/
theorem entails_here (w : Scope) (c : Constraint w.numbers) : (w.assume c).Entails c :=
  fun ρ => ρ.property c (List.mem_cons_self ..)

/-- A checked symbolic substitution between parameter contexts. -/
structure Map (w z : Scope) where
  /-- Numeric and type substitutions. -/
  parameters : ParameterSubstitution w.numbers w.types z.numbers z.types
  /-- Substitution preserves the hypotheses of the source context. -/
  valid : ∀ ρ : z.Assignment, w.Valid (ρ.val.pull parameters)

/-- Pull a valid target assignment back along a checked context map. -/
@[expose] def Map.pull {w z : Scope} (μ : Map w z) (ρ : z.Assignment) : w.Assignment :=
  ⟨ρ.val.pull μ.parameters, μ.valid ρ⟩

/-- Reindex the schemes of local value variables. -/
@[expose] def Map.sort {w z : Scope} (μ : Map w z) (s : w.ValueSort) : z.ValueSort :=
  s.subst μ.parameters

/-- Identity checked context change. -/
@[expose] def Map.id (w : Scope) : Map w w := ⟨ParameterSubstitution.id _ _, by
  intro ρ
  rw [ParameterAssignment.pull_id]
  exact ρ.property⟩

/-- Composition carries the original constraint evidence through both substitutions. -/
@[expose] def Map.comp {w z u : Scope} (μ : Map w z) (ν : Map z u) : Map w u :=
  ⟨μ.parameters.comp ν.parameters, by
    intro ρ
    rw [ParameterAssignment.pull_comp]
    exact μ.valid (ν.pull ρ)⟩

end Scope
end Interop.Cryptol.Polymorphic
