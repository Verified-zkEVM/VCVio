/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Interop.Cryptol.Model.PolyScope

/-! # Checked substitutions under numeric, type and proof binders -/

public section

namespace Interop.Cryptol.Polymorphic.Scope

theorem valid_bindNum (w : Scope) (ρ : ParameterAssignment (w.numbers + 1) w.types) :
    w.bindNum.Valid ρ ↔ w.Valid (ρ.pull (ParameterSubstitution.weakenNum _ _)) := by
  constructor
  · intro h c hc
    exact (Constraint.holds_subst c _ _).mp (h _ (List.mem_map_of_mem hc))
  · intro h c hc
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hc
    exact (Constraint.holds_subst d _ _).mpr (h d hd)

theorem valid_bindType (w : Scope) (ρ : ParameterAssignment w.numbers (w.types + 1)) :
    w.bindType.Valid ρ ↔ w.Valid (ρ.pull (ParameterSubstitution.weakenType _ _)) := Iff.rfl

namespace Map

variable {w z u : Scope}

/-- Numeric weakening preserves all existing assumptions. -/
@[expose] def weakenNum (w : Scope) : Map w w.bindNum :=
  ⟨ParameterSubstitution.weakenNum _ _, fun ρ => (valid_bindNum w ρ.val).mp ρ.property⟩

/-- Type weakening preserves all existing assumptions. -/
@[expose] def weakenType (w : Scope) : Map w w.bindType :=
  ⟨ParameterSubstitution.weakenType _ _, fun ρ => ρ.property⟩

/-- Adding an assumption does not change parameter meanings. -/
@[expose] def weakenProof (w : Scope) (c : Constraint w.numbers) : Map w (w.assume c) :=
  ⟨ParameterSubstitution.id _ _, by
    intro ρ
    rw [ParameterAssignment.pull_id]
    exact fun d hd => ρ.property d (List.mem_cons_of_mem _ hd)⟩

/-- Lift a checked map below a numeric abstraction. -/
@[expose] def liftNum (μ : Map w z) : Map w.bindNum z.bindNum :=
  ⟨μ.parameters.liftNum, by
    intro ρ
    rw [valid_bindNum, ← ParameterAssignment.pull_comp,
      ParameterSubstitution.weakenNum_comp_liftNum, ParameterAssignment.pull_comp]
    exact μ.valid ((weakenNum z).pull ρ)⟩

/-- Lift a checked map below a value-type abstraction. -/
@[expose] def liftType (μ : Map w z) : Map w.bindType z.bindType :=
  ⟨μ.parameters.liftType, by
    intro ρ
    rw [valid_bindType, ← ParameterAssignment.pull_comp,
      ParameterSubstitution.weakenType_comp_liftType, ParameterAssignment.pull_comp]
    exact μ.valid ((weakenType z).pull ρ)⟩

/-- Entailed constraints remain entailed after checked parameter substitution. -/
theorem entails (μ : Map w z) {c : Constraint w.numbers} (hc : w.Entails c) :
    z.Entails (c.subst μ.parameters.numbers) :=
  fun ρ => (Constraint.holds_subst c _ _).mpr (hc (μ.pull ρ))

/-- Lift a checked map below an erased proof abstraction. -/
@[expose] def assume (μ : Map w z) (c : Constraint w.numbers) :
    Map (w.assume c) (z.assume (c.subst μ.parameters.numbers)) :=
  ⟨μ.parameters, by
    intro ρ d hd
    rcases List.mem_cons.mp hd with he | hd
    · subst d
      exact (Constraint.holds_subst c _ _).mp (ρ.property _ (List.mem_cons_self ..))
    · exact μ.valid ⟨ρ.val, fun e he => ρ.property e (List.mem_cons_of_mem _ he)⟩ d hd⟩

/-- Checked maps are determined by their symbolic substitutions. -/
@[ext] theorem ext {μ ν : Map w z} (h : μ.parameters = ν.parameters) : μ = ν := by
  cases μ
  cases ν
  cases h
  rfl

@[simp] theorem id_comp (μ : Map w z) : (id w).comp μ = μ := by
  apply ext
  exact ParameterSubstitution.id_comp μ.parameters

@[simp] theorem comp_id (μ : Map w z) : μ.comp (id z) = μ := by
  apply ext
  exact ParameterSubstitution.comp_id μ.parameters

theorem comp_assoc {v : Scope} (μ : Map w z) (ν : Map z u) (ξ : Map u v) :
    (μ.comp ν).comp ξ = μ.comp (ν.comp ξ) := by
  apply ext
  exact ParameterSubstitution.comp_assoc ..

/-- Numeric lifting preserves the identity checked map. -/
@[simp] theorem liftNum_id (w : Scope) : (id w).liftNum = id w.bindNum := by
  apply ext
  exact ParameterSubstitution.liftNum_id ..

/-- Type lifting preserves the identity checked map. -/
@[simp] theorem liftType_id (w : Scope) : (id w).liftType = id w.bindType := by
  apply ext
  exact ParameterSubstitution.liftType_id ..

/-- Numeric lifting preserves checked composition and its constraint evidence. -/
theorem liftNum_comp (μ : Map w z) (ν : Map z u) :
    (μ.comp ν).liftNum = μ.liftNum.comp ν.liftNum := by
  apply ext
  exact ParameterSubstitution.liftNum_comp ..

/-- Type lifting preserves checked composition and its constraint evidence. -/
theorem liftType_comp (μ : Map w z) (ν : Map z u) :
    (μ.comp ν).liftType = μ.liftType.comp ν.liftType := by
  apply ext
  exact ParameterSubstitution.liftType_comp ..

/-- Checked maps with equal endpoints and symbolic substitutions are heterogeneously equal. -/
theorem heq_of_parameters_heq {w z u : Scope} (μ : Map w z) (ν : Map w u)
    (hz : z = u) (hp : HEq μ.parameters ν.parameters) : HEq μ ν := by
  cases hz
  exact heq_of_eq (ext (eq_of_heq hp))

/-- Lifting composition below a proof binder preserves the checked parameter map. -/
theorem assume_comp_heq {w z u : Scope} (μ : Map w z) (ν : Map z u)
    (c : Constraint w.numbers) :
    HEq ((μ.assume c).comp (ν.assume (c.subst μ.parameters.numbers)))
      ((μ.comp ν).assume c) := by
  apply heq_of_parameters_heq
  · exact congrArg (Scope.assume u) (Constraint.subst_subst c _ _)
  · rfl

end Map
end Interop.Cryptol.Polymorphic.Scope
