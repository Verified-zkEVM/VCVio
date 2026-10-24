/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Interop.Cryptol.Bridge.Imperative

/-! # Whole-module loop consumers use public equations on partial inputs -/

public section

namespace Cryptol.Tests.Imperative

open Bridge.Imperative

/-- An unused divergent body does not prevent a loop from returning its initial value. -/
theorem unused_divergent_body (initial : Computation .integer) :
    whileLoop (.value (.const (.value ⟨false⟩))) ⊥ initial = initial :=
  whileLoop_false _ _

/-- Do-while demands the first body application, unlike while with a false condition. -/
example (initial : Computation .integer) :
    doWhileLoop (.value (.const (.value ⟨false⟩))) ⊥ initial = ⊥ :=
  doWhileLoop_false _ _

/-- A constant body can return a value without demanding an undefined initial state. -/
example : doWhileLoop (a := .integer) (.value (.const (.value ⟨false⟩)))
    (.value (.const (.value ⟨(7 : Int)⟩))) ⊥ = .value ⟨(7 : Int)⟩ :=
  doWhileLoop_false _ _

/-- A single iteration changes the state; returning the initial state is not equivalent. -/
example : whileLoop (a := .bit) (.value OmegaCompletePartialOrder.ContinuousHom.id)
    (.value (.const (.value ⟨false⟩))) (.value ⟨true⟩) = .value ⟨false⟩ := by
  rw [whileLoop_eq_step_of_true _ _ _ rfl]
  exact whileLoop_eq_of_false _ _ _ rfl

/-- Callback errors survive the public interface. -/
example (initial : Computation .bit) :
    whileLoop (.error (.user "condition")) ⊥ initial = .error (.user "condition") :=
  whileLoop_error _ _ _

end Cryptol.Tests.Imperative
