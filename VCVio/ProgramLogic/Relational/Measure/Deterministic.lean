/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import VCVio.ProgramLogic.Relational.Measure
public import VCVio.EvalDist.Defs.Measure.Deterministic

/-!
# Constructor simplification for deterministic relational semantics

Successful deterministic constructors reduce relational judgments to their returned values.
These equations let `simp` recognize constructors after the monad's `pure` has reduced.
-/

public section

open scoped ENNReal

namespace MeasureProgramLogic

variable {α β : Type} [MeasurableSpace α] [MeasurableSpace β]
  [MeasurableSingletonClass α] [MeasurableSingletonClass β]

/-- Two present optional outputs have exactly their returned post-expectation. -/
@[simp]
theorem eRelWP_some_some (a : α) (b : β) (g : α → β → ℝ≥0∞) :
    eRelWP (some a) (some b) g = g a b :=
  eRelWP_pure_pure a b g

/-- Two present optional outputs satisfy exactly their returned relation. -/
@[simp]
theorem relWP_some_some_iff (a : α) (b : β) (R : α → β → Prop) :
    RelWP (some a) (some b) R ↔ R a b :=
  relWP_pure_pure_iff a b R

/-- Two successful exceptional outputs have exactly their returned post-expectation. -/
@[simp]
theorem eRelWP_ok_ok {ε δ : Type} (a : α) (b : β) (g : α → β → ℝ≥0∞) :
    eRelWP (Except.ok a : Except ε α) (Except.ok b : Except δ β) g = g a b :=
  eRelWP_pure_pure a b g

/-- Two successful exceptional outputs satisfy exactly their returned relation. -/
@[simp]
theorem relWP_ok_ok_iff {ε δ : Type} (a : α) (b : β) (R : α → β → Prop) :
    RelWP (Except.ok a : Except ε α) (Except.ok b : Except δ β) R ↔ R a b :=
  relWP_pure_pure_iff a b R

end MeasureProgramLogic
