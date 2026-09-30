/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module
public import VCVio.EvalDist.Defs.Measure.Failure
public import VCVio.EvalDist.ProbabilityNotation
public import ToMathlib.Control.Except
public import ToMathlib.Control.Option
public import ToMathlib.Control.Monad.Algebra

/-!
# Successful-output measures for deterministic computations

`Id` returns its unique value with Dirac measure. `Option` and `Except` assign Dirac measure to
successful values and zero measure to failures. Error values need no measurable structure when
only successful outputs are observed. These interpretations satisfy the measurable Giry laws.
-/

public section

open MeasureTheory

universe u v

/-- A deterministic total computation denotes its Dirac output measure. -/
noncomputable instance (priority := 20) instEvalDistSemanticsId : EvalDistSemantics Id where
  denote mx := Measure.dirac mx.run
  apply_univ_le_one _ := by simp

/-- The unique returned value determines a deterministic computation's measure. -/
@[simp, grind norm]
theorem Id.evalDist_eq_dirac {α : Type u} [MeasurableSpace α] (mx : Id α) :
    𝒟[mx] = Measure.dirac mx.run := rfl

/-- Every deterministic total computation denotes a probability measure. -/
instance Id.isProbabilityMeasure_evalDist {α : Type u} [MeasurableSpace α] (mx : Id α) :
    IsProbabilityMeasure 𝒟[mx] := by
  rw [Id.evalDist_eq_dirac]
  infer_instance

/-- Deterministic total computations respect the measurable Giry laws. -/
instance (priority := 20) instLawfulEvalDistSemanticsId : LawfulEvalDistSemantics Id where
  denote_pure _ := rfl
  denote_bind mx _ hf := (Measure.dirac_bind hf mx.run).symm

/-- A deterministic optional result denotes zero on failure and a Dirac measure on success. -/
noncomputable instance (priority := 20) instEvalDistSemanticsOption :
    EvalDistSemantics Option where
  denote mx := mx.elim 0 Measure.dirac
  apply_univ_le_one mx := by cases mx <;> simp

/-- An absent optional result has no successful-output mass. -/
@[simp, grind =]
theorem Option.evalDist_none {α : Type u} [MeasurableSpace α] :
    𝒟[(none : Option α)] = 0 := rfl

/-- Deterministic optional failure has zero successful-output measure. -/
instance (priority := 20) instLawfulFailureEvalDistSemanticsOption :
    LawfulFailureEvalDistSemantics Option where
  denote_failure := Option.evalDist_none

/-- A present optional result has its Dirac output measure. -/
@[simp, grind =]
theorem Option.evalDist_some {α : Type u} [MeasurableSpace α] (x : α) :
    𝒟[(some x : Option α)] = Measure.dirac x := rfl

/-- A present optional result denotes a probability measure. -/
instance Option.isProbabilityMeasure_evalDist_some {α : Type u} [MeasurableSpace α] (x : α) :
    IsProbabilityMeasure 𝒟[(some x : Option α)] := by
  rw [Option.evalDist_some]
  infer_instance

/-- Deterministic optional computations respect the measurable Giry laws. -/
instance (priority := 20) instLawfulEvalDistSemanticsOption :
    LawfulEvalDistSemantics Option where
  denote_pure _ := rfl
  denote_bind mx f hf := by
    cases mx with
    | none => exact (Measure.bind_zero_left fun x ↦ 𝒟[f x]).symm
    | some x => exact (Measure.dirac_bind hf x).symm

/-- A deterministic exceptional result assigns mass only to its successful output. -/
noncomputable instance (priority := 20) instEvalDistSemanticsExcept {ε : Type u} :
    EvalDistSemantics (Except ε) where
  denote mx := match mx with
    | .error _ => 0
    | .ok x => Measure.dirac x
  apply_univ_le_one mx := by cases mx <;> simp

/-- An exceptional result has no successful-output mass. -/
@[simp, grind =]
theorem Except.evalDist_error {ε : Type u} {α : Type v} [MeasurableSpace α] (error : ε) :
    𝒟[(Except.error error : Except ε α)] = 0 := rfl

/-- A successful exceptional result has its Dirac output measure. -/
@[simp, grind =]
theorem Except.evalDist_ok {ε : Type u} {α : Type v} [MeasurableSpace α] (x : α) :
    𝒟[(Except.ok x : Except ε α)] = Measure.dirac x := rfl

/-- A successful exceptional result denotes a probability measure. -/
instance Except.isProbabilityMeasure_evalDist_ok {ε : Type u} {α : Type v}
    [MeasurableSpace α] (x : α) :
    IsProbabilityMeasure 𝒟[(Except.ok x : Except ε α)] := by
  rw [Except.evalDist_ok]
  infer_instance

/-- Deterministic exceptional computations respect the measurable Giry laws. -/
instance (priority := 20) instLawfulEvalDistSemanticsExcept {ε : Type u} :
    LawfulEvalDistSemantics (Except ε) where
  denote_pure _ := rfl
  denote_bind mx f hf := by
    cases mx with
    | error _ => exact (Measure.bind_zero_left fun x ↦ 𝒟[f x]).symm
    | ok x => exact (Measure.dirac_bind hf x).symm

/-! ## Expectations and events of deterministic computations

The expectation laws are stated for every observation, so `simp` applies them to events too; the
event forms follow. -/

/-- An absent optional result has expectation zero. -/
@[simp, grind =]
theorem Option.wp_none {α : Type} (g : α → ENNReal) : wp⟦(none : Option α)⟧ g = 0 := by
  let : MeasurableSpace α := ⊤
  rw [MeasureProgramLogic.wp_eq_lintegral _ g Measurable.of_discrete, Option.evalDist_none,
    lintegral_zero_measure]

/-- An absent optional result makes every event impossible. -/
theorem Option.prEvent_none {α : Type} (p : α → Prop) : Pr{let x ← (none : Option α)}[p x] = 0 :=
  Option.wp_none _

/-- The expectation of a present optional result is the observation at that result. `simp`
applies PolyFun's `ExactWPMonad.wp_some`. -/
@[grind =]
theorem Option.wp_some {α : Type} (x : α) (g : α → ENNReal) : wp⟦some x⟧ g = g x :=
  MeasureProgramLogic.wp_pure (m := Option) x g

/-- An event of a present optional result is the indicator of the event at that result. -/
theorem Option.prEvent_some {α : Type} (x : α) (p : α → Prop) :
    Pr{let y ← some x}[p y] = propInd (p x) :=
  Option.wp_some x _

/-- An exceptional result has expectation zero. -/
@[simp, grind =]
theorem Except.wp_error {ε : Type u} {α : Type} (error : ε) (g : α → ENNReal) :
    wp⟦(Except.error error : Except ε α)⟧ g = 0 := by
  let : MeasurableSpace α := ⊤
  rw [MeasureProgramLogic.wp_eq_lintegral _ g Measurable.of_discrete, Except.evalDist_error,
    lintegral_zero_measure]

/-- An exceptional result makes every event impossible. -/
theorem Except.prEvent_error {ε : Type u} {α : Type} (error : ε) (p : α → Prop) :
    Pr{let x ← (Except.error error : Except ε α)}[p x] = 0 :=
  Except.wp_error error _

/-- The expectation of a successful exceptional result is the observation at that result. -/
@[simp, grind =]
theorem Except.wp_ok {ε : Type u} {α : Type} (x : α) (g : α → ENNReal) :
    wp⟦(Except.ok x : Except ε α)⟧ g = g x :=
  MeasureProgramLogic.wp_pure (m := Except ε) x g

/-- An event of a successful exceptional result is the indicator of the event at that result. -/
theorem Except.prEvent_ok {ε : Type u} {α : Type} (x : α) (p : α → Prop) :
    Pr{let y ← (Except.ok x : Except ε α)}[p y] = propInd (p x) :=
  Except.wp_ok x _
