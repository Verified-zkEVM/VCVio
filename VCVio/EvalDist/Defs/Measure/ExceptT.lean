/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import VCVio.EvalDist.Defs.Measure.Core
public import ToMathlib.MeasureTheory.Measure.Except

/-!
# Successful-output measure semantics for exceptional computations

An `ExceptT ε m` computation denotes the pullback of its underlying `Except ε α`-valued
measure along the measurable embedding `Except.ok`. Errors are therefore missing successful
mass, while the effect-preserving denotation remains available by observing `mx.run` directly.

The construction uses Mathlib's `Measure.comap`; no transformer-specific measure operation is
needed. Native pure, map, and bind laws inherit the base monad's measure laws. Successful-output
measurability suffices for the full bind law, without requiring the error family to be measurable.
-/

public section

open MeasureTheory

universe u v

/-- Interpret successful `ExceptT` results by pulling the run measure back along `Except.ok`. -/
noncomputable instance (priority := 20) instEvalDistSemanticsExceptT
    {ε : Type u} [MeasurableSpace ε] {m : Type u → Type v} [EvalDistSemantics m] :
    EvalDistSemantics (ExceptT ε m) where
  denote mx := (𝒟[mx.run]).comap Except.ok
  apply_univ_le_one mx :=
    calc
      (𝒟[mx.run]).comap Except.ok Set.univ
          = 𝒟[mx.run] (Except.ok '' Set.univ) :=
            Except.measurableEmbedding_ok.comap_apply _ _
      _ ≤ 𝒟[mx.run] Set.univ := measure_mono (Set.subset_univ _)
      _ ≤ 1 := evalDist_apply_univ_le_one mx.run

/-- Unfold the native successful-output semantics to Mathlib's pullback along `Except.ok`. -/
theorem ExceptT.evalDist_eq_comap_ok
    {ε : Type u} [MeasurableSpace ε] {m : Type u → Type v} [EvalDistSemantics m]
    {α : Type u} [MeasurableSpace α] (mx : ExceptT ε m α) :
    𝒟[mx] = (𝒟[mx.run]).comap Except.ok := by
  rfl

/-- The successful-output measure of an exceptional computation on an event is the
run measure of the corresponding `Except.ok` outcomes. -/
theorem ExceptT.evalDist_apply
    {ε : Type u} [MeasurableSpace ε] {m : Type u → Type v} [EvalDistSemantics m]
    {α : Type u} [MeasurableSpace α] (mx : ExceptT ε m α) {event : Set α} :
    𝒟[mx] event = 𝒟[mx.run] (Except.ok '' event) :=
  Except.measurableEmbedding_ok.comap_apply _ _

/-- The total successful mass of an exceptional computation is the mass of its `ok` branch. -/
@[simp]
theorem ExceptT.evalDist_apply_univ
    {ε : Type u} [MeasurableSpace ε] {m : Type u → Type v} [EvalDistSemantics m]
    {α : Type u} [MeasurableSpace α] (mx : ExceptT ε m α) :
    𝒟[mx] Set.univ = 𝒟[mx.run] (Set.range Except.ok) := by
  rw [ExceptT.evalDist_apply, Set.image_univ]

/-- Pure exceptional computations have Dirac successful-output semantics. -/
theorem ExceptT.evalDist_pure
    {ε : Type u} [MeasurableSpace ε] {m : Type u → Type v}
    [Monad m] [EvalDistSemantics m] [LawfulPureEvalDistSemantics m]
    {α : Type u} [MeasurableSpace α] (x : α) :
    𝒟[(pure x : ExceptT ε m α)] = Measure.dirac x := by
  rw [ExceptT.evalDist_eq_comap_ok, ExceptT.run_pure, _root_.evalDist_pure,
    Measure.comap_ok_dirac_ok]

/-- Native exceptional semantics preserves pure whenever the base semantics does. -/
instance (priority := 20) instLawfulPureEvalDistSemanticsExceptT
    {ε : Type u} [MeasurableSpace ε] {m : Type u → Type v}
    [Monad m] [EvalDistSemantics m] [LawfulPureEvalDistSemantics m] :
    LawfulPureEvalDistSemantics (ExceptT ε m) where
  denote_pure := ExceptT.evalDist_pure

/-- Throwing an exception carries no successful-output mass. -/
@[simp]
theorem ExceptT.evalDist_throw
    {ε : Type u} [MeasurableSpace ε] {m : Type u → Type v}
    [Monad m] [EvalDistSemantics m] [LawfulPureEvalDistSemantics m]
    {α : Type u} [MeasurableSpace α] (error : ε) :
    𝒟[(throw error : ExceptT ε m α)] = 0 := by
  rw [ExceptT.evalDist_eq_comap_ok, ExceptT.run_throw, _root_.evalDist_pure,
    Measure.comap_ok_dirac_error]

/-- Lifting a computation into `ExceptT` preserves its successful-output measure. -/
@[simp]
theorem ExceptT.evalDist_liftM
    {ε : Type u} [MeasurableSpace ε] {m : Type u → Type v}
    [Monad m] [LawfulMonad m] [EvalDistSemantics m] [LawfulEvalDistSemantics m]
    {α : Type u} [MeasurableSpace α] (mx : m α) :
    𝒟[(liftM mx : ExceptT ε m α)] = 𝒟[mx] := by
  rw [ExceptT.evalDist_eq_comap_ok, ExceptT.run_liftM,
    _root_.evalDist_map mx Except.measurable_ok,
    Except.measurableEmbedding_ok.comap_map]

/-- Lifting a lossless computation into the exceptional monad preserves its probability measure. -/
instance ExceptT.isProbabilityMeasure_evalDist_liftM
    {ε : Type u} [MeasurableSpace ε] {m : Type u → Type v}
    [Monad m] [LawfulMonad m] [EvalDistSemantics m] [LawfulEvalDistSemantics m]
    {α : Type u} [MeasurableSpace α] (mx : m α) [IsProbabilityMeasure 𝒟[mx]] :
    IsProbabilityMeasure 𝒟[(liftM mx : ExceptT ε m α)] := by
  rw [ExceptT.evalDist_liftM]
  infer_instance

/-- A measurable map of successful exceptional results is the measure pushforward. -/
theorem ExceptT.evalDist_map
    {ε : Type u} [MeasurableSpace ε] {m : Type u → Type v}
    [Monad m] [LawfulMonad m] [EvalDistSemantics m] [LawfulEvalDistSemantics m]
    {α β : Type u} [MeasurableSpace α] [MeasurableSpace β]
    (mx : ExceptT ε m α) (f : α → β) (hf : Measurable f) :
    𝒟[f <$> mx] = 𝒟[mx].map f := by
  rw [ExceptT.evalDist_eq_comap_ok, ExceptT.run_map,
    _root_.evalDist_map mx.run (Except.measurable_map hf), Measure.comap_ok_map _ f hf,
    ExceptT.evalDist_eq_comap_ok]

/-- A measurable family of full run measures suffices to compose native exceptional denotations. -/
theorem ExceptT.evalDist_bind
    {ε : Type u} [MeasurableSpace ε] {m : Type u → Type v}
    [Monad m] [EvalDistSemantics m] [LawfulEvalDistSemantics m]
    {α β : Type u} [MeasurableSpace α] [MeasurableSpace β]
    (mx : ExceptT ε m α) (f : α → ExceptT ε m β)
    (hf : Measurable fun x => 𝒟[(f x).run]) :
    𝒟[mx >>= f] = Measure.bind 𝒟[mx] fun x => 𝒟[f x] := by
  simp_rw [ExceptT.evalDist_eq_comap_ok]
  have hCont : (fun value : Except ε α =>
      𝒟[match value with
        | .ok x => (f x).run
        | .error error => pure (Except.error error)]) =
      (fun value => match value with
        | .error error => Measure.dirac (Except.error error)
        | .ok x => 𝒟[(f x).run]) := by
    funext value
    cases value <;> simp only [_root_.evalDist_pure]
  have hBindCont : Measurable fun value : Except ε α =>
      𝒟[match value with
        | .ok x => (f x).run
        | .error error => pure (Except.error error)] := by
    rw [hCont]
    exact Except.measurable_elim
      (Measure.measurable_dirac.comp Except.measurable_error) hf
  have hRun : 𝒟[(mx >>= f).run] = Measure.bind 𝒟[mx.run] fun value =>
      𝒟[match value with
        | .ok x => (f x).run
        | .error error => pure (Except.error error)] := by
    rw [ExceptT.run_bind]
    exact _root_.evalDist_bind mx.run
      (fun value => match value with
        | .ok x => (f x).run
        | .error error => pure (Except.error error)) hBindCont
  rw [hRun]
  rw [hCont]
  exact Measure.comap_ok_bind 𝒟[mx.run] (fun x => 𝒟[(f x).run]) hf

/-- Discrete intermediate values discharge the run-measurability premise of
`ExceptT.evalDist_bind`. -/
theorem ExceptT.evalDist_bind_of_discrete
    {ε : Type u} [MeasurableSpace ε] {m : Type u → Type v}
    [Monad m] [EvalDistSemantics m] [LawfulEvalDistSemantics m]
    {α β : Type u} [MeasurableSpace α] [DiscreteMeasurableSpace α] [MeasurableSpace β]
    (mx : ExceptT ε m α) (f : α → ExceptT ε m β) :
    𝒟[mx >>= f] = Measure.bind 𝒟[mx] fun x => 𝒟[f x] :=
  ExceptT.evalDist_bind mx f Measurable.of_discrete

/-- Native exceptional semantics satisfies the measurable-bind law for successful-output families.
The base monad's map law relates the auxiliary discrete draw to the selected source space. -/
instance (priority := 20) instLawfulEvalDistSemanticsExceptT
    {ε : Type u} [MeasurableSpace ε] {m : Type u → Type v}
    [Monad m] [LawfulMonad m] [EvalDistSemantics m] [LawfulEvalDistSemantics m] :
    LawfulEvalDistSemantics (ExceptT ε m) where
  denote_bind {α β} mα mβ mx f hf := by
    have hId : @Measurable α α ⊤ mα id := fun _ _ ↦ trivial
    have hmap := @ExceptT.evalDist_map ε _ m _ _ _ _ α α ⊤ mα mx id hId
    rw [id_map] at hmap
    rw [hmap, @Measure.bind_map α α β ⊤ mα mβ _ _ _ hId hf]
    exact @ExceptT.evalDist_bind ε _ m _ _ _ α β ⊤ mβ mx f (fun _ _ ↦ trivial)
