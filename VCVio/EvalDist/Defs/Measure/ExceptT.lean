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
needed.
-/

public section

open MeasureTheory

universe u v

/-- Interpret successful `ExceptT` results by pulling the run measure back along `Except.ok`. -/
noncomputable instance (priority := 5) instEvalDistSemanticsExceptT
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

/-- The successful-output measure of an exceptional computation on a measurable event is the
run measure of the corresponding `Except.ok` outcomes. -/
theorem ExceptT.evalDist_apply
    {ε : Type u} [MeasurableSpace ε] {m : Type u → Type v} [EvalDistSemantics m]
    {α : Type u} [MeasurableSpace α] (mx : ExceptT ε m α)
    {event : Set α} (_hevent : MeasurableSet event) :
    𝒟[mx] event = 𝒟[mx.run] (Except.ok '' event) :=
  Except.measurableEmbedding_ok.comap_apply _ _

/-- The total successful mass of an exceptional computation is the mass of its `ok` branch. -/
@[simp]
theorem ExceptT.evalDist_apply_univ
    {ε : Type u} [MeasurableSpace ε] {m : Type u → Type v} [EvalDistSemantics m]
    {α : Type u} [MeasurableSpace α] (mx : ExceptT ε m α) :
    𝒟[mx] Set.univ = 𝒟[mx.run] (Set.range Except.ok) := by
  rw [ExceptT.evalDist_apply mx MeasurableSet.univ, Set.image_univ]

/-- Pure exceptional computations have Dirac successful-output semantics. -/
@[simp]
theorem ExceptT.evalDist_pure
    {ε : Type u} [MeasurableSpace ε] {m : Type u → Type v}
    [Monad m] [EvalDistSemantics m] [LawfulPureEvalDistSemantics m]
    {α : Type u} [MeasurableSpace α] (x : α) :
    𝒟[(pure x : ExceptT ε m α)] = Measure.dirac x := by
  rw [ExceptT.evalDist_eq_comap_ok, ExceptT.run_pure, _root_.evalDist_pure,
    Measure.comap_ok_dirac_ok]

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

/-- Native exceptional bind composes successful-output measures when the full run measures of
the continuations form a measurable family. This stronger premise is necessary: measurability
after discarding errors does not determine measurability of the hidden error branch. -/
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
