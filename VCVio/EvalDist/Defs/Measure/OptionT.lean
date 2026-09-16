/-
Copyright (c) 2026 VCVio Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module
public import VCVio.EvalDist.Defs.Measure.Core
public import ToMathlib.MeasureTheory.Measure.Option

/-!
# Successful-output measure semantics for optional computations

An `OptionT` computation denotes the pullback of its underlying `Option`-valued measure along the
measurable embedding `some`. The low priority preserves the compatibility semantics when a
finite-distribution lift is already part of an existing downstream instance graph; bundled
semantics can select this effect-native construction directly.
-/

public section

open MeasureTheory

universe u v

/-- Interpret successful `OptionT` results by pulling the run measure back along `some`. -/
noncomputable instance (priority := 5) instEvalDistSemanticsOptionT
    {m : Type u → Type v} [EvalDistSemantics m] :
    EvalDistSemantics (OptionT m) where
  denote mx := (𝒟[mx.run]).comap some
  apply_univ_le_one mx :=
    calc
      (𝒟[mx.run]).comap some Set.univ = 𝒟[mx.run] (some '' Set.univ) :=
        Option.measurableEmbedding_some.comap_apply _ _
      _ ≤ 𝒟[mx.run] Set.univ := measure_mono (Set.subset_univ _)
      _ ≤ 1 := evalDist_apply_univ_le_one mx.run

/-- Unfold the native successful-output semantics to Mathlib's pullback along `some`. -/
theorem OptionT.evalDist_eq_comap_some
    {m : Type u → Type v} [EvalDistSemantics m]
    {α : Type u} [MeasurableSpace α] (mx : OptionT m α) :
    𝒟[mx] = (𝒟[mx.run]).comap some := by
  rfl

/-- The successful-output measure of an optional computation on a measurable event is the run
measure of the corresponding `some` outcomes. -/
theorem OptionT.evalDist_apply
    {m : Type u → Type v} [EvalDistSemantics m]
    {α : Type u} [MeasurableSpace α] (mx : OptionT m α)
    {event : Set α} (_hevent : MeasurableSet event) :
    𝒟[mx] event = 𝒟[mx.run] (some '' event) :=
  Option.measurableEmbedding_some.comap_apply _ _

/-- The successful mass of an optional computation is the mass of present values in its run. -/
@[simp]
theorem OptionT.evalDist_apply_univ
    {m : Type u → Type v} [EvalDistSemantics m]
    {α : Type u} [MeasurableSpace α] (mx : OptionT m α) :
    𝒟[mx] Set.univ = 𝒟[mx.run] {value | value.isSome} :=
  by
    rw [OptionT.evalDist_apply mx MeasurableSet.univ]
    congr 1
    ext value
    cases value <;> simp

/-- Pure optional computations have Dirac successful-output semantics. -/
@[simp]
theorem OptionT.evalDist_pure
    {m : Type u → Type v} [Monad m] [EvalDistSemantics m] [LawfulPureEvalDistSemantics m]
    {α : Type u} [MeasurableSpace α] (x : α) :
    𝒟[(pure x : OptionT m α)] = Measure.dirac x := by
  rw [OptionT.evalDist_eq_comap_some, OptionT.run_pure, _root_.evalDist_pure,
    ← Measure.dropNone_eq_comap_some, Measure.dropNone_dirac_some]

/-- Optional failure has no successful-output mass. -/
@[simp]
theorem OptionT.evalDist_failure
    {m : Type u → Type v} [Monad m] [EvalDistSemantics m] [LawfulPureEvalDistSemantics m]
    {α : Type u} [MeasurableSpace α] : 𝒟[(failure : OptionT m α)] = 0 := by
  rw [OptionT.evalDist_eq_comap_some,
    show (failure : OptionT m α).run = pure none from rfl, _root_.evalDist_pure,
    ← Measure.dropNone_eq_comap_some, Measure.dropNone_dirac_none]

/-- Lifting a computation into `OptionT` preserves its successful-output measure. -/
@[simp]
theorem OptionT.evalDist_lift
    {m : Type u → Type v} [Monad m] [LawfulMonad m]
    [EvalDistSemantics m] [LawfulEvalDistSemantics m]
    {α : Type u} [MeasurableSpace α] (mx : m α) :
    𝒟[OptionT.lift mx] = 𝒟[mx] := by
  rw [OptionT.evalDist_eq_comap_some, OptionT.run_lift,
    LawfulMonad.bind_pure_comp, _root_.evalDist_map mx Option.measurable_some,
    Option.measurableEmbedding_some.comap_map]

/-- Native optional bind composes successful-output measures when the full run measures of the
continuations form a measurable family. This stronger premise is necessary: measurability after
discarding `none` does not determine measurability of the hidden failure branch. -/
theorem OptionT.evalDist_bind
    {m : Type u → Type v} [Monad m]
    [EvalDistSemantics m] [LawfulEvalDistSemantics m]
    {α β : Type u} [MeasurableSpace α] [MeasurableSpace β]
    (mx : OptionT m α) (f : α → OptionT m β)
    (hf : Measurable fun x => 𝒟[(f x).run]) :
    𝒟[mx >>= f] = Measure.bind 𝒟[mx] fun x => 𝒟[f x] := by
  simp_rw [OptionT.evalDist_eq_comap_some]
  simp_rw [← Measure.dropNone_eq_comap_some]
  have hCont : (fun value : Option α =>
      𝒟[value.elim (pure none) fun x => (f x).run]) =
      (fun value => value.elim (Measure.dirac none) fun x => 𝒟[(f x).run]) := by
    funext value
    cases value <;> simp only [Option.elim_none, Option.elim_some, _root_.evalDist_pure]
  have hBindCont : Measurable fun value : Option α =>
      𝒟[value.elim (pure none) fun x => (f x).run] := by
    rw [hCont]
    exact Option.measurable_elim' _ hf
  rw [OptionT.run_bind, Option.elimM,
    _root_.evalDist_bind mx.run
      (fun value => value.elim (pure none) fun x => (f x).run) hBindCont]
  rw [hCont]
  exact Measure.dropNone_bind 𝒟[mx.run] (fun x => 𝒟[(f x).run]) hf

/-- Discrete intermediate values discharge the run-measurability premise of
`OptionT.evalDist_bind`. -/
theorem OptionT.evalDist_bind_of_discrete
    {m : Type u → Type v} [Monad m]
    [EvalDistSemantics m] [LawfulEvalDistSemantics m]
    {α β : Type u} [MeasurableSpace α] [DiscreteMeasurableSpace α] [MeasurableSpace β]
    (mx : OptionT m α) (f : α → OptionT m β) :
    𝒟[mx >>= f] = Measure.bind 𝒟[mx] fun x => 𝒟[f x] :=
  OptionT.evalDist_bind mx f Measurable.of_discrete

/-- The effect-native successful-output measure of sampling and then guarding is the measure of
the corresponding Boolean event. This statement is independent of which global `OptionT`
semantics wins instance synthesis. -/
@[simp]
theorem OptionT.dropNone_evalDist_run_bind_guard_apply_univ
    {m : Type → Type v} [Monad m] [LawfulMonad m]
    [EvalDistSemantics m] [LawfulEvalDistSemantics m]
    {α : Type} (mx : m α) (p : α → Prop) [DecidablePred p] :
    (𝒟[do let x ← mx; (guard (p x) : OptionT m Unit).run]).dropNone Set.univ =
      𝒟[do let x ← mx; pure (p x)] {True} := by
  let : MeasurableSpace α := ⊤
  have hrun : (do let x ← mx; (guard (p x) : OptionT m Unit).run) =
      (do let x ← mx; pure (if p x then some () else none)) := by
    apply bind_congr
    intro x
    by_cases hx : p x <;> simp [hx]
  rw [Measure.dropNone_apply_univ, hrun, LawfulMonad.bind_pure_comp,
    LawfulMonad.bind_pure_comp]
  rw [evalDist_map mx (f := fun x => if p x then some () else none) Measurable.of_discrete,
    evalDist_map mx (f := p) Measurable.of_discrete,
    Measure.map_apply Measurable.of_discrete Option.measurableSet_isSome,
    Measure.map_apply Measurable.of_discrete (measurableSet_singleton True)]
  congr 1
  ext x
  simp
