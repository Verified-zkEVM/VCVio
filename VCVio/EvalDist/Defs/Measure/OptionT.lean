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
measurable embedding `some`. This effect-native construction supplies the primary semantics;
finite-distribution lifts remain available for explicit compatibility observations.

Native map and monad laws use the base monad's measure laws. The full bind law only requires
measurability of the successful-output family: an auxiliary discrete source space discharges
full-run measurability, and the map law transports its source measure to the selected space.
-/

public section

open MeasureTheory

universe u v

/-- Interpret successful `OptionT` results by pulling the run measure back along `some`. -/
noncomputable instance (priority := 20) instEvalDistSemanticsOptionT
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

/-- The successful-output measure of an optional computation on an event is the run
measure of the corresponding `some` outcomes. -/
theorem OptionT.evalDist_apply
    {m : Type u → Type v} [EvalDistSemantics m]
    {α : Type u} [MeasurableSpace α] (mx : OptionT m α) {event : Set α} :
    𝒟[mx] event = 𝒟[mx.run] (some '' event) :=
  Option.measurableEmbedding_some.comap_apply _ _

/-- The successful mass of an optional computation is the mass of present values in its run. -/
@[simp]
theorem OptionT.evalDist_apply_univ
    {m : Type u → Type v} [EvalDistSemantics m]
    {α : Type u} [MeasurableSpace α] (mx : OptionT m α) :
    𝒟[mx] Set.univ = 𝒟[mx.run] {value | value.isSome} :=
  by
    rw [OptionT.evalDist_apply]
    congr 1
    ext value
    cases value <;> simp

/-- Pure optional computations have Dirac successful-output semantics. -/
theorem OptionT.evalDist_pure
    {m : Type u → Type v} [Monad m] [EvalDistSemantics m] [LawfulPureEvalDistSemantics m]
    {α : Type u} [MeasurableSpace α] (x : α) :
    𝒟[(pure x : OptionT m α)] = Measure.dirac x := by
  rw [OptionT.evalDist_eq_comap_some, OptionT.run_pure, _root_.evalDist_pure,
    ← Measure.dropNone_eq_comap_some, Measure.dropNone_dirac_some]

/-- Native optional semantics preserves pure whenever the base semantics does. -/
instance (priority := 20) instLawfulPureEvalDistSemanticsOptionT
    {m : Type u → Type v} [Monad m] [EvalDistSemantics m]
    [LawfulPureEvalDistSemantics m] : LawfulPureEvalDistSemantics (OptionT m) where
  denote_pure := OptionT.evalDist_pure

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

/-- Lifting a lossless computation into the optional monad preserves its probability measure. -/
instance OptionT.isProbabilityMeasure_evalDist_lift
    {m : Type u → Type v} [Monad m] [LawfulMonad m]
    [EvalDistSemantics m] [LawfulEvalDistSemantics m]
    {α : Type u} [MeasurableSpace α] (mx : m α) [IsProbabilityMeasure 𝒟[mx]] :
    IsProbabilityMeasure 𝒟[OptionT.lift mx] := by
  rw [OptionT.evalDist_lift]
  infer_instance

/-- A monadic lift into the optional monad preserves a known probability measure. -/
instance OptionT.isProbabilityMeasure_evalDist_liftM
    {m : Type u → Type v} [Monad m] [LawfulMonad m]
    [EvalDistSemantics m] [LawfulEvalDistSemantics m]
    {α : Type u} [MeasurableSpace α] (mx : m α) [IsProbabilityMeasure 𝒟[mx]] :
    IsProbabilityMeasure 𝒟[(liftM mx : OptionT m α)] :=
  OptionT.isProbabilityMeasure_evalDist_lift mx

/-- A measurable map of successful optional results is the measure pushforward. -/
theorem OptionT.evalDist_map
    {m : Type u → Type v} [Monad m] [LawfulMonad m]
    [EvalDistSemantics m] [LawfulEvalDistSemantics m]
    {α β : Type u} [MeasurableSpace α] [MeasurableSpace β]
    (mx : OptionT m α) (f : α → β) (hf : Measurable f) :
    𝒟[f <$> mx] = 𝒟[mx].map f := by
  simp only [OptionT.evalDist_eq_comap_some, ← Measure.dropNone_eq_comap_some]
  rw [OptionT.run_map, _root_.evalDist_map mx.run (by fun_prop), Measure.dropNone_map _ f hf]

/-- A measurable family of full run measures suffices to compose native optional denotations. -/
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

/-- Native optional semantics satisfies the measurable-bind law for successful-output families.
The base monad's map law relates the auxiliary discrete draw to the selected source space. -/
instance (priority := 20) instLawfulEvalDistSemanticsOptionT
    {m : Type u → Type v} [Monad m] [LawfulMonad m]
    [EvalDistSemantics m] [LawfulEvalDistSemantics m] :
    LawfulEvalDistSemantics (OptionT m) where
  denote_bind {α β} mα mβ mx f hf := by
    have hId : @Measurable α α ⊤ mα id := fun _ _ ↦ trivial
    have hmap := @OptionT.evalDist_map m _ _ _ _ α α ⊤ mα mx id hId
    rw [id_map] at hmap
    rw [hmap, @Measure.bind_map α α β ⊤ mα mβ _ _ _ hId hf]
    exact @OptionT.evalDist_bind m _ _ _ α β ⊤ mβ mx f (fun _ _ ↦ trivial)

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
  rw [_root_.evalDist_map mx (f := fun x => if p x then some () else none) Measurable.of_discrete,
    _root_.evalDist_map mx (f := p) Measurable.of_discrete,
    Measure.map_apply Measurable.of_discrete Option.measurableSet_isSome,
    Measure.map_apply Measurable.of_discrete (measurableSet_singleton True)]
  congr 1
  ext x
  simp
