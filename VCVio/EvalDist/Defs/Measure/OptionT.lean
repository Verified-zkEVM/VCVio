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

An `OptionT` computation denotes the successful-output measure of its underlying
`Option`-valued computation. The low priority preserves the compatibility semantics
when a finite-distribution lift is already part of an existing downstream instance graph;
bundled semantics can select this effect-native construction directly.
-/

public section

open MeasureTheory

universe u v

/-- Interpret successful `OptionT` results by discarding the `none` outcome. -/
noncomputable instance (priority := 5) instEvalDistSemanticsOptionT
    {m : Type u → Type v} [EvalDistSemantics m] :
    EvalDistSemantics (OptionT m) where
  denote mx := (𝒟[mx.run]).dropNone
  apply_univ_le_one mx :=
    (Measure.dropNone_apply_univ_le _).trans (evalDist_apply_univ_le_one mx.run)

/-- The successful mass of an optional computation is the mass of present values in its run. -/
@[simp]
theorem OptionT.evalDist_apply_univ
    {m : Type u → Type v} [EvalDistSemantics m]
    {α : Type u} [MeasurableSpace α] (mx : OptionT m α) :
    𝒟[mx] Set.univ = 𝒟[mx.run] {value | value.isSome} :=
  Measure.dropNone_apply_univ _

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
