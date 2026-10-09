/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import VCVio.ProgramLogic.Unary.SimulateQ

/-!
# Native quantitative oracle semantics

A deliberately nonuniform oracle checks that quantitative WP uses the configured measure.
Its real-valued observations use the usual real measurable space, and a stateful interpreter
preserves expectations without assigning a measurable space to its hidden function state.
-/

public section

open MeasureTheory OracleComp OracleSpec
open OracleComp.ProgramLogic
open scoped ENNReal OracleComp.Quantitative

run_cmd do
  let env ← Lean.getEnv
  for name in [`PMF, `SPMF, `NeverFail, `EvalDistCompatible, `DiscreteEvalDistCompatible] do
    if env.contains name then
      throwError "native oracle WP unexpectedly imports {name}"

namespace VCVioTest.NativeOracleWP

/-- An oracle whose answer is always true. -/
abbrev fixedSpec : OracleSpec Unit := fun _ ↦ Bool

instance : (t : fixedSpec.Domain) → MeasurableSpace (fixedSpec.Range t) :=
  fun _ ↦ inferInstanceAs (MeasurableSpace Bool)

instance : (t : fixedSpec.Domain) → DiscreteMeasurableSpace (fixedSpec.Range t) :=
  fun _ ↦ inferInstanceAs (DiscreteMeasurableSpace Bool)

noncomputable instance : OracleSpec.IsMeasureSpec fixedSpec where
  toMeasure _ := Measure.dirac true
  isProbabilityMeasure _ := inferInstance

@[simp]
theorem fixed_toMeasure (t : Unit) : OracleSpec.IsMeasureSpec.toMeasure (spec := fixedSpec) t =
    Measure.dirac true := rfl

example (post : Bool → ENNReal) :
    wp (fixedSpec.query () : OracleComp fixedSpec Bool) post = post true := by
  rw [wp_query]
  simp

example (post : ℝ → ENNReal) :
    wp ((fun b ↦ if b then (-3 : ℝ) else 1) <$>
      (fixedSpec.query () : OracleComp fixedSpec Bool)) post =
      post (-3) := by
  rw [wp_map, wp_query]
  simp

example (mx : OracleComp fixedSpec ℝ) (post : ℝ → ENNReal) (hpost : Measurable post) :
    wp mx post = ∫⁻ x, post x ∂𝒟[mx] := wp_eq_lintegral mx post hpost

/-- Finite answer partitions leave arbitrary hidden output types unmeasured. -/
example (mx : OracleComp fixedSpec (ℕ → ℕ)) (post : (ℕ → ℕ) → ENNReal) :
    wp mx post = ∑' x, Pr{let y ← mx}[y = x] * post x :=
  wp_eq_tsum mx post

/-- A handler that increments an unobserved function state at each query. -/
@[expose]
def countingImpl : QueryImpl fixedSpec (StateT (ℕ → ℕ) (OracleComp fixedSpec)) :=
  fun t ↦ do
    modify (fun counts n ↦ counts n + 1)
    query t

example {α : Type} (mx : OracleComp fixedSpec α) (counts : ℕ → ℕ) (post : α → ENNReal) :
    wp ((simulateQ countingImpl mx).run' counts) post = wp mx post := by
  apply wp_simulateQ_run'_eq
  intro t s
  simp [countingImpl, StateT.run'_eq, StateT.run_bind, StateT.run_modify,
    evalDist_liftM_query]

end VCVioTest.NativeOracleWP
