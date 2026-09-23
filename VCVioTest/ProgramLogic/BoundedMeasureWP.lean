/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module
public import VCVio.ProgramLogic.Unary.WP.Probabilistic.Measure
public import VCVio.EvalDist.Defs.Measure.Deterministic
public import VCVio.OracleComp.EvalDist.MeasureSpec
public import Mathlib.Tactic.GRewrite

/-!
# Bounded native WP regressions

Probability assertions apply to unsuccessful runs and weighted oracle responses. Ordinary
imports supply the interpretation, public value laws, and congruence automation.
-/

public section

open MeasureTheory Std.Internal.Do
open scoped ENNReal MeasureProgramLogic.Probabilistic

run_cmd do
  let env ← Lean.getEnv
  for name in [`PMF, `SPMF] do
    if env.contains name then
      throwError "bounded native WP unexpectedly imports {name}"

namespace VCVioTest.ProgramLogic.BoundedMeasureWP

noncomputable example : WPMonad Option Prob EPost.Nil := inferInstance

example (p : Prob) : wp (pure 7 : Option Nat) (fun _ ↦ p) Lean.Order.bot = p := by simp

example (p : Prob) : (wp (none : Option Nat) (fun _ ↦ p) Lean.Order.bot).val = 0 := by simp

example (p : Prob) : (wp (some 7 : Option Nat) (fun _ ↦ p) Lean.Order.bot).val = p.val := by
  simp

universe v

variable {m : Type → Type v} [Monad m] [LawfulMonad m]
  [EvalDistSemantics m] [LawfulEvalDistSemantics m] {α : Type}

example (mx : m α) (f g : α → Prob) (hfg : ∀ a, f a ≤ g a) :
    wp mx f (Lean.Order.bot : EPost.Nil) ≤ wp mx g (Lean.Order.bot : EPost.Nil) := by
  gcongr with a
  exact hfg a

example (mx : m α) (f g : α → Prob) (hfg : ∀ a, f a ≤ g a) :
    wp mx f (Lean.Order.bot : EPost.Nil) ≤ wp mx g (Lean.Order.bot : EPost.Nil) := by
  grw [hfg]

abbrev WeightedSpec : OracleSpec (Fin 1) := Fin 1 →ₒ Bool

noncomputable instance weightedMeasureSpec : OracleSpec.IsMeasureSpec WeightedSpec where
  toMeasure _ := Measure.dirac false
  isProbabilityMeasure _ := inferInstance

example : (wp (WeightedSpec.query 0 : OracleComp WeightedSpec Bool)
    (fun answer ↦ Prob.indicator (answer = true)) Lean.Order.bot).val = 0 := by
  rw [MeasureProgramLogic.Probabilistic.wp_val_eq_lintegral _ _ Measurable.of_discrete]
  simp only [OracleComp.evalDist_liftM_query]
  simp [OracleSpec.IsMeasureSpec.toMeasure, PFunctor.IsMeasureSpec.toMeasure]

end VCVioTest.ProgramLogic.BoundedMeasureWP
