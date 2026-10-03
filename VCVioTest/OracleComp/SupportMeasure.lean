/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module
public import VCVio.ProgramLogic.Unary.WP.OracleMeasure
public import Mathlib.Tactic.GRewrite

/-!
# Operational and quantitative oracle reasoning

These canaries require only the chosen response measures, including weighted measures with
zero-mass possible answers. No discrete probability backend is imported.
-/

public section

open MeasureTheory Std.WP
open scoped ENNReal ExpectationWP.Lower

run_cmd do
  let env ← Lean.getEnv
  if env.contains `PMF then
    throwError "support/measure bridge unexpectedly imports PMF"

universe u

namespace VCVioTest.OracleComp.SupportMeasure

section Generic

variable {ι : Type u} {spec : OracleSpec.{u, 0} ι}
  [OracleSpec.AnswerMeasure spec]
  {α : Type} [MeasurableSpace α] [DiscreteMeasurableSpace α]

example (mx : OracleComp spec α) (f g : α → ENNReal)
    (hfg : ∀ x ∈ support mx, f x ≤ g x) : wp mx f Lean.Order.bot ≤ wp mx g Lean.Order.bot := by
  gcongr with x hx
  exact hfg x hx

example (mx : OracleComp spec α) (f g : α → ENNReal)
    (hfg : ∀ x ∈ support mx, f x ≤ g x) : wp mx f Lean.Order.bot ≤ wp mx g Lean.Order.bot := by
  grw [wp_mono_of_support mx hfg]

example (mx : OracleComp spec α) (f g : α → ENNReal) (c : ENNReal)
    (hfg : ∀ x ∈ support mx, f x ≤ c + g x) :
    wp mx f Lean.Order.bot ≤ c + wp mx g Lean.Order.bot :=
  ExpectationWP.wp_le_const_add_of_support mx hfg

end Generic

/-! ## Possible answers with zero probability -/

abbrev WeightedSpec : OracleSpec (Fin 1) := Fin 1 →ₒ Bool

noncomputable instance weightedMeasureSpec : OracleSpec.AnswerMeasure WeightedSpec where
  toMeasure _ := Measure.dirac false
  isProbabilityMeasure _ := inferInstance

example : true ∈ support (liftM (WeightedSpec.query 0) : OracleComp WeightedSpec Bool) :=
  OracleComp.mem_support_query (spec := WeightedSpec) 0 true

example : 𝒟[(liftM (WeightedSpec.query 0) : OracleComp WeightedSpec Bool)] {true} = 0 := by
  rw [OracleComp.evalDist_liftM_query_apply (spec := WeightedSpec) 0 (MeasurableSet.singleton _)]
  simp [OracleSpec.AnswerMeasure.toMeasure, PFunctor.AnswerMeasure.toMeasure]

end VCVioTest.OracleComp.SupportMeasure
