/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import VCVio.EvalDist.Defs.Measure.Core
public import ToMathlib.MeasureTheory.Measure.Bool

/-!
# Boolean guessing experiments under native measure semantics

A fair hidden bit and two lossless Boolean branches have a guessing bias equal to the branches'
distinguishing distance. The monad is arbitrary; fairness and losslessness are semantic hypotheses.
-/

public section

open MeasureTheory

universe v

/-- Fair hidden-bit guessing has the Boolean distance of its two lossless branches. -/
theorem evalDist_boolBias_bind_coin {m : Type → Type v} [Monad m]
    [EvalDistSemantics m] [LawfulEvalDistSemantics m]
    (coin real rand : m Bool) [IsProbabilityMeasure 𝒟[real]] [IsProbabilityMeasure 𝒟[rand]]
    (htrue : 𝒟[coin] {true} = 1 / 2) (hfalse : 𝒟[coin] {false} = 1 / 2) :
    (𝒟[do
      let b ← coin
      let z ← if b then real else rand
      pure (b == z)]).boolBias = (𝒟[real]).boolDist 𝒟[rand] := by
  have hgame :
      𝒟[do
        let b ← coin
        let z ← if b then real else rand
        pure (b == z)] =
        𝒟[coin].bind fun b ↦
          (if b then 𝒟[real] else 𝒟[rand]).bind fun z ↦ Measure.dirac (b == z) := by
    rw [evalDist_bind_of_discrete]
    apply Measure.bind_congr_right
    filter_upwards [] with b
    cases b <;> simp only [Bool.false_eq_true, ↓reduceIte, evalDist_bind_of_discrete,
      evalDist_pure]
  rw [hgame]
  exact Measure.boolBias_bind_coin 𝒟[coin] 𝒟[real] 𝒟[rand]
    htrue hfalse (by simp) (by simp)
