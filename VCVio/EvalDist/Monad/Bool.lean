/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import VCVio.EvalDist.Defs.Measure.Core
public import VCVio.EvalDist.ProbabilityNotation
public import ToMathlib.MeasureTheory.Measure.Bool

/-!
# Boolean guessing experiments under measure semantics

A fair hidden bit and two lossless Boolean branches have a guessing bias equal to the branches'
distinguishing distance. The monad is arbitrary; fairness and losslessness are semantic hypotheses.
Two lossless Boolean computations, each at most as likely as the other to return either bit, have
the same law.
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

/-- Two lossless Boolean computations, each at most as likely as the other to return `true` and to
return `false`, have the same law: under a probability measure each bit's mass is one minus the
other's, so the two inequalities are equalities. -/
theorem evalDist_eq_of_prEvent_le {m : Type → Type v} [Monad m] [LawfulMonad m]
    [EvalDistSemantics m] [LawfulEvalDistSemantics m] {mx my : m Bool}
    [IsProbabilityMeasure 𝒟[mx]] [IsProbabilityMeasure 𝒟[my]]
    (ht : Pr{let x ← mx}[x = true] ≤ Pr{let x ← my}[x = true])
    (hf : Pr{let x ← mx}[x = false] ≤ Pr{let x ← my}[x = false]) : 𝒟[mx] = 𝒟[my] := by
  rw [prEvent_eq_evalDist_singleton, prEvent_eq_evalDist_singleton] at ht hf
  have hx := Measure.apply_true_add_apply_false_eq_one 𝒟[mx]
  have hy := Measure.apply_true_add_apply_false_eq_one 𝒟[my]
  have htrue : 𝒟[mx] {true} = 𝒟[my] {true} := by
    refine le_antisymm ht ?_
    rw [ENNReal.eq_sub_of_add_eq (measure_ne_top _ _) hx,
      ENNReal.eq_sub_of_add_eq (measure_ne_top _ _) hy]
    exact tsub_le_tsub_left hf 1
  have hfalse : 𝒟[mx] {false} = 𝒟[my] {false} := by
    rw [add_comm] at hx hy
    rw [ENNReal.eq_sub_of_add_eq (measure_ne_top _ _) hx,
      ENNReal.eq_sub_of_add_eq (measure_ne_top _ _) hy, htrue]
  exact Measure.ext_of_singleton fun x => by cases x <;> assumption
