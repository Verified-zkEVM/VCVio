/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module
public import VCVio.EvalDist.Defs.Measure.Deterministic
public import VCVio.EvalDist.Monad.Option
public import VCVio.EvalDist.Defs.Measure.ExceptT

/-!
# Deterministic measure semantics canaries

Total, optional, and exceptional deterministic computations have native measures on arbitrary
output spaces. Successful constructors infer probability instances; failure has zero mass.
Exceptional events need no measurable structure on their error type. The native import surface
contains no finite-distribution backend.
-/

public section

open MeasureTheory

run_cmd do
  let env ← Lean.getEnv
  for name in [`PMF, `SPMF] do
    if env.contains name then
      throwError "deterministic measure semantics unexpectedly import {name}"

namespace VCVioTest.Deterministic

universe u v

section measures

variable {ε : Type u} {α β : Type v} [MeasurableSpace α] [MeasurableSpace β]

example (mx : Id α) : 𝒟[mx] = Measure.dirac mx.run := by simp

example (mx : Id α) : IsProbabilityMeasure 𝒟[mx] := inferInstance

example : 𝒟[(none : Option α)] = 0 := by simp

example (x : α) : IsProbabilityMeasure 𝒟[(some x : Option α)] := inferInstance

example (error : ε) : 𝒟[(Except.error error : Except ε α)] = 0 := by simp

example (x : α) : IsProbabilityMeasure 𝒟[(Except.ok x : Except ε α)] := inferInstance

example (mx : Id α) (f : α → Id β) (hf : Measurable fun x ↦ 𝒟[f x]) :
    𝒟[mx >>= f] = (𝒟[mx]).bind fun x ↦ 𝒟[f x] := evalDist_bind mx f hf

example (mx : Option α) (f : α → Option β) (hf : Measurable fun x ↦ 𝒟[f x]) :
    𝒟[mx >>= f] = (𝒟[mx]).bind fun x ↦ 𝒟[f x] := evalDist_bind mx f hf

example (mx : Except ε α) (f : α → Except ε β) (hf : Measurable fun x ↦ 𝒟[f x]) :
    𝒟[mx >>= f] = (𝒟[mx]).bind fun x ↦ 𝒟[f x] := evalDist_bind mx f hf

example (mx : OptionT Id α) : IsSubprobabilityMeasure 𝒟[mx] := inferInstance

example (event : Set α) : (0 : Measure α) event = 0 := by grind

example (mx : Option α) : IsSubprobabilityMeasure 𝒟[mx] := inferInstance

example (mx : Except ε α) : IsSubprobabilityMeasure 𝒟[mx] := inferInstance

end measures

section events

variable {ε α : Type} (x : α) (p : α → Prop) [DecidablePred p]

example {m : Type → Type v} [Monad m] [EvalDistSemantics m]
    [LawfulPureEvalDistSemantics m] (q : Prop) [Decidable q] :
    𝒟[(pure q : m Prop)] {True} = if q then 1 else 0 := by simp

example (q : Prop) [Decidable q] : Measure.dirac q {True} = if q then 1 else 0 := by grind

example : Pr{let value ← (pure x : Id α)}[p value] = if p x then 1 else 0 := by simp

example : Pr{let value ← (pure x : Id α)}[p value] = if p x then 1 else 0 := by grind

example : Pr{let value ← (some x : Option α)}[p value] = if p x then 1 else 0 := by simp

example : Pr{let value ← (some x : Option α)}[p value] = if p x then 1 else 0 := by grind

example : Pr{let value ← (none : Option α)}[p value] = 0 := by simp

example : Pr{let value ← (none : Option α)}[p value] = 0 := by grind

example : Pr{let value ← (Except.ok x : Except ε α)}[p value] =
    if p x then 1 else 0 := by simp

example : Pr{let value ← (Except.ok x : Except ε α)}[p value] =
    if p x then 1 else 0 := by grind

example (error : ε) : Pr{let value ← (Except.error error : Except ε α)}[p value] = 0 := by
  simp

example (error : ε) : Pr{let value ← (Except.error error : Except ε α)}[p value] = 0 := by
  grind

end events

end VCVioTest.Deterministic
