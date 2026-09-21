/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module
public import VCVio.EvalDist.Monad.Option
public import VCVio.EvalDist.Defs.Measure.ExceptT
public import VCVio.EvalDist.ProbabilityBounds

/-!
# Native measure laws for optional and exceptional computations

Pure laws inherit only the base pure certificate. Bind laws require measurability of successful
output measures rather than full run measures. Events of independent transformer computations
normalize with `simp` and `grind`, without a finite-distribution backend or measurable spaces on
intermediate outputs.
-/

public section

open MeasureTheory

run_cmd do
  let env ← Lean.getEnv
  for name in [`PMF, `SPMF] do
    if env.contains name then
      throwError "native transformer laws unexpectedly import {name}"

namespace VCVioTest.Transformers

universe u v

section pure

variable {m : Type u → Type v} [Monad m] [EvalDistSemantics m]
  [LawfulPureEvalDistSemantics m] {ε α : Type u} [MeasurableSpace ε] [MeasurableSpace α]

example (x : α) : 𝒟[(pure x : OptionT m α)] = Measure.dirac x := by simp

example (x : α) : IsProbabilityMeasure 𝒟[(pure x : OptionT m α)] := inferInstance

example : 𝒟[(failure : OptionT m α)] = 0 := by simp

example (x : α) : 𝒟[(pure x : ExceptT ε m α)] = Measure.dirac x := by simp

example (x : α) : IsProbabilityMeasure 𝒟[(pure x : ExceptT ε m α)] := inferInstance

example (error : ε) : 𝒟[(throw error : ExceptT ε m α)] = 0 := by simp

end pure

section bind

variable {m : Type u → Type v} [Monad m] [LawfulMonad m]
  [EvalDistSemantics m] [LawfulEvalDistSemantics m]
  {ε α β : Type u} [MeasurableSpace ε] [MeasurableSpace α] [MeasurableSpace β]

example (mx : OptionT m α) (f : α → OptionT m β) (hf : Measurable fun x ↦ 𝒟[f x]) :
    𝒟[mx >>= f] = Measure.bind 𝒟[mx] fun x ↦ 𝒟[f x] :=
  evalDist_bind mx f hf

example (mx : ExceptT ε m α) (f : α → ExceptT ε m β)
    (hf : Measurable fun x ↦ 𝒟[f x]) :
    𝒟[mx >>= f] = Measure.bind 𝒟[mx] fun x ↦ 𝒟[f x] :=
  evalDist_bind mx f hf

example (mx : OptionT m α) (f : α → β) (hf : Measurable f) :
    𝒟[f <$> mx] = 𝒟[mx].map f := evalDist_map mx hf

example (mx : ExceptT ε m α) (f : α → β) (hf : Measurable f) :
    𝒟[f <$> mx] = 𝒟[mx].map f := evalDist_map mx hf

example (mx : m α) [IsProbabilityMeasure 𝒟[mx]] :
    IsProbabilityMeasure 𝒟[OptionT.lift mx] := inferInstance

example (mx : m α) [IsProbabilityMeasure 𝒟[mx]] :
    IsProbabilityMeasure 𝒟[(liftM mx : OptionT m α)] := inferInstance

example (mx : m α) [IsProbabilityMeasure 𝒟[mx]] :
    IsProbabilityMeasure 𝒟[(liftM mx : ExceptT ε m α)] := inferInstance

example (mx : OptionT m α) (event : Set α) :
    𝒟[mx] event = 𝒟[mx.run] (some '' event) := OptionT.evalDist_apply mx

example (mx : ExceptT ε m α) (event : Set α) :
    𝒟[mx] event = 𝒟[mx.run] (Except.ok '' event) := ExceptT.evalDist_apply mx

end bind

section events

variable {m : Type → Type v} [Monad m] [LawfulMonad m]
  [EvalDistSemantics m] [LawfulEvalDistSemantics m] {ε α β : Type} [MeasurableSpace ε]

example (mx : m α) (p : α → Prop) :
    Pr{let x ← OptionT.lift mx}[p x] = Pr{let x ← mx}[p x] := by simp

example (mx : m α) (p : α → Prop) {bound : ENNReal}
    (h : Pr{let x ← mx}[p x] ≤ bound) :
    Pr{let x ← OptionT.lift mx}[p x] ≤ bound := by grind

example (mx : OptionT m α) (my : OptionT m β) (p : α → Prop) (q : β → Prop) :
    Pr{let x ← mx; let y ← my}[p x ∧ q y] =
      Pr{let x ← mx}[p x] * Pr{let y ← my}[q y] := by simp

example (mx : m α) (p q : α → Prop) [DecidablePred p] :
    Pr{let x ← OptionT.lift mx; guard (p x)}[q x] =
      Pr{let x ← mx}[p x ∧ q x] := by simp

example (mx : m α) (p : α → Prop) [DecidablePred p] :
    Pr{let x ← OptionT.lift mx; guard (p x)}[True] = Pr{let x ← mx}[p x] := by simp

example (mx : m α) (p q : α → Prop) [DecidablePred p] :
    𝒟[do let x ← OptionT.lift mx; (fun _ : Unit ↦ q x) <$> guard (p x)] {True} =
      Pr{let x ← mx}[p x ∧ q x] := by simp

example (mx : m α) (p q : α → Prop) [DecidablePred p] {bound : ENNReal}
    (h : Pr{let x ← mx}[p x ∧ q x] ≤ bound) :
    𝒟[do let x ← OptionT.lift mx; (fun _ : Unit ↦ q x) <$> guard (p x)] {True} ≤
      bound := by grind

example (mx : m α) (p : α → Prop) [DecidablePred p] :
    𝒟[do let x ← OptionT.lift mx; guard (p x)] =
      Pr{let x ← mx}[p x] • Measure.dirac () := by simp

example (mx : m α) (p : α → Prop) [DecidablePred p] :
    𝒟[do let x ← (liftM mx : OptionT m α); guard (p x)] =
      Pr{let x ← mx}[p x] • Measure.dirac () := by simp

example (mx : m α) (p q : α → Prop) [DecidablePred p] {bound : ENNReal}
    (h : Pr{let x ← mx}[p x ∧ q x] ≤ bound) :
    Pr{let x ← OptionT.lift mx; guard (p x)}[q x] ≤ bound := by grind

example (mx : OptionT m α) (my : OptionT m β) (p : α → Prop) (q : β → Prop)
    {bound : ENNReal}
    (h : Pr{let x ← mx}[p x] * Pr{let y ← my}[q y] ≤ bound) :
    Pr{let x ← mx; let y ← my}[p x ∧ q y] ≤ bound := by grind

example (mx : ExceptT ε m α) (my : ExceptT ε m β) (p : α → Prop) (q : β → Prop) :
    Pr{let x ← mx; let y ← my}[p x ∧ q y] =
      Pr{let x ← mx}[p x] * Pr{let y ← my}[q y] := by simp

example (mx : ExceptT ε m α) (my : ExceptT ε m β) (p : α → Prop) (q : β → Prop)
    {bound : ENNReal}
    (h : Pr{let x ← mx}[p x] * Pr{let y ← my}[q y] ≤ bound) :
    Pr{let x ← mx; let y ← my}[p x ∧ q y] ≤ bound := by grind

example (mx : OptionT m α) (p q : α → Prop) (hpq : ∀ x, p x → q x) {bound : ENNReal}
    (h : Pr{let x ← mx}[q x] ≤ bound) : Pr{let x ← mx}[p x] ≤ bound := by
  grw [prEvent_mono mx p q hpq, h]

example (mx : ExceptT ε m α) (p q : α → Prop) (hpq : ∀ x, p x → q x) :
    Pr{let x ← mx}[p x] ^ 2 ≤ Pr{let x ← mx}[q x] ^ 2 := by
  gcongr ?_ ^ 2
  exact prEvent_mono mx p q hpq

end events

end VCVioTest.Transformers
