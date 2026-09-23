/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module
public import VCVio.EvalDist.Monad.Seq.Measure
public import VCVio.EvalDist.IndepProductMeasure
public import VCVio.EvalDist.Defs.Measure.Deterministic
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.Tactic.GCongr
public import Mathlib.Tactic.GRewrite

/-!
# Native applicative and finite-product canaries

Sequencing laws preserve successful mass on arbitrary measurable spaces. Lossless factors
propagate their probability certificates, while potentially failing factors retain their mass
in event bounds. The automation checks exercise `simp`, `grind`, `gcongr`, and `grw` without a
discrete distribution backend or operational support hypotheses.
-/

public section

open MeasureTheory

run_cmd do
  let env ← Lean.getEnv
  for name in [`PMF, `SPMF] do
    if env.contains name then
      throwError "native sequencing unexpectedly imports {name}"

namespace VCVioTest.SeqMeasure

universe u v

section measures

variable {m : Type u → Type v} [Monad m] [LawfulMonad m]
  [EvalDistSemantics m] [LawfulEvalDistSemantics m] {α β γ : Type u}
  [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
  (mx : m α) (my : m β)

example : 𝒟[Prod.mk <$> mx <*> my] = 𝒟[mx].prod 𝒟[my] := by simp

example : 𝒟[Prod.mk <$> mx <*> my] = 𝒟[mx].prod 𝒟[my] := by grind

example : 𝒟[mx <* my] = 𝒟[my] Set.univ • 𝒟[mx] := by simp

example : 𝒟[mx <* my] = 𝒟[my] Set.univ • 𝒟[mx] := by grind

example : 𝒟[mx *> my] = 𝒟[mx] Set.univ • 𝒟[my] := by simp

example : 𝒟[mx *> my] = 𝒟[mx] Set.univ • 𝒟[my] := by grind

example : IsSubprobabilityMeasure (𝒟[mx].prod 𝒟[my]) := inferInstance

example (f : α → β → γ) (hf : Measurable (Function.uncurry f)) :
    𝒟[f <$> mx <*> my] = (𝒟[mx].prod 𝒟[my]).map (Function.uncurry f) :=
  evalDist_seq_map mx my f hf

example [IsProbabilityMeasure 𝒟[my]] : 𝒟[mx <* my] = 𝒟[mx] := by simp

example [IsProbabilityMeasure 𝒟[mx]] : 𝒟[mx *> my] = 𝒟[my] := by simp

example [IsProbabilityMeasure 𝒟[mx]] [IsProbabilityMeasure 𝒟[my]] :
    IsProbabilityMeasure 𝒟[Prod.mk <$> mx <*> my] := inferInstance

example [IsProbabilityMeasure 𝒟[mx]] [IsProbabilityMeasure 𝒟[my]] :
    IsProbabilityMeasure 𝒟[mx <* my] := inferInstance

example [IsProbabilityMeasure 𝒟[mx]] [IsProbabilityMeasure 𝒟[my]] :
    IsProbabilityMeasure 𝒟[mx *> my] := inferInstance

example (n : ℕ) (g : Fin n → m α) :
    𝒟[Fin.mOfFn n g] = Measure.pi fun i ↦ 𝒟[g i] := evalDist_mOfFn n g

example (n : ℕ) (g : Fin n → m α) [∀ i, IsProbabilityMeasure 𝒟[g i]] :
    IsProbabilityMeasure 𝒟[Fin.mOfFn n g] := inferInstance

example (n : ℕ) (g : Fin n → m α) [∀ i, IsProbabilityMeasure 𝒟[g i]] :
    𝒟[Fin.mOfFn n g] Set.univ = 1 := by simp

end measures

section events

variable {m : Type → Type v} [Monad m] [LawfulMonad m]
  [EvalDistSemantics m] [LawfulEvalDistSemantics m] {α β : Type}

example [MeasurableSpace β] (mx : m α) (my : m β) (p : α → Prop) :
    Pr{let x ← mx <* my}[p x] = 𝒟[my] Set.univ * Pr{let x ← mx}[p x] := by simp

example [MeasurableSpace β] (mx : m α) (my : m β) (p : α → Prop) :
    Pr{let x ← mx <* my}[p x] = 𝒟[my] Set.univ * Pr{let x ← mx}[p x] := by grind

example [MeasurableSpace α] (mx : m α) (my : m β) (p : β → Prop) :
    Pr{let y ← mx *> my}[p y] = 𝒟[mx] Set.univ * Pr{let y ← my}[p y] := by simp

example [MeasurableSpace α] (mx : m α) (my : m β) (p : β → Prop) :
    Pr{let y ← mx *> my}[p y] = 𝒟[mx] Set.univ * Pr{let y ← my}[p y] := by grind

example [MeasurableSpace β] (mx : m α) (my : m β) (p : α → Prop) {r : ENNReal}
    (h : Pr{
      let x ← mx}[p x] ≤ r) : Pr{let x ← mx <* my}[p x] ≤ 𝒟[my] Set.univ * r := by
  simp only [prEvent_seqLeft]
  gcongr

example [MeasurableSpace β] (mx : m α) (my : m β) (p : α → Prop) {r : ENNReal}
    (h : Pr{
      let x ← mx}[p x] ≤ r) : Pr{let x ← mx <* my}[p x] ≤ 𝒟[my] Set.univ * r := by
  rw [prEvent_seqLeft]
  grw [h]

end events

section finite

variable {m : Type → Type v} [Monad m] [LawfulMonad m]
  [EvalDistSemantics m] [LawfulEvalDistSemantics m] {α ι : Type}
  [MeasurableSpace α] [Fintype ι]

example (g : ι → m α) : 𝒟[Fintype.mPi g] = Measure.pi fun i ↦ 𝒟[g i] := evalDist_mPi g

example (g : ι → m α) [∀ i, IsProbabilityMeasure 𝒟[g i]] :
    IsProbabilityMeasure 𝒟[Fintype.mPi g] := inferInstance

example (g : ι → m α) [∀ i, IsProbabilityMeasure 𝒟[g i]] :
    𝒟[Fintype.mPi g] Set.univ = 1 := by simp

end finite

example (mx my : Id ℝ) : 𝒟[Prod.mk <$> mx <*> my] = 𝒟[mx].prod 𝒟[my] := by simp

example (g : Fin 3 → Id ℝ) :
    𝒟[Fin.mOfFn 3 g] = Measure.pi fun i ↦ 𝒟[g i] := evalDist_mOfFn 3 g

example (g : Bool → Id ℝ) :
    𝒟[Fintype.mPi g] = Measure.pi fun i ↦ 𝒟[g i] := evalDist_mPi g

example : Pr{let x ← (some 7 : Option ℕ) <* (none : Option ℝ)}[x = 7] = 0 := by simp

end VCVioTest.SeqMeasure
