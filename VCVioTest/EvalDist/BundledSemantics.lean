/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module
public import VCVio.EvalDist.Defs.Measure.Deterministic
public import VCVio.EvalDist.MeasureSemantics

/-!
# Bundled measure and kernel inference canaries

Local semantics bundles expose their mass certificates to Mathlib's typeclasses and simplifier.
Successful-output observations retain the distinction between subprobability and losslessness;
effect-preserving observations of a total base monad remain probability measures.
The import surface contains no PMF/SPMF backend.
-/

public section

open MeasureTheory ProbabilityTheory

run_cmd do
  let env ← Lean.getEnv
  for name in [`PMF, `SPMF] do
    if env.contains name then
      throwError "bundled native semantics unexpectedly import {name}"

namespace VCVioTest.BundledSemantics

universe u v w

section observations

variable {m : Type u → Type v} [Monad m] {α β : Type u} {ρ : Type w}
  [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace ρ]
  (sem : MeasureSemanticsVia m) (mx : m α)

example : IsSubprobabilityMeasure (sem.evalDist mx) := inferInstance

example : IsFiniteMeasure (sem.evalDist mx) := inferInstance

example (s : Set α) : sem.evalDist mx s ≤ 1 := measure_le_one _ _

example (s : Set α) : sem.evalDist mx s ≠ ⊤ := measure_ne_top _ _

example (f : α → β) : IsSubprobabilityMeasure ((sem.evalDist mx).map f) := inferInstance

example (f : α → m β) (hf : AEMeasurable (fun x ↦ sem.evalDist (f x)) (sem.evalDist mx)) :
    IsSubprobabilityMeasure ((sem.evalDist mx).bind fun x ↦ sem.evalDist (f x)) :=
  MeasureTheory.isSubprobabilityMeasure_bind hf

example : sem.evalDist mx Set.univ ≤ 1 := by simp

example (f : ρ → m α) (hf : Measurable fun r ↦ sem.evalDist (f r)) :
    IsSubprobabilityKernel (sem.evalDistKernel f hf) := inferInstance

example (f : ρ → m α) (hf : Measurable fun r ↦ sem.evalDist (f r)) :
    IsFiniteKernel (sem.evalDistKernel f hf) := inferInstance

example (f : ρ → m α) (hf : Measurable fun r ↦ sem.evalDist (f r))
    [∀ r, IsProbabilityMeasure (sem.evalDist (f r))] :
    IsMarkovKernel (sem.evalDistKernel f hf) := inferInstance

end observations

section global

variable {m : Type u → Type v} [Monad m] [EvalDistSemantics m]
  {α ε : Type u} [MeasurableSpace α] [MeasurableSpace ε]

example (mx : m α) :
    IsSubprobabilityMeasure ((MeasureSemanticsVia.ofEvalDistSemantics m).evalDist mx) :=
  inferInstance

example (mx : m α) [IsProbabilityMeasure 𝒟[mx]] :
    IsProbabilityMeasure ((MeasureSemanticsVia.ofEvalDistSemantics m).evalDist mx) :=
  inferInstance

example (mx : m α) [IsProbabilityMeasure 𝒟[mx]] :
    (MeasureSemanticsVia.ofEvalDistSemantics m).evalDist mx Set.univ = 1 := by simp

example (mx : OptionT m α) :
    IsSubprobabilityMeasure ((MeasureSemanticsVia.optionT m).evalDist mx) := inferInstance

example (mx : OptionT m α) [IsProbabilityMeasure 𝒟[mx]] :
    IsProbabilityMeasure ((MeasureSemanticsVia.optionT m).evalDist mx) := inferInstance

example (mx : ExceptT ε m α) :
    IsSubprobabilityMeasure ((MeasureSemanticsVia.exceptT ε m).evalDist mx) := inferInstance

example (mx : ExceptT ε m α) [IsProbabilityMeasure 𝒟[mx]] :
    IsProbabilityMeasure ((MeasureSemanticsVia.exceptT ε m).evalDist mx) := inferInstance

variable [LawfulPureEvalDistSemantics m]

example (x : α) :
    IsProbabilityMeasure ((MeasureSemanticsVia.optionT m).evalDist (pure x)) := inferInstance

example (x : α) :
    IsProbabilityMeasure ((MeasureSemanticsVia.exceptT ε m).evalDist (pure x)) := inferInstance

example : (MeasureSemanticsVia.optionT m).evalDist (failure : OptionT m α) = 0 := by
  simp

end global

section total

variable {m : Type u → Type v} {α ε ω ρ σ : Type u}
  [MeasurableSpace α] [MeasurableSpace ε] [MeasurableSpace ω]
  [MeasurableSpace ρ] [MeasurableSpace σ] (sem : ProbabilitySemantics m)

example (mx : m α) : IsProbabilityMeasure (sem.denote mx) := inferInstance

example (mx : OptionT m α) : IsProbabilityMeasure (sem.optionT mx) := inferInstance

example (mx : ExceptT ε m α) : IsProbabilityMeasure (sem.exceptT mx) := inferInstance

example (mx : WriterT ω m α) : IsProbabilityMeasure (sem.writerT mx) := inferInstance

example (mx : OptionT m α) : IsSubprobabilityMeasure (sem.optionT mx) := inferInstance

example (mx : OptionT m α) : sem.optionT mx Set.univ = 1 := by simp

example (mx : ExceptT ε m α) : sem.exceptT mx Set.univ = 1 := by simp

example (mx : WriterT ω m α) : sem.writerT mx Set.univ = 1 := by simp

example (mx : ReaderT ρ m α)
    (hf : Measurable fun r ↦ sem.denote (mx r)) :
    IsMarkovKernel (sem.readerTKernel mx hf) := inferInstance

example (mx : StateT σ m α)
    (hf : Measurable fun s ↦ sem.denote (mx s)) :
    IsMarkovKernel (sem.stateTKernel mx hf) := inferInstance

end total

end VCVioTest.BundledSemantics
