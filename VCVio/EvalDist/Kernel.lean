/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import VCVio.EvalDist.Defs.Semantics
public import ToMathlib.Probability.Kernel.Subprobability

/-!
# Kernel-valued evaluation semantics

This module bundles a measurably parameterized family of computations as a Mathlib kernel. Closed
computations denote measures; a family `f : ρ → m α` denotes a kernel precisely when the family
of output measures is measurable in `ρ`.

The resulting kernel is automatically subprobabilistic. If the family is lossless, it is a Markov
kernel. Monad bind is composition of the input measure with the continuation kernel.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

universe u v w

variable {m : Type u → Type v} {α β : Type u}

section

variable {ρ : Type w}

/-- The kernel denoted by a measurably parameterized family of computations. -/
noncomputable def evalDistKernel [EvalDistSemantics m]
    [MeasurableSpace ρ] [MeasurableSpace α] (f : ρ → m α)
    (hf : Measurable fun r => 𝒟[f r]) : Kernel ρ α :=
  ⟨fun r => 𝒟[f r], hf⟩

/-- On a discrete input space, every computation-valued family defines a kernel. -/
noncomputable def evalDistKernelOfDiscrete [EvalDistSemantics m]
    [MeasurableSpace ρ] [DiscreteMeasurableSpace ρ] [MeasurableSpace α]
    (f : ρ → m α) : Kernel ρ α :=
  evalDistKernel f Measurable.of_discrete

@[simp]
theorem evalDistKernel_apply [EvalDistSemantics m]
    [MeasurableSpace ρ] [MeasurableSpace α] (f : ρ → m α)
    (hf : Measurable fun r => 𝒟[f r]) (r : ρ) :
    evalDistKernel f hf r = 𝒟[f r] := rfl

@[simp]
theorem evalDistKernelOfDiscrete_apply [EvalDistSemantics m]
    [MeasurableSpace ρ] [DiscreteMeasurableSpace ρ] [MeasurableSpace α]
    (f : ρ → m α) (r : ρ) :
    evalDistKernelOfDiscrete f r = 𝒟[f r] := rfl

instance evalDistKernel.instIsSubprobabilityKernel [EvalDistSemantics m]
    [MeasurableSpace ρ] [MeasurableSpace α] (f : ρ → m α)
    (hf : Measurable fun r => 𝒟[f r]) :
    IsSubprobabilityKernel (evalDistKernel f hf) :=
  ⟨fun r => evalDist_apply_univ_le_one (f r)⟩

instance evalDistKernelOfDiscrete.instIsSubprobabilityKernel [EvalDistSemantics m]
    [MeasurableSpace ρ] [DiscreteMeasurableSpace ρ] [MeasurableSpace α]
    (f : ρ → m α) : IsSubprobabilityKernel (evalDistKernelOfDiscrete f) :=
  ⟨fun r => evalDist_apply_univ_le_one (f r)⟩

/-- A lossless computation family denotes a Markov kernel. -/
theorem isMarkovKernel_evalDistKernel [EvalDistSemantics m]
    [MeasurableSpace ρ] [MeasurableSpace α] (f : ρ → m α)
    (hf : Measurable fun r => 𝒟[f r])
    (hProbability : ∀ r, IsProbabilityMeasure 𝒟[f r]) :
    IsMarkovKernel (evalDistKernel f hf) :=
  ⟨hProbability⟩

/-- Monad bind is composition of a measure with the continuation kernel. -/
theorem evalDist_bind_eq_comp [Monad m] [EvalDistSemantics m] [LawfulEvalDistSemantics m]
    [MeasurableSpace α] [MeasurableSpace β] (mx : m α) (f : α → m β)
    (hf : Measurable fun x => 𝒟[f x]) :
    𝒟[mx >>= f] = evalDistKernel f hf ∘ₘ 𝒟[mx] :=
  evalDist_bind mx f hf

/-- Discrete-domain specialization of `evalDist_bind_eq_comp`. -/
theorem evalDist_bind_eq_comp_of_discrete [Monad m] [EvalDistSemantics m]
    [LawfulEvalDistSemantics m] [MeasurableSpace α] [DiscreteMeasurableSpace α]
    [MeasurableSpace β] (mx : m α) (f : α → m β) :
    𝒟[mx >>= f] = evalDistKernelOfDiscrete f ∘ₘ 𝒟[mx] :=
  evalDist_bind_of_discrete mx f

namespace MeasureSemanticsVia

variable [Monad m]

/-- A local bundled semantics turns a measurable family of surface computations into a kernel. -/
noncomputable def evalDistKernel (sem : MeasureSemanticsVia m)
    [MeasurableSpace ρ] [MeasurableSpace α] (f : ρ → m α)
    (hf : Measurable fun r => sem.evalDist (f r)) : Kernel ρ α :=
  ⟨fun r => sem.evalDist (f r), hf⟩

@[simp]
theorem evalDistKernel_apply (sem : MeasureSemanticsVia m)
    [MeasurableSpace ρ] [MeasurableSpace α] (f : ρ → m α)
    (hf : Measurable fun r => sem.evalDist (f r)) (r : ρ) :
    sem.evalDistKernel f hf r = sem.evalDist (f r) := rfl

instance evalDistKernel.instIsSubprobabilityKernel (sem : MeasureSemanticsVia m)
    [MeasurableSpace ρ] [MeasurableSpace α] (f : ρ → m α)
    (hf : Measurable fun r => sem.evalDist (f r)) :
    IsSubprobabilityKernel (sem.evalDistKernel f hf) :=
  ⟨fun r => sem.evalDist_apply_univ_le_one (f r)⟩

end MeasureSemanticsVia

end

namespace ReaderT

variable {ρ : Type u}

/-- A reader computation denotes a kernel from environments to output distributions. -/
noncomputable def evalDistKernel [EvalDistSemantics m]
    [MeasurableSpace ρ] [MeasurableSpace α] (mx : ReaderT ρ m α)
    (hMeasurable : Measurable fun environment => 𝒟[mx environment]) : Kernel ρ α :=
  _root_.evalDistKernel mx hMeasurable

/-- Discrete environments discharge the reader kernel's measurability obligation. -/
noncomputable def evalDistKernelOfDiscrete [EvalDistSemantics m]
    [MeasurableSpace ρ] [DiscreteMeasurableSpace ρ] [MeasurableSpace α]
    (mx : ReaderT ρ m α) : Kernel ρ α :=
  _root_.evalDistKernelOfDiscrete mx

@[simp]
theorem evalDistKernel_apply [EvalDistSemantics m]
    [MeasurableSpace ρ] [MeasurableSpace α] (mx : ReaderT ρ m α)
    (hMeasurable : Measurable fun environment => 𝒟[mx environment]) (environment : ρ) :
    ReaderT.evalDistKernel mx hMeasurable environment = 𝒟[mx environment] := rfl

instance evalDistKernel.instIsSubprobabilityKernel [EvalDistSemantics m]
    [MeasurableSpace ρ] [MeasurableSpace α] (mx : ReaderT ρ m α)
    (hMeasurable : Measurable fun environment => 𝒟[mx environment]) :
    IsSubprobabilityKernel (ReaderT.evalDistKernel mx hMeasurable) :=
  ⟨fun environment => evalDist_apply_univ_le_one (mx environment)⟩

/-- A lossless reader computation denotes a Markov kernel. -/
theorem isMarkovKernel_evalDistKernel [EvalDistSemantics m]
    [MeasurableSpace ρ] [MeasurableSpace α] (mx : ReaderT ρ m α)
    (hMeasurable : Measurable fun environment => 𝒟[mx environment])
    (hProbability : ∀ environment, IsProbabilityMeasure 𝒟[mx environment]) :
    IsMarkovKernel (ReaderT.evalDistKernel mx hMeasurable) :=
  _root_.isMarkovKernel_evalDistKernel mx hMeasurable hProbability

end ReaderT

namespace StateT

variable {ρ : Type u}

/-- A state computation denotes a kernel from initial state to result and final state. -/
noncomputable def evalDistKernel [EvalDistSemantics m]
    [MeasurableSpace ρ] [MeasurableSpace α] (mx : StateT ρ m α)
    (hMeasurable : Measurable fun state => 𝒟[mx state]) : Kernel ρ (α × ρ) :=
  _root_.evalDistKernel mx hMeasurable

/-- Discrete states discharge the state kernel's measurability obligation. -/
noncomputable def evalDistKernelOfDiscrete [EvalDistSemantics m]
    [MeasurableSpace ρ] [DiscreteMeasurableSpace ρ] [MeasurableSpace α]
    (mx : StateT ρ m α) : Kernel ρ (α × ρ) :=
  _root_.evalDistKernelOfDiscrete mx

@[simp]
theorem evalDistKernel_apply [EvalDistSemantics m]
    [MeasurableSpace ρ] [MeasurableSpace α] (mx : StateT ρ m α)
    (hMeasurable : Measurable fun state => 𝒟[mx state]) (state : ρ) :
    StateT.evalDistKernel mx hMeasurable state = 𝒟[mx state] := rfl

instance evalDistKernel.instIsSubprobabilityKernel [EvalDistSemantics m]
    [MeasurableSpace ρ] [MeasurableSpace α] (mx : StateT ρ m α)
    (hMeasurable : Measurable fun state => 𝒟[mx state]) :
    IsSubprobabilityKernel (StateT.evalDistKernel mx hMeasurable) :=
  ⟨fun state => evalDist_apply_univ_le_one (mx state)⟩

/-- A lossless state computation denotes a Markov kernel. -/
theorem isMarkovKernel_evalDistKernel [EvalDistSemantics m]
    [MeasurableSpace ρ] [MeasurableSpace α] (mx : StateT ρ m α)
    (hMeasurable : Measurable fun state => 𝒟[mx state])
    (hProbability : ∀ state, IsProbabilityMeasure 𝒟[mx state]) :
    IsMarkovKernel (StateT.evalDistKernel mx hMeasurable) :=
  _root_.isMarkovKernel_evalDistKernel mx hMeasurable hProbability

/-- Discarding the final state is the first marginal of the state kernel. -/
theorem evalDist_run'_eq_fst [Functor m] [EvalDistSemantics m]
    [MeasurableSpace ρ] [MeasurableSpace α]
    (mx : StateT ρ m α) (hMeasurable : Measurable fun state => 𝒟[mx state])
    (state : ρ)
    (hMap : 𝒟[Prod.fst <$> mx state] = (𝒟[mx state]).map Prod.fst) :
    𝒟[mx.run' state] = (StateT.evalDistKernel mx hMeasurable).fst state := by
  change 𝒟[Prod.fst <$> mx state] = (StateT.evalDistKernel mx hMeasurable).fst state
  rw [hMap, Kernel.fst_apply, StateT.evalDistKernel_apply]

end StateT
