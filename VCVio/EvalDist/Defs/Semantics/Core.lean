/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import PolyFun.Control.Monad.Hom
public import VCVio.EvalDist.Defs.Measure.Core
public import VCVio.EvalDist.Defs.Measure.OptionT
public import VCVio.EvalDist.Defs.Measure.ExceptT

/-!
# Bundled measure observations

`SemanticsVia` factors a computation through an internal monad and an external observer.
`MeasureSemanticsVia` makes the observer's measurable-space choice explicit and certifies
subprobability mass. Observation need not preserve bind: a fixed environment, initial state,
or output projection may hide internal effects at the observation boundary.

The bundles select interpretations as data, without choosing a global semantics instance.
Optional and exceptional observations retain unsuccessful runs as missing successful-output mass.
-/

public section

open MeasureTheory

universe u v w x

/-- Bundled semantics for `m` obtained by factoring through an internal semantic monad.

`SemanticsVia m Obs` packages the very general pattern:

1. interpret a computation in the surface monad `m` into some internal semantic monad `Sem`
2. observe the resulting internal computation as an external semantic object `Obs α`

The observation target `Obs` is generic: it can describe possible outcomes, traces, or other
observations independent of a probability representation. Measure-valued observations use
`MeasureSemanticsVia`, which also selects the output measurable space.

The important asymmetry is that `interpret` is required to be a monad morphism, while `observe`
is not. This lets us model semantics where running the internal computation requires fixing hidden
state or discarding auxiliary structure before exposing the final denotation. -/
structure SemanticsVia (m : Type u → Type v) [Monad m] (Obs : Type u → Type x) where
  /-- Internal monad used to give denotational meaning to computations in `m`. -/
  Sem : Type u → Type w
  /-- Monad structure on the internal semantic monad. -/
  [instMonadSem : Monad Sem]
  /-- Interpret a surface computation into the internal semantic monad. -/
  interpret : m →ᵐ Sem
  /-- Observe the internal semantic computation as an external semantic object, forgetting any
  hidden internal structure. -/
  observe : {α : Type u} → Sem α → Obs α

namespace SemanticsVia

variable {m : Type u → Type v} [Monad m] {Obs : Type u → Type x} {α : Type u}

/-- The external denotation of `mx` under a bundled semantics factorization. -/
@[expose]
def denote (sem : SemanticsVia m Obs) (mx : m α) : Obs α :=
  sem.observe (sem.interpret mx)

end SemanticsVia

/-! ## Measure-valued semantics -/

/-- Bundled subprobability semantics factoring a surface monad through an internal monad.

Unlike `SemanticsVia m Measure`, which cannot be formed because observing a `Measure α` requires
a selected measurable space, the measurable-space argument is explicit in `observe`. Failure or
nontermination is represented by missing mass. -/
structure MeasureSemanticsVia (m : Type u → Type v) [Monad m] where
  /-- Internal semantic monad. -/
  Sem : Type u → Type w
  /-- Monad structure carried by the internal semantics. -/
  [instMonadSem : Monad Sem]
  /-- Interpret a surface computation in the internal semantic monad. -/
  interpret : m →ᵐ Sem
  /-- Observe successful outputs as a Mathlib measure. -/
  observe : {α : Type u} → [MeasurableSpace α] → Sem α → Measure α
  /-- Every observation has total mass at most one. -/
  observe_apply_univ_le_one : ∀ {α : Type u} [MeasurableSpace α] (mx : Sem α),
    observe mx Set.univ ≤ 1

instance {m : Type u → Type v} [Monad m] (sem : MeasureSemanticsVia m) : Monad sem.Sem :=
  sem.instMonadSem

namespace MeasureSemanticsVia

variable {m : Type u → Type v} [Monad m] {α : Type u}

/-- The visible measure denoted by a computation under a bundled semantics. -/
@[expose]
noncomputable def evalDist (sem : MeasureSemanticsVia m) [MeasurableSpace α]
    (mx : m α) : Measure α :=
  sem.observe (sem.interpret mx)

@[simp]
theorem evalDist_apply_univ_le_one (sem : MeasureSemanticsVia m) [MeasurableSpace α]
    (mx : m α) : sem.evalDist mx Set.univ ≤ 1 :=
  sem.observe_apply_univ_le_one (sem.interpret mx)

/-- Every bundled observation is a subprobability measure. -/
instance evalDist.instIsSubprobabilityMeasure (sem : MeasureSemanticsVia m)
    [MeasurableSpace α] (mx : m α) : IsSubprobabilityMeasure (sem.evalDist mx) :=
  ⟨sem.evalDist_apply_univ_le_one mx⟩

/-- Failure probability is the mass missing from the successful-output measure. -/
@[expose]
noncomputable def probFailure (sem : MeasureSemanticsVia m) [MeasurableSpace α]
    (mx : m α) : ENNReal :=
  1 - sem.evalDist mx Set.univ

@[simp]
theorem probFailure_le_one (sem : MeasureSemanticsVia m) [MeasurableSpace α]
    (mx : m α) : sem.probFailure mx ≤ 1 :=
  tsub_le_self

/-- Package a global `EvalDistSemantics` instance as a local bundled semantics. -/
@[expose]
protected noncomputable def ofEvalDistSemantics (m : Type u → Type v) [Monad m]
    [EvalDistSemantics m] : MeasureSemanticsVia m where
  Sem := m
  instMonadSem := inferInstance
  interpret := MonadHom.id m
  observe := fun mx ↦ EvalDistSemantics.denote mx
  observe_apply_univ_le_one := fun mx ↦ EvalDistSemantics.apply_univ_le_one mx

@[simp]
theorem ofEvalDistSemantics_evalDist (mx : m α) [EvalDistSemantics m]
    [MeasurableSpace α] :
    (MeasureSemanticsVia.ofEvalDistSemantics m).evalDist mx = 𝒟[mx] := by
  rfl

/-- Bundling a lossless denotation preserves its probability-measure certificate. -/
instance ofEvalDistSemantics.instIsProbabilityMeasure [EvalDistSemantics m]
    [MeasurableSpace α] (mx : m α) [IsProbabilityMeasure 𝒟[mx]] :
    IsProbabilityMeasure ((MeasureSemanticsVia.ofEvalDistSemantics m).evalDist mx) :=
  inferInstanceAs (IsProbabilityMeasure 𝒟[mx])

/-- Bundle the successful-output semantics of an optional computation. Its observation
measures present outputs and retains any underlying failure as missing mass. -/
@[expose]
protected noncomputable def optionT (m : Type u → Type v) [Monad m]
    [EvalDistSemantics m] : MeasureSemanticsVia (OptionT m) where
  Sem := OptionT m
  instMonadSem := inferInstance
  interpret := MonadHom.id (OptionT m)
  observe := fun mx ↦ (𝒟[mx.run]).comap some
  observe_apply_univ_le_one := fun mx ↦
    by simpa only [OptionT.evalDist_eq_comap_some] using
      _root_.evalDist_apply_univ_le_one mx

@[simp]
theorem optionT_evalDist (mx : OptionT m α) [EvalDistSemantics m]
    [MeasurableSpace α] :
    (MeasureSemanticsVia.optionT m).evalDist mx = (𝒟[mx.run]).dropNone := by
  exact (Measure.dropNone_eq_comap_some _).symm

/-- Optional bundling preserves a known successful-output probability certificate. -/
instance optionT.instIsProbabilityMeasure [EvalDistSemantics m]
    [MeasurableSpace α] (mx : OptionT m α) [IsProbabilityMeasure 𝒟[mx]] :
    IsProbabilityMeasure ((MeasureSemanticsVia.optionT m).evalDist mx) := by
  rw [optionT_evalDist, Measure.dropNone_eq_comap_some, ← OptionT.evalDist_eq_comap_some]
  infer_instance

/-- Bundle the effect-native successful-output semantics of `ExceptT`. Errors remain observable
in the run measure and are discarded only by the `Except.ok` observation at this boundary. -/
@[expose]
protected noncomputable def exceptT (ε : Type u) [MeasurableSpace ε]
    (m : Type u → Type v) [Monad m] [EvalDistSemantics m] :
    MeasureSemanticsVia (ExceptT ε m) where
  Sem := ExceptT ε m
  instMonadSem := inferInstance
  interpret := MonadHom.id (ExceptT ε m)
  observe := fun mx ↦ (𝒟[mx.run]).comap Except.ok
  observe_apply_univ_le_one := fun mx ↦
    by simpa only [ExceptT.evalDist_eq_comap_ok] using
      _root_.evalDist_apply_univ_le_one mx

@[simp]
theorem exceptT_evalDist (ε : Type u) [MeasurableSpace ε]
    (mx : ExceptT ε m α) [EvalDistSemantics m] [MeasurableSpace α] :
    (MeasureSemanticsVia.exceptT ε m).evalDist mx = (𝒟[mx.run]).comap Except.ok := by
  rfl

/-- Exceptional bundling preserves a known successful-output probability certificate. -/
instance exceptT.instIsProbabilityMeasure {ε : Type u} [MeasurableSpace ε]
    [EvalDistSemantics m] [MeasurableSpace α] (mx : ExceptT ε m α)
    [IsProbabilityMeasure 𝒟[mx]] :
    IsProbabilityMeasure ((MeasureSemanticsVia.exceptT ε m).evalDist mx) := by
  rw [exceptT_evalDist, ← ExceptT.evalDist_eq_comap_ok]
  infer_instance

end MeasureSemanticsVia
