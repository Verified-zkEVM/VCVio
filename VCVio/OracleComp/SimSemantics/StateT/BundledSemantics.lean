/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.OracleComp.ProbComp.Basic
public import VCVio.OracleComp.Constructions.UniformFinMeasure
public import VCVio.OracleComp.ProbCompLift
public import VCVio.OracleComp.Coercions.Add.Basic
public import VCVio.OracleComp.SimSemantics.Append
public import VCVio.OracleComp.SimSemantics.StateT.Basic.Native
public import VCVio.EvalDist.Defs.Semantics.Core
public import ToMathlib.Control.StateT

/-!
# Bundled Measure Semantics for Oracle Simulations

This file builds bundled measure semantics for the common oracle-simulation pattern used
throughout the crypto constructions in this repo:

1. a surface `OracleComp` program runs in a public-randomness world
2. selected oracle families are implemented by a `StateT`-based simulator over `ProbComp`
3. the final semantics is obtained by running the hidden state from a fixed initial cache and then
   observing the resulting `ProbComp` as a successful-output measure

`ProbCompRuntime.withStateOracle` bundles these semantics with the lift of plain `ProbComp`
sampling into the uniform summand, giving the runtime of such a world.
-/

@[expose] public section

open OracleComp OracleSpec

namespace MeasureSemanticsVia

/-- Measure semantics for an oracle world consisting of public randomness plus a hidden stateful
oracle implementation.

The surface computation is interpreted in `StateT σ ProbComp`; running it from `s` and discarding
the final state produces the visible successful-output measure directly. -/
noncomputable def withStateOracle
    {ι : Type} {hashSpec : OracleSpec ι} {σ : Type}
    (hashImpl : QueryImpl hashSpec (StateT σ ProbComp)) (s : σ) :
    MeasureSemanticsVia (OracleComp (unifSpec + hashSpec)) where
  Sem := StateT σ ProbComp
  instMonadSem := inferInstance
  interpret := simulateQ'
    ((QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT σ ProbComp) + hashImpl)
  observe := fun mx => 𝒟[StateT.run' mx s]
  observe_apply_univ_le_one := fun mx =>
    _root_.evalDist_apply_univ_le_one (StateT.run' mx s)

/-- The state-oracle measure semantics exposes the measure of the simulated run from its initial
state. -/
lemma withStateOracle_evalDist
    {ι : Type} {hashSpec : OracleSpec ι} {σ α : Type}
    (hashImpl : QueryImpl hashSpec (StateT σ ProbComp)) (s : σ)
    [MeasurableSpace α] (mx : OracleComp (unifSpec + hashSpec) α) :
    (MeasureSemanticsVia.withStateOracle hashImpl s).evalDist mx =
      𝒟[StateT.run' (simulateQ'
        ((QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT σ ProbComp) + hashImpl) mx) s] :=
  rfl

/-- Mapping a measurable function over a state-oracle computation maps its visible measure. -/
@[simp]
lemma withStateOracle_evalDist_map
    {ι : Type} {hashSpec : OracleSpec ι} {σ α β : Type}
    (hashImpl : QueryImpl hashSpec (StateT σ ProbComp)) (s : σ)
    [MeasurableSpace α] [MeasurableSpace β] (f : α → β) (hf : Measurable f)
    (mx : OracleComp (unifSpec + hashSpec) α) :
    (MeasureSemanticsVia.withStateOracle hashImpl s).evalDist (f <$> mx) =
      ((MeasureSemanticsVia.withStateOracle hashImpl s).evalDist mx).map f := by
  simp only [withStateOracle_evalDist, simulateQ_map,
    StateT.run'_map', evalDist_map _ hf]

/-- Binding a pure measurable function after a state-oracle computation maps its visible measure. -/
lemma withStateOracle_evalDist_bind_pure
    {ι : Type} {hashSpec : OracleSpec ι} {σ α β : Type}
    (hashImpl : QueryImpl hashSpec (StateT σ ProbComp)) (s : σ)
    [MeasurableSpace α] [MeasurableSpace β] (mx : OracleComp (unifSpec + hashSpec) α)
    (f : α → β) (hf : Measurable f) :
    (MeasureSemanticsVia.withStateOracle hashImpl s).evalDist (mx >>= fun x => pure (f x)) =
      ((MeasureSemanticsVia.withStateOracle hashImpl s).evalDist mx).map f := by
  simpa only [map_eq_bind_pure_comp, Function.comp_def] using
    withStateOracle_evalDist_map hashImpl s f hf mx

end MeasureSemanticsVia

namespace ProbCompRuntime

/-- Runtime for an oracle world consisting of public randomness plus a hidden stateful oracle
implementation `hashImpl` started from `s`. Experiments are observed through
`MeasureSemanticsVia.withStateOracle`, and plain `ProbComp` sampling lifts into the uniform
summand. -/
noncomputable def withStateOracle
    {ι : Type} {hashSpec : OracleSpec ι} {σ : Type}
    (hashImpl : QueryImpl hashSpec (StateT σ ProbComp)) (s : σ) :
    ProbCompRuntime (OracleComp (unifSpec + hashSpec)) where
  toMeasureSemanticsVia := MeasureSemanticsVia.withStateOracle hashImpl s
  toProbCompLift := ProbCompLift.ofMonadLift _
  evalDist_map_eq f hf mx := MeasureSemanticsVia.withStateOracle_evalDist_map _ _ f hf mx

/-- The state-oracle runtime observes the measure of the simulated run from its initial
state. -/
lemma withStateOracle_evalDist
    {ι : Type} {hashSpec : OracleSpec ι} {σ α : Type}
    (hashImpl : QueryImpl hashSpec (StateT σ ProbComp)) (s : σ)
    [MeasurableSpace α] (mx : OracleComp (unifSpec + hashSpec) α) :
    (ProbCompRuntime.withStateOracle hashImpl s).evalDist mx =
      𝒟[(simulateQ
        ((QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT σ ProbComp) + hashImpl)
          mx).run' s] :=
  rfl

end ProbCompRuntime
