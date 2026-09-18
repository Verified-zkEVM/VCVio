/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.OracleComp.ProbComp
public import VCVio.OracleComp.Coercions.Add
public import VCVio.OracleComp.SimSemantics.Append
public import VCVio.OracleComp.SimSemantics.StateT.Basic
public import VCVio.EvalDist.Defs.Semantics
public import ToMathlib.Control.StateT

/-!
# Bundled Measure Semantics for Oracle Simulations

This file builds bundled measure semantics for the common oracle-simulation pattern used
throughout the crypto constructions in this repo:

1. a surface `OracleComp` program runs in a public-randomness world
2. selected oracle families are implemented by a `StateT`-based simulator over `ProbComp`
3. the final semantics is obtained by running the hidden state from a fixed initial cache and then
   observing the resulting `ProbComp` as a successful-output measure

The `SPMFSemantics` construction remains as the executable compatibility surface while runtime
consumers migrate to `MeasureSemanticsVia.withStateOracle`.
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

namespace SPMFSemantics

/-- Bundled `SPMF` semantics for an oracle world consisting of public randomness plus a hidden
stateful oracle implementation.

The surface monad is `OracleComp (unifSpec + hashSpec)`. Internally, computations are interpreted
by simulating the public-randomness queries with their identity implementation and the additional
oracle family `hashSpec` with the supplied stateful simulator `hashImpl`. The hidden state is then
initialized at `s` and discarded, leaving only the externally visible output subdistribution. -/
noncomputable def withStateOracle
    {ι : Type} {hashSpec : OracleSpec ι} {σ : Type}
    (hashImpl : QueryImpl hashSpec (StateT σ ProbComp)) (s : σ) :
    SPMFSemantics (OracleComp (unifSpec + hashSpec)) where
  Sem := StateT σ ProbComp
  instMonadSem := inferInstance
  interpret := simulateQ'
    ((QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT σ ProbComp) + hashImpl)
  observe := fun mx => (liftM (StateT.run' mx s) : SPMF _)

/-- `withStateOracle` commutes with `<$>`: mapping a function over the surface computation
is the same as mapping it over the observed `SPMF`.

This holds because `interpret` is the bundled monad morphism `simulateQ'`, and the `StateT`
observer `fun mx => toSPMF (StateT.run' mx s)` preserves `<$>` even though it is not a full
monad morphism: `<$>` does not thread state, so `Prod.fst <$> (f <$> mx).run s` factors as
`f <$> (Prod.fst <$> mx.run s) = f <$> StateT.run' mx s`. -/
@[simp] lemma withStateOracle_evalSPMF_map
    {ι : Type} {hashSpec : OracleSpec ι} {σ : Type}
    (hashImpl : QueryImpl hashSpec (StateT σ ProbComp)) (s : σ)
    {α β : Type} (f : α → β) (mx : OracleComp (unifSpec + hashSpec) α) :
    (SPMFSemantics.withStateOracle hashImpl s).evalSPMF (f <$> mx) =
      f <$> (SPMFSemantics.withStateOracle hashImpl s).evalSPMF mx := by
  set impl := (QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT σ ProbComp) + hashImpl
  change (liftM (StateT.run' (simulateQ impl (f <$> mx)) s) : SPMF _) =
    f <$> (liftM (StateT.run' (simulateQ impl mx) s) : SPMF _)
  rw [simulateQ_map, StateT.run'_map', liftM_map]

/-- `withStateOracle` commutes with the specific `>>= pure ∘ f` pattern produced by
a do-block returning a pure value at the end. A direct corollary of
`withStateOracle_evalSPMF_map`. -/
lemma withStateOracle_evalSPMF_bind_pure
    {ι : Type} {hashSpec : OracleSpec ι} {σ : Type}
    (hashImpl : QueryImpl hashSpec (StateT σ ProbComp)) (s : σ)
    {α β : Type} (mx : OracleComp (unifSpec + hashSpec) α) (f : α → β) :
    (SPMFSemantics.withStateOracle hashImpl s).evalSPMF (mx >>= fun x => pure (f x)) =
      f <$> (SPMFSemantics.withStateOracle hashImpl s).evalSPMF mx := by
  calc
    _ = (SPMFSemantics.withStateOracle hashImpl s).evalSPMF (f <$> mx) := by
      rw [map_eq_bind_pure_comp]
      rfl
    _ = _ := withStateOracle_evalSPMF_map hashImpl s f mx

end SPMFSemantics
