/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.OracleComp.ProbComp
public import VCVio.OracleComp.EvalDist.UniformCompatibility
public import VCVio.EvalDist.Defs.Semantics.Core
public import PolyFun.Control.Monad.Hom
import VCVio.EvalDist.Monad.Map

/-!
# Bundled Lifts from `ProbComp`

This file packages the "public randomness" capability separately from denotational semantics.

Many crypto constructions need two orthogonal pieces of structure on their ambient monad `m`:

1. a way to observe successful outputs as a measure
2. a way to *inject* plain probabilistic sampling into `m`

This file packages the second capability as a bundled monad homomorphism `ProbComp →ᵐ m`, so it
can be carried independently of whatever denotational semantics the construction uses. It also
defines `ProbCompRuntime`, the common crypto-facing bundle that pairs public-randomness lifting
with bundled measure semantics for an ambient monad.
-/

@[expose] public section

open MeasureTheory

universe v w

/-- Bundled way to lift plain probabilistic computations into an ambient monad `m`.

Intuitively, this is the capability "sample fresh public randomness inside `m`". We package it as
a monad homomorphism so it composes lawfully with `pure` and `bind`. -/
structure ProbCompLift (m : Type → Type v) [Monad m] where
  /-- Inject a plain `ProbComp` computation into `m`. -/
  liftProbComp : ProbComp →ᵐ m

namespace ProbCompLift

/-- Build a bundled `ProbCompLift` from an existing lawful `MonadLiftT ProbComp m` instance. -/
def ofMonadLift (m : Type → Type v) [Monad m]
    [MonadLiftT ProbComp m] [LawfulMonadLiftT ProbComp m] : ProbCompLift m where
  liftProbComp := MonadHom.ofLift ProbComp m

/-- The identity lift on `ProbComp` itself. -/
def id : ProbCompLift ProbComp where
  liftProbComp := MonadHom.id ProbComp

end ProbCompLift

/-- Common runtime bundle for crypto games in an ambient monad `m`.

This packages the two capabilities that security experiments usually need together:

1. `MeasureSemanticsVia m` to observe successful experiment outputs.
2. `ProbCompLift m` to sample fresh public randomness inside `m`.

The bundle is kept separate from the core scheme definitions so that executable scheme data does
not become noncomputable merely by carrying denotational semantics. -/
structure ProbCompRuntime (m : Type → Type v) [Monad m] where
  /-- Bundled successful-output measure semantics for the ambient monad. -/
  toMeasureSemanticsVia : MeasureSemanticsVia.{0, v, w} m
  /-- Bundled injection of plain probabilistic sampling into the ambient monad. -/
  toProbCompLift : ProbCompLift m
  /-- Observing a measurable map agrees with pushing the output measure forward. -/
  evalDist_map_eq : ∀ {α β : Type} [MeasurableSpace α] [MeasurableSpace β]
    (f : α → β), Measurable f → ∀ mx : m α,
      toMeasureSemanticsVia.evalDist (f <$> mx) =
        (toMeasureSemanticsVia.evalDist mx).map f

namespace ProbCompRuntime

variable {m : Type → Type v} [Monad m] {α : Type}

/-- Observe an ambient computation by its successful-output measure. -/
noncomputable def evalDist (runtime : ProbCompRuntime m) [MeasurableSpace α]
    (mx : m α) : Measure α :=
  runtime.toMeasureSemanticsVia.evalDist mx

/-- Failure probability of an ambient computation under the runtime's bundled semantics. -/
noncomputable def probFailure (runtime : ProbCompRuntime m) [MeasurableSpace α]
    (mx : m α) : ENNReal :=
  runtime.toMeasureSemanticsVia.probFailure mx

@[simp]
lemma evalDist_apply_univ_le_one (runtime : ProbCompRuntime m) [MeasurableSpace α]
    (mx : m α) : runtime.evalDist mx Set.univ ≤ 1 :=
  runtime.toMeasureSemanticsVia.evalDist_apply_univ_le_one mx

/-- Every runtime observation is a subprobability measure. Registering the bundled mass bound as
an instance lets the ordinary measure API discharge finite-mass and `≤ 1` side conditions. -/
instance (runtime : ProbCompRuntime m) [MeasurableSpace α] (mx : m α) :
    IsSubprobabilityMeasure (runtime.evalDist mx) :=
  ⟨runtime.evalDist_apply_univ_le_one mx⟩

/-- Runtime observation commutes with measurable maps. -/
@[simp]
lemma evalDist_map (runtime : ProbCompRuntime m) {β : Type}
    [MeasurableSpace α] [MeasurableSpace β] (f : α → β) (hf : Measurable f) (mx : m α) :
    runtime.evalDist (f <$> mx) = (runtime.evalDist mx).map f :=
  runtime.evalDist_map_eq f hf mx

/-- Binding a pure measurable function pushes the runtime's output measure forward. -/
lemma evalDist_bind_pure (runtime : ProbCompRuntime m) {β : Type}
    [LawfulMonad m] [MeasurableSpace α] [MeasurableSpace β]
    (mx : m α) (f : α → β) (hf : Measurable f) :
    runtime.evalDist (mx >>= fun x => pure (f x)) = (runtime.evalDist mx).map f := by
  rw [show (mx >>= fun x => pure (f x)) = f <$> mx from
    (map_eq_bind_pure_comp _ f mx).symm]
  exact runtime.evalDist_map f hf mx

/-- Lift a plain `ProbComp` computation into the ambient monad using the runtime's public
randomness capability. -/
def liftProbComp (runtime : ProbCompRuntime m) : ProbComp →ᵐ m :=
  runtime.toProbCompLift.liftProbComp

/-- Canonical runtime for `ProbComp` itself. -/
noncomputable def probComp : ProbCompRuntime ProbComp where
  toMeasureSemanticsVia := MeasureSemanticsVia.ofEvalDistSemantics ProbComp
  toProbCompLift := ProbCompLift.id
  evalDist_map_eq _f hf mx := _root_.evalDist_map mx hf

@[simp]
lemma probComp_evalDist [MeasurableSpace α] (mx : ProbComp α) :
    probComp.evalDist mx = 𝒟[mx] := rfl

/-- The canonical `ProbComp` runtime satisfies the pure-return factoring law: `evalDist`
commutes with binding a pure measurable function. Security decompositions that couple several
experiments through one joint execution (e.g. the exact SUF-CMA partition in
`VCVio.CryptoFoundations.SignatureAlg`) take exactly this equation as their pull-through
hypothesis, so consumers instantiating them at `ProbCompRuntime.probComp` can use this
lemma directly. -/
lemma probComp_evalDist_bind_pure {α β : Type} [MeasurableSpace α] [MeasurableSpace β]
    (f : α → β) (hf : Measurable f) (mx : ProbComp α) :
    probComp.evalDist (mx >>= fun x => pure (f x)) = (probComp.evalDist mx).map f := by
  exact probComp.evalDist_bind_pure mx f hf

end ProbCompRuntime
