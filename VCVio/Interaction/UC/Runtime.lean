/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import PolyFun.Interaction.Basic.Sampler
public import PolyFun.Interaction.Basic.TypeTreeFintype
public import PolyFun.Interaction.UC.OpenProcessModel
public import VCVio.Interaction.UC.Computational
public import VCVio.OracleComp.Constructions.SampleableType

/-!
# Runtime execution semantics for open processes

This file bridges the structural `OpenProcess` layer to the bundled
sub-probabilistic semantics (`UC.Semantics`) by defining how to execute
a closed process.

The core runtime primitives (`TypeTree.Sampler`, `samplePath`,
`StepOver.sample`, `ProcessOver.runSteps`) are parameterized by an
arbitrary monad `m : Type → Type`. This generality lets the execution
intermediate monad carry additional capabilities, such as shared oracle
access (random oracles, CRS, …), while the bundled
`MeasureSemanticsVia m` fixes how those capabilities are collapsed into the
externally visible `Measure Result`.

Common instantiations:

* `m = ProbComp` with its canonical measure semantics for
  coin-flip-only protocols. Use `processSemanticsProbComp`.

* `m = OracleComp (unifSpec + roSpec)` with a bundled measure semantics
  whose internal monad is `StateT σ ProbComp` and whose
  interpreter is `simulateQ' impl`. Use `processSemanticsOracle` for
  protocols in the random oracle model, where `impl` combines a
  `unifSpec` identity lift with `randomOracle` (or any `QueryImpl`).

* Observation-style semantics that deliberately carry failure mass,
  for example `m = OptionT ProbComp` with the canonical adapter. This is what
  cryptographic smoke tests (OTP-style privacy, guess games) use so
  that the `guard` branch contributes a real failure mass to the
  resulting visible measure.

## Main definitions

* `TypeTree.Sampler m spec` provides an `m X` computation at each node of
  a `TypeTree`, resolving each move in the intermediate monad.

* `TypeTree.samplePath` executes a sampler to produce a full path in `m`.

* `StepOver.sample` runs one step by sampling a transcript and applying
  the continuation.

* `ProcessOver.runSteps` iterates `sample` for a fixed number of steps.

* `UC.processSemantics` constructs a `Semantics (openTheory Party)`
  from a bundled `MeasureSemanticsVia m`, an initial state, a step sampler,
  a fuel count, and an observation function. The resulting semantics
  observes closed systems through `sem.evalDist`.

* `UC.processSemanticsProbComp` is the specialization for `m =
  ProbComp` with its canonical measure semantics.

* `UC.processSemanticsOracle` constructs semantics for protocols with
  shared oracle access, collapsing the oracle layer through
  `simulateQ'`.

## Universe constraints

The runtime layer requires the spec and state type universes to be `0`,
since `ProbComp : Type → Type` operates in `Type`. This is satisfied by
concrete protocols whose move types and state types live in `Type`.
-/

@[expose] public section

universe u

open OracleComp

namespace Interaction

namespace TypeTree

/--
Uniform selection from a nonempty finite type as a `ProbComp` primitive,
realized by sampling through the `SampleableType.ofFintype` bridge (which
reduces to uniform selection on `Fin (Fintype.card X)` via `Fintype.equivFin`).
This lands in `ProbComp` so that uniform sampling can be plugged directly into per-node
components of a `Sampler ProbComp spec`.
-/
noncomputable def probCompUniformOfFintype (X : Type) [Fintype X] [Nonempty X] : ProbComp X :=
  letI := SampleableType.ofFintype X
  $ᵗ X

/--
Canonical uniform sampler on a finite, nonempty-branching tree, built by
recursion on the two ornaments: each node samples uniformly from its move
space using `probCompUniformOfFintype`, and the continuation samplers are
produced recursively from the corresponding per-branch ornaments.

This is the interaction-spec analogue of `SampleableType` for
`OracleSpec`: concrete `spec` trees whose move types all carry `Fintype`
and `Nonempty` synthesize separate `TypeTree.Fintype spec` and
`TypeTree.Nonempty spec` instances automatically, yielding `Sampler.uniform
spec` as the canonical coin-flip-only sampler for downstream runtime
semantics (`processSemanticsProbComp`, etc.).
-/
noncomputable def Sampler.uniform :
    (spec : TypeTree.{0}) → TypeTree.Fintype spec → TypeTree.Nonempty spec →
      Sampler ProbComp spec
  | .done, _, _ => ⟨⟩
  | .node X rest, .node hFin hFinRec, hNon =>
      (@probCompUniformOfFintype X hFin (TypeTree.Nonempty.rootNonempty hNon),
        fun x => Sampler.uniform (rest x) (hFinRec x) (TypeTree.Nonempty.rest hNon x))

/-- Instance-argument form of `Sampler.uniform`. -/
@[reducible]
noncomputable def Sampler.uniformI (spec : TypeTree.{0})
    [hFin : TypeTree.Fintype spec] [hNon : TypeTree.Nonempty spec] :
    Sampler ProbComp spec :=
  Sampler.uniform spec hFin hNon

/-! Smoke test: typeclass synthesis builds separate `TypeTree.Fintype` and
`TypeTree.Nonempty` instances for a concrete spec, and `Sampler.uniformI`
elaborates against both. -/

private example : TypeTree.Fintype
    (TypeTree.node Bool (fun _ => TypeTree.node (Fin 4) (fun _ => TypeTree.done))) :=
  inferInstance

private example : TypeTree.Nonempty
    (TypeTree.node Bool (fun _ => TypeTree.node (Fin 4) (fun _ => TypeTree.done))) :=
  inferInstance

private noncomputable example :
    Sampler ProbComp
      (TypeTree.node Bool (fun _ => TypeTree.node (Fin 4) (fun _ => TypeTree.done))) :=
  Sampler.uniformI _

end TypeTree

namespace Concurrent

/--
Run one step of a `ProcessOver` by sampling a transcript from the step's
spec and applying the continuation to get the next state.
-/
noncomputable def StepOver.sample {m : Type → Type} [Monad m]
    {Γ : TypeTree.Node.Context} {P : Type}
    (step : StepOver Γ P) (sampler : TypeTree.Sampler m step.tree) : m P :=
  step.next <$> TypeTree.samplePath step.tree sampler

/--
Run `fuel` steps of a process, starting from state `s`, using a
state-dependent sampler at each step.
-/
noncomputable def ProcessOver.runSteps {m : Type → Type} [Monad m]
    {Γ : TypeTree.Node.Context} {P : Type}
    (process : ProcessOver P Γ)
    (sampler : (p : process.Proc) → TypeTree.Sampler m (process.step p).tree) :
    ℕ → process.Proc → m process.Proc
  | 0, s => pure s
  | n + 1, s => (process.step s).sample (sampler s) >>= runSteps process sampler n

end Concurrent

namespace UC

open Concurrent

abbrev RuntimeClosed (Party : Type u) (m : Type → Type) (schedulerSampler : m (ULift Bool)) :=
  (openTheory.{u, 0, 0, 0} Party m schedulerSampler).Closed

/--
Construct a `Semantics` for the open-process theory, parameterized by a
surface execution monad `m` together with bundled measure semantics.

The execution runs entirely in `m`: per-step samplers come from the
`OpenProcess`'s `stepSampler` field, multi-step iteration threads them,
and the observer extracts the final judgment as an `m Result` value. The
bundled `sem` then collapses the `m Result` game into a visible measure via
`Semantics.evalDist`.

See `processSemanticsProbComp` for the coin-flip-only specialization
and `processSemanticsOracle` for the shared-oracle specialization.
-/
noncomputable def processSemantics (Party : Type u) {m : Type → Type} [Monad m] {Result : Type}
    [MeasurableSpace Result]
    (schedulerSampler : m (ULift Bool)) (sem : MeasureSemanticsVia.{0, 0, 0} m)
    (init : ∀ (p : RuntimeClosed Party m schedulerSampler), p.Proc) (fuel : ℕ)
    (observe : ∀ (p : RuntimeClosed Party m schedulerSampler), p.Proc → m Result) :
    Semantics (openTheory.{u, 0, 0, 0} Party m schedulerSampler) where
  Result := Result
  instMeasurableSpace := inferInstance
  m := m
  instMonad := inferInstance
  sem := sem
  run process :=
    ProcessOver.runSteps process.toProcess process.stepSampler fuel (init process) >>=
      observe process

/--
`processSemanticsProbComp` is the specialization of `processSemantics`
for `m = ProbComp` with its canonical measure semantics.
This is the right entry point for coin-flip-only protocols with no
shared oracles and no deliberate failure mass.
-/
noncomputable def processSemanticsProbComp (Party : Type u) {Result : Type}
    [MeasurableSpace Result]
    (schedulerSampler : ProbComp (ULift Bool))
    (init : ∀ (p : RuntimeClosed Party ProbComp schedulerSampler), p.Proc) (fuel : ℕ)
    (observe : ∀ (p : RuntimeClosed Party ProbComp schedulerSampler), p.Proc → ProbComp Result) :
    Semantics (openTheory.{u, 0, 0, 0} Party ProbComp schedulerSampler) :=
  processSemantics Party schedulerSampler
    (MeasureSemanticsVia.ofEvalDistSemantics ProbComp)
    init fuel observe

/--
`processSemanticsOracle` constructs semantics for protocols with shared
oracle access (random oracles, CRS, etc.).

The surface monad is `OracleComp superSpec`, where `superSpec` describes
all oracles available during execution. The bundled measure semantics
interprets those oracle queries by `simulateQ' impl` into
`StateT σ ProbComp`, initializing the oracle state to `initOracle` and
projecting onto the output to obtain the final visible measure.

For a protocol in the random oracle model, a typical instantiation is:
* `superSpec := unifSpec + (D →ₒ R)` (uniform sampling plus hash oracle)
* `impl := HasQuery.toQueryImpl.liftTarget _ + randomOracle`
  (identity on `unifSpec`, lazy-cached on the hash)
* `initOracle := ∅` (empty random oracle cache)
-/
noncomputable def processSemanticsOracle (Party : Type u) {ι : Type}
    {superSpec : OracleSpec.{0, 0} ι} {σ : Type} {Result : Type}
    [MeasurableSpace Result]
    (schedulerSampler : OracleComp superSpec (ULift Bool))
    (impl : QueryImpl superSpec (StateT σ ProbComp)) (initOracle : σ)
    (init : ∀ (p : RuntimeClosed Party (OracleComp superSpec) schedulerSampler), p.Proc) (fuel : ℕ)
    (observe : ∀ (p : RuntimeClosed Party (OracleComp superSpec) schedulerSampler),
      p.Proc → OracleComp superSpec Result) :
    Semantics (openTheory.{u, 0, 0, 0} Party (OracleComp superSpec) schedulerSampler) :=
  let oracleSem : MeasureSemanticsVia.{0, 0, 0} (OracleComp superSpec) :=
    { Sem := StateT σ ProbComp
      instMonadSem := inferInstance
      interpret := simulateQ' impl
      observe := fun {_} {_} mx => (liftM (mx.run' initOracle) : SPMF _).toMeasure
      observe_apply_univ_le_one := fun {_} {_} mx =>
        SPMF.toMeasure_apply_univ_le_one (liftM (mx.run' initOracle) : SPMF _) }
  processSemantics Party (m := OracleComp superSpec) schedulerSampler oracleSem
    init fuel observe

end UC
end Interaction
