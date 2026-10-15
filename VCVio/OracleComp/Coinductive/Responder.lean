/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module
public import VCVio.OracleComp.Coinductive.DynSystem
public import VCVio.OracleComp.QueryTracking.RandomOracle.Basic
public import VCVio.EvalDist.Kernel
public import PolyFun.PFunctor.Dynamical.Game

/-!
# Probabilistic Wiring: Adversary Strategies Against Stateful Responders

`ProbResponder spec` is the challenger side of an interactive game presented as a
coalgebra: a measurable state space together with, for each query, a *joint*
subprobability kernel over the answer and the next state. It is a Mealy machine in the
Kleisli category of subprobability kernels. An optional coherent executable
presentation as a stateful handler `QueryImpl spec (StateT State ProbComp)`, whose output
measures are the kernels, is available through `ProbResponder.IsExecutable`,
`ProbResponder.IsExecutable.answerComp`, and `ProbResponder.toQueryImpl`.

Wiring a responder against an adversary `OracleStrategy` is not a hand-rolled
construction: `stepAgainst` / `iterateAgainst` are PolyFun's generic eval-wired runs
`PFunctor.DynSystem.stepWith` / `iterWith` instantiated at `m := ProbComp`, driven by the
responder's stateful handler. The responder state comes first in the product state,
matching the upstream handler-state-first convention and the challenger-first state of
`PFunctor.DynSystem.closedGame`; a deterministic responder (`ProbResponder.ofDet`) wires
to `pure` of the closed-game step (`stepAgainst_ofDet`). `transcriptAgainst` additionally
records the exchanged queries and answers — `QueryLog` is VCVio vocabulary, so the
transcript form lives here rather than upstream.

Memoryless oracles embed as responders with trivial (`ProbResponder.ofHandler`) or
constant (`ProbResponder.ofHandlerFamily`) state, and the wired run then collapses to
the memoryless runs `OracleStrategy.kleisliStep` / `kleisliIterate`
(`stepAgainst_ofHandler` and companions) — the setup-indexed family form of the upstream
stateless collapses `PFunctor.DynSystem.stepWith_lift` / `iterWith_lift`. The
per-run-sampled oracle of a one-shot security game is exactly the constant-state case.
Genuinely stateful challengers enter through `ProbResponder.ofQueryImpl` (from a
`QueryImpl` into `StateT σ ProbComp`, read through its output measures): the lazy random
oracle (`randomOracleResponder`) is the motivating instance, and cached LR encryption
oracles fit the same constructor at the `CryptoFoundations` layer. The joint
answer/state draw is essential for these — the cache entry a random oracle stores must
be the very answer it returned.

## Categorical view (Spivak–Niu)

A *deterministic* responder is a dynamical system over the internal hom `[p, y]` of
Spivak–Niu §4.5 (for `p` the interface polynomial `spec.toPFunctor`) — PolyFun's
`PFunctor.Responder`, which embeds here as the Dirac case `ProbResponder.ofDet`.
Closing an adversary against a responder is wiring along the evaluation map
`eval : [p, y] ⊗ p → y`: `stepAgainst` keeps that wiring as deterministic combinatorial
data and lets the *states* advance in the Kleisli category of `ProbComp` — one synchronized
step of the tensor system with the evaluation wiring applied, which is precisely the upstream
`stepWith`. `ProbResponder` is strictly more general
than a Kleisli lift of an `[p, y]`-system, because the answer and the next state are
drawn jointly rather than the state first determining a handler. The UC layer's
`processSemanticsOracle` is the heavyweight sibling of this construction (multi-party,
scheduler-driven); this file is the minimal two-party core, and neither is derived from
the other.

Wired runs of machine adversaries (an `OracleMachine.runK` against a responder rather
than a memoryless handler) live in `VCVio.OracleComp.Coinductive.WiredRun`.
-/

@[expose] public section

universe u v

open OracleSpec

variable {ι : Type u} {spec : OracleSpec.{u, u} ι} {S : Type u}

/-! ## Probabilistic stateful responders -/

/-- A probabilistic stateful responder: the challenger side of an interactive game, as
a Mealy coalgebra in the Kleisli category of subprobability kernels. From a state, each
query yields a joint subprobability measure over the answer and the successor state.
The joint draw matters:
a lazy random oracle's stored cache entry must be the very answer it returned, which no
answer-then-state factorization expresses. -/
structure ProbResponder {ι : Type u} (spec : OracleSpec.{u, u} ι) where
  /-- The responder's internal state (the challenger's memory). -/
  State : Type u
  /-- The measurable structure on the responder's private state. -/
  instMeasurableSpaceState : MeasurableSpace State
  /-- The measurable structure on the answer to each query. -/
  instMeasurableSpaceRange : (t : spec.Domain) → MeasurableSpace (spec.Range t)
  /-- Answer a query from a state, jointly drawing the successor state. -/
  answerKernel : (t : spec.Domain) →
    letI := instMeasurableSpaceState
    letI := instMeasurableSpaceRange t
    ProbabilityTheory.Kernel State (spec.Range t × State)
  /-- Each query kernel is subprobabilistic. -/
  answerKernel_isSubprobability : ∀ t,
    letI := instMeasurableSpaceState
    letI := instMeasurableSpaceRange t
    ProbabilityTheory.IsSubprobabilityKernel (answerKernel t)

attribute [instance] ProbResponder.instMeasurableSpaceState

namespace ProbResponder

open MeasureTheory ProbabilityTheory

/-- The subprobability invariant stored by a responder, exposed as an instance. -/
instance answerKernel.instIsSubprobabilityKernel (R : ProbResponder spec)
    (t : spec.Domain) :
    letI := R.instMeasurableSpaceRange t
    IsSubprobabilityKernel (R.answerKernel t) :=
  R.answerKernel_isSubprobability t

section Executable

variable {ι : Type} {spec : OracleSpec.{0, 0} ι}

/-- A coherent executable realization of a kernel responder: a `ProbComp` program for each state
and query whose output measure is the stored kernel. This separate typeclass lets kernel-native
responders remain genuinely measure-theoretic, while responders built from VCVio's `ProbComp`
execution layer retain their program without imposing countability on abstract state or answer
types.

The state and answer σ-algebras of an executable responder separate points. This is what makes
the kernel determine the program's distribution (`IsExecutable.answerComp_evalDistEq`): a
program's output measure in a σ-algebra that does not separate points, such as the trivial one,
forgets the program's point masses, so two programs with the same output measure could still
play a game differently. -/
class IsExecutable (R : ProbResponder spec) where
  /-- The executable answer-and-successor-state program. -/
  answerComp : R.State → (t : spec.Domain) → ProbComp (spec.Range t × R.State)
  /-- The state σ-algebra separates points. -/
  instMeasurableSingletonClassState :
    letI := R.instMeasurableSpaceState
    MeasurableSingletonClass R.State
  /-- The answer σ-algebra of every query separates points. -/
  instMeasurableSingletonClassRange : ∀ t,
    letI := R.instMeasurableSpaceRange t
    MeasurableSingletonClass (spec.Range t)
  /-- The executable realization denotes exactly the stored answer kernel. -/
  answerKernel_eq_evalDist : ∀ s t,
    letI := R.instMeasurableSpaceRange t
    R.answerKernel t s = 𝒟[answerComp s t]

/-- The authoritative kernel determines the output measure of every executable realization. -/
theorem IsExecutable.evalDist_answerComp_eq (R : ProbResponder spec)
    (E₁ E₂ : R.IsExecutable) (s : R.State) (t : spec.Domain) :
    letI := R.instMeasurableSpaceRange t
    𝒟[E₁.answerComp s t] = 𝒟[E₂.answerComp s t] := by
  let _ := R.instMeasurableSpaceRange t
  rw [← E₁.answerKernel_eq_evalDist s t, ← E₂.answerKernel_eq_evalDist s t]

/-- The authoritative kernel determines every executable realization up to equality in
distribution: since the responder's σ-algebras separate points, the output measure of a
realization records each of its point masses. -/
theorem IsExecutable.answerComp_evalDistEq (R : ProbResponder spec)
    (E₁ E₂ : R.IsExecutable) (s : R.State) (t : spec.Domain) :
    E₁.answerComp s t =ᵈ E₂.answerComp s t := by
  refine OracleComp.evalDistEq_of_forall_prEvent_eq_output fun x => ?_
  let _ := R.instMeasurableSpaceRange t
  have := E₁.instMeasurableSingletonClassState
  have := E₁.instMeasurableSingletonClassRange t
  rw [prEvent_eq_evalDist_singleton, prEvent_eq_evalDist_singleton,
    IsExecutable.evalDist_answerComp_eq R E₁ E₂ s t]

/-- Build a kernel responder from an executable `ProbComp`-valued stateful handler, read through
its output measures. The constructor equips the state and answers with local discrete measurable
structures; it does not install blanket measurable-space instances on the underlying types. -/
@[reducible] noncomputable def ofQueryImpl {σ : Type}
    (impl : QueryImpl spec (StateT σ ProbComp)) : ProbResponder spec where
  State := σ
  instMeasurableSpaceState := ⊤
  instMeasurableSpaceRange := fun _ => ⊤
  answerKernel t := by
    letI : MeasurableSpace σ := ⊤
    letI : MeasurableSpace (spec.Range t) := ⊤
    exact evalDistKernelOfDiscrete fun s => impl t s
  answerKernel_isSubprobability t := by infer_instance

/-- A stateful `ProbComp` handler is executable: each answer is computed by running the handler
from the current state. -/
instance ofQueryImpl.instIsExecutable {σ : Type}
    (impl : QueryImpl spec (StateT σ ProbComp)) : (ofQueryImpl impl).IsExecutable where
  answerComp s t := impl t s
  instMeasurableSingletonClassState := inferInstance
  instMeasurableSingletonClassRange _ := inferInstance
  answerKernel_eq_evalDist _ _ := rfl

/-- A responder as a stateful query implementation in `StateT State ProbComp`: the
bundled-to-unbundled direction of the Kleisli–Mealy identification, of which
`PFunctor.Responder.equivStateHandler` is the deterministic (`Id`) sibling. -/
noncomputable def toQueryImpl (R : ProbResponder spec) [R.IsExecutable] :
    QueryImpl spec (StateT R.State ProbComp) :=
  fun t s => IsExecutable.answerComp (R := R) s t

@[simp] lemma toQueryImpl_ofQueryImpl {σ : Type}
    (impl : QueryImpl spec (StateT σ ProbComp)) : (ofQueryImpl impl).toQueryImpl = impl := rfl

@[simp] theorem answerComp_ofQueryImpl {σ : Type}
    (impl : QueryImpl spec (StateT σ ProbComp)) (s : σ) (t : spec.Domain) :
    IsExecutable.answerComp (R := ofQueryImpl impl) s t = impl t s := rfl

/-- The state set of a responder built from a stateful handler is that handler's state; a
`@[simp]` `rfl` bridge so `(ofQueryImpl impl).State` reduces to the concrete state type in
downstream goals (the responder-`State` field is otherwise opaque to `simp` and blocks `StateT`
run-map / bind rewriting). -/
@[simp] theorem ofQueryImpl_state {σ : Type} (impl : QueryImpl spec (StateT σ ProbComp)) :
    (ofQueryImpl impl).State = σ := rfl

/-- A family of memoryless randomized oracles indexed by a fixed setup value, as a
responder whose state is the setup and never changes: the per-run-sampled oracle of a
one-shot security game (sample the setup, then answer memorylessly) is exactly this
constant-state case. -/
@[reducible] noncomputable def ofHandlerFamily {Γ : Type} (h : Γ → ProbHandler spec) :
    ProbResponder spec :=
  ofQueryImpl fun t γ => (fun r => (r, γ)) <$> h γ t

/-- A memoryless randomized oracle as a (trivially) stateful responder. -/
@[reducible] noncomputable def ofHandler (H : ProbHandler spec) : ProbResponder spec :=
  ofHandlerFamily fun _ : PUnit => H

/-- A deterministic responder — PolyFun's `PFunctor.Responder`, a dynamical system over
the internal hom `spec.toPFunctor ⊸ X` — as a Dirac probabilistic responder: the answer
and successor state it commits to, with probability one. Wiring against it recovers the
upstream closed game (`OracleStrategy.stepAgainst_ofDet`). -/
@[reducible] noncomputable def ofDet {σ : Type} (C : PFunctor.Responder σ spec.toPFunctor) :
    ProbResponder spec :=
  ofQueryImpl fun t s => pure (C.answer s t, C.next s t)

end Executable

/-- Pull a responder back along an interface lens: translate each query forward through
the lens, ask the target responder, and pull its answer back through the lens, keeping
the target's state. This is the challenger side of interface wrapping — dual to
installing an adversary forward along a lens (`OracleStrategy.reduce`).

Reducible so that `(pullback w R).State` unfolds to `R.State` during unification:
statements freely mix the two spellings, and keeping them interchangeable at
reducible transparency is what lets `rw`/`simp` traverse such goals. -/
@[reducible] noncomputable def pullback {ι' : Type u} {spec' : OracleSpec.{u, u} ι'}
    (w : PFunctor.Lens spec.toPFunctor spec'.toPFunctor) (R : ProbResponder spec') :
    ProbResponder spec where
  State := R.State
  instMeasurableSpaceState := R.instMeasurableSpaceState
  instMeasurableSpaceRange := fun t =>
    MeasurableSpace.map (w.toFunB t) (R.instMeasurableSpaceRange (w.toFunA t))
  answerKernel t := by
    letI := R.instMeasurableSpaceRange (w.toFunA t)
    letI : MeasurableSpace (spec.Range t) :=
      MeasurableSpace.map (w.toFunB t) (R.instMeasurableSpaceRange (w.toFunA t))
    exact (R.answerKernel (w.toFunA t)).map fun q => (w.toFunB t q.1, q.2)
  answerKernel_isSubprobability t := by infer_instance

/-- The answer/state map used by kernel pullback is measurable for the transported
answer measurable space. -/
theorem measurable_pullback_answerMap {ι' : Type u}
    {spec' : OracleSpec.{u, u} ι'}
    (w : PFunctor.Lens spec.toPFunctor spec'.toPFunctor) (R : ProbResponder spec')
    (t : spec.Domain) :
    letI := R.instMeasurableSpaceRange (w.toFunA t)
    letI := (pullback w R).instMeasurableSpaceRange t
    Measurable fun q : spec'.Range (w.toFunA t) × R.State =>
      (w.toFunB t q.1, q.2) := by
  let _ := R.instMeasurableSpaceRange (w.toFunA t)
  let _ := (pullback w R).instMeasurableSpaceRange t
  have hw : Measurable (w.toFunB t) := by
    rw [measurable_iff_comap_le]
    exact MeasurableSpace.comap_map_le
  exact (hw.comp measurable_fst).prodMk measurable_snd

/-- The pulled-back answer σ-algebra of a query separates points whenever the target's does
and the lens translates the answers injectively: the preimage of a singleton under an
injective map is a singleton or empty. -/
theorem pullback.measurableSingletonClass_range_of_injective {ι' : Type u}
    {spec' : OracleSpec.{u, u} ι'}
    (w : PFunctor.Lens spec.toPFunctor spec'.toPFunctor) (R : ProbResponder spec')
    (t : spec.Domain) (hw : Function.Injective (w.toFunB t))
    (h : letI := R.instMeasurableSpaceRange (w.toFunA t)
      MeasurableSingletonClass (spec'.Range (w.toFunA t))) :
    letI := (pullback w R).instMeasurableSpaceRange t
    MeasurableSingletonClass (spec.Range t) := by
  let _ := R.instMeasurableSpaceRange (w.toFunA t)
  let _ := (pullback w R).instMeasurableSpaceRange t
  refine ⟨fun x => ?_⟩
  change MeasurableSet (w.toFunB t ⁻¹' {x})
  by_cases hx : x ∈ Set.range (w.toFunB t)
  · obtain ⟨y, rfl⟩ := hx
    rw [← Set.image_singleton, hw.preimage_image]
    exact measurableSet_singleton y
  · rw [Set.preimage_singleton_eq_empty.mpr hx]
    exact MeasurableSet.empty

section Executable

variable {ι : Type} {spec : OracleSpec.{0, 0} ι}

/-- Pulling an executable responder back along a lens that translates every answer
injectively keeps the answer σ-algebras point-separating, which is the side condition of
`pullback.instIsExecutable`. -/
theorem pullback.measurableSingletonClass_range_of_forall_injective {ι' : Type}
    {spec' : OracleSpec.{0, 0} ι'}
    (w : PFunctor.Lens spec.toPFunctor spec'.toPFunctor) (R : ProbResponder spec')
    [R.IsExecutable] (hw : ∀ t, Function.Injective (w.toFunB t)) : ∀ t,
    letI := (pullback w R).instMeasurableSpaceRange t
    MeasurableSingletonClass (spec.Range t) := fun t =>
  pullback.measurableSingletonClass_range_of_injective w R t (hw t)
    (IsExecutable.instMeasurableSingletonClassRange (R := R) (w.toFunA t))

/-- Executability is preserved by semantic responder pullback whose answer σ-algebras
separate points (`pullback.measurableSingletonClass_range_of_forall_injective` supplies the
side condition for lenses that translate answers injectively). The executable handler maps
the same answer/state pair as the kernel, and `evalDist_map` proves that the two readings
still agree. -/
noncomputable instance pullback.instIsExecutable {ι' : Type}
    {spec' : OracleSpec.{0, 0} ι'}
    (w : PFunctor.Lens spec.toPFunctor spec'.toPFunctor) (R : ProbResponder spec')
    [R.IsExecutable]
    [∀ t, letI := (pullback w R).instMeasurableSpaceRange t
      MeasurableSingletonClass (spec.Range t)] : (pullback w R).IsExecutable where
  answerComp s t :=
    (fun q => (w.toFunB t q.1, q.2)) <$>
      IsExecutable.answerComp (R := R) s (w.toFunA t)
  instMeasurableSingletonClassState :=
    IsExecutable.instMeasurableSingletonClassState (R := R)
  instMeasurableSingletonClassRange _ := inferInstance
  answerKernel_eq_evalDist s t := by
    let _ := R.instMeasurableSpaceRange (w.toFunA t)
    let _ := (pullback w R).instMeasurableSpaceRange t
    simp only [pullback]
    rw [Kernel.map_apply _ (measurable_pullback_answerMap w R t) s,
      IsExecutable.answerKernel_eq_evalDist,
      evalDist_map _ (measurable_pullback_answerMap w R t)]

/-- The executable pulled-back responder's handler translates each query forward and
maps the target responder's answer back through the lens. -/
@[simp] theorem toQueryImpl_pullback {ι' : Type}
    {spec' : OracleSpec.{0, 0} ι'}
    (w : PFunctor.Lens spec.toPFunctor spec'.toPFunctor) (R : ProbResponder spec')
    [R.IsExecutable]
    [∀ t, letI := (pullback w R).instMeasurableSpaceRange t
      MeasurableSingletonClass (spec.Range t)]
    (t : spec.toPFunctor.A) :
    (pullback w R).toQueryImpl t =
      (fun a => w.toFunB t a) <$> R.toQueryImpl (w.toFunA t) := by
  funext s
  change (fun q => (w.toFunB t q.1, q.2)) <$>
      IsExecutable.answerComp (R := R) s (w.toFunA t) =
    ((fun a => w.toFunB t a) <$> R.toQueryImpl (w.toFunA t)).run s
  rw [StateT.run_map]
  rfl

/-- **`FreeM.liftM` naturality for responder pullback**: interpreting a lens-translated
program through a responder's handler is interpreting the original program through the
pulled-back responder. The handler-level content of the interface-wrapping adjunction —
machine-free, so run-level wrapping laws follow from it by pure congruence. -/
theorem liftM_mapLens_pullback {ι' : Type} {spec' : OracleSpec.{0, 0} ι'}
    (w : PFunctor.Lens spec.toPFunctor spec'.toPFunctor) (R : ProbResponder spec')
    [R.IsExecutable]
    [∀ t, letI := (pullback w R).instMeasurableSpaceRange t
      MeasurableSingletonClass (spec.Range t)]
    {γ : Type} : ∀ oa : OracleComp spec γ,
    PFunctor.FreeM.liftM R.toQueryImpl (PFunctor.FreeM.mapLens w oa) =
      PFunctor.FreeM.liftM (pullback w R).toQueryImpl oa
  | .pure x => rfl
  | .liftBind t rest => by
    change (R.toQueryImpl (w.toFunA t) >>= fun d =>
        PFunctor.FreeM.liftM R.toQueryImpl (PFunctor.FreeM.mapLens w (rest (w.toFunB t d)))) =
      (pullback w R).toQueryImpl t >>= fun a =>
        PFunctor.FreeM.liftM (pullback w R).toQueryImpl (rest a)
    rw [toQueryImpl_pullback]
    simp only [bind_map_left]
    exact bind_congr fun d => liftM_mapLens_pullback w R (rest (w.toFunB t d))

end Executable

end ProbResponder

/-- The lazy random oracle as a probabilistic responder: the state is the query cache,
and each fresh query jointly draws a uniform answer and the cache extended by it. The
canonical example of a challenger whose answer and successor state must be drawn
jointly. -/
noncomputable def randomOracleResponder {ι₀ : Type} [DecidableEq ι₀]
    {spec₀ : OracleSpec.{0, 0} ι₀} [∀ t : spec₀.Domain, SampleableType (spec₀.Range t)] :
    ProbResponder spec₀ :=
  .ofQueryImpl spec₀.randomOracle

namespace OracleStrategy

open MeasureTheory ProbabilityTheory

/-! ## Wired runs

`stepAgainst` / `iterateAgainst` are the upstream eval-wired runs
`PFunctor.DynSystem.stepWith` / `iterWith` at `m := ProbComp`, driven by the responder's
stateful handler `ProbResponder.toQueryImpl`. The responder state comes first in the
product, mirroring the upstream handler-state-first convention (and the challenger-first
state of `PFunctor.DynSystem.closedGame`). Likewise, the memoryless Kleisli runs of
`VCVio.OracleComp.Coinductive.DynSystem` are the upstream stateless runs at `m := ProbComp`:
the step identification is definitional, the iterate agrees by fuel induction (the two
equation-compiler recursions do not unify definitionally at a variable fuel). Regression
guards below keep both identifications tight. -/

/-! ## Kernel-valued wired runs -/

/-- The one-round output measure obtained by wiring a strategy to a responder at a
particular joint state. The measurability of the answer-to-next-state map is explicit;
`stepAgainstKernel` additionally asks that this family of measures be measurable in
the joint input state. -/
noncomputable def stepAgainstMeasure [MeasurableSpace S]
    (A : OracleStrategy S spec) (R : ProbResponder spec)
    (_hUpdate : ∀ p : R.State × S,
      letI := R.instMeasurableSpaceRange (A.expose p.2)
      Measurable fun q : spec.Range (A.expose p.2) × R.State =>
        (q.2, A.update p.2 q.1))
    (p : R.State × S) : Measure (R.State × S) := by
  let _ := R.instMeasurableSpaceRange (A.expose p.2)
  exact (R.answerKernel (A.expose p.2) p.1).map
    (fun q => (q.2, A.update p.2 q.1))

/-- One wired round as a subprobability kernel on the responder/strategy product
state. The two hypotheses are precisely the local deterministic-update measurability
and the joint-state measurability needed to promote the pointwise construction to a
kernel. -/
noncomputable def stepAgainstKernel [MeasurableSpace S]
    (A : OracleStrategy S spec) (R : ProbResponder spec)
    (hUpdate : ∀ p : R.State × S,
      letI := R.instMeasurableSpaceRange (A.expose p.2)
      Measurable fun q : spec.Range (A.expose p.2) × R.State =>
        (q.2, A.update p.2 q.1))
    (hFamily : Measurable (stepAgainstMeasure A R hUpdate)) :
    Kernel (R.State × S) (R.State × S) :=
  ⟨stepAgainstMeasure A R hUpdate, hFamily⟩

@[simp] theorem stepAgainstKernel_apply [MeasurableSpace S]
    (A : OracleStrategy S spec) (R : ProbResponder spec)
    (hUpdate : ∀ p : R.State × S,
      letI := R.instMeasurableSpaceRange (A.expose p.2)
      Measurable fun q : spec.Range (A.expose p.2) × R.State =>
        (q.2, A.update p.2 q.1))
    (hFamily : Measurable (stepAgainstMeasure A R hUpdate))
    (p : R.State × S) :
    stepAgainstKernel A R hUpdate hFamily p = stepAgainstMeasure A R hUpdate p := rfl

instance stepAgainstKernel.instIsSubprobabilityKernel [MeasurableSpace S]
    (A : OracleStrategy S spec) (R : ProbResponder spec)
    (hUpdate : ∀ p : R.State × S,
      letI := R.instMeasurableSpaceRange (A.expose p.2)
      Measurable fun q : spec.Range (A.expose p.2) × R.State =>
        (q.2, A.update p.2 q.1))
    (hFamily : Measurable (stepAgainstMeasure A R hUpdate)) :
    IsSubprobabilityKernel (stepAgainstKernel A R hUpdate hFamily) := ⟨fun p => by
  let _ := R.instMeasurableSpaceRange (A.expose p.2)
  rw [stepAgainstKernel_apply, stepAgainstMeasure, Measure.map_apply (hUpdate p)
    MeasurableSet.univ, Set.preimage_univ]
  exact (R.answerKernel (A.expose p.2)).measure_univ_le p.1⟩

/-- The `n`-round kernel generated by `stepAgainstKernel`. Kernel powers provide the
canonical iteration/composition operation and inherit the subprobability invariant. -/
noncomputable def iterateAgainstKernel [MeasurableSpace S]
    (A : OracleStrategy S spec) (R : ProbResponder spec)
    (hUpdate : ∀ p : R.State × S,
      letI := R.instMeasurableSpaceRange (A.expose p.2)
      Measurable fun q : spec.Range (A.expose p.2) × R.State =>
        (q.2, A.update p.2 q.1))
    (hFamily : Measurable (stepAgainstMeasure A R hUpdate)) (n : ℕ) :
    Kernel (R.State × S) (R.State × S) :=
  stepAgainstKernel A R hUpdate hFamily ^ n

instance iterateAgainstKernel.instIsSubprobabilityKernel [MeasurableSpace S]
    (A : OracleStrategy S spec) (R : ProbResponder spec)
    (hUpdate : ∀ p : R.State × S,
      letI := R.instMeasurableSpaceRange (A.expose p.2)
      Measurable fun q : spec.Range (A.expose p.2) × R.State =>
        (q.2, A.update p.2 q.1))
    (hFamily : Measurable (stepAgainstMeasure A R hUpdate)) (n : ℕ) :
    IsSubprobabilityKernel (iterateAgainstKernel A R hUpdate hFamily n) := by
  unfold iterateAgainstKernel
  infer_instance

section Executable

variable {ι : Type} {spec : OracleSpec.{0, 0} ι} {S : Type}

example (H : ProbHandler spec) (A : OracleStrategy S spec) (s : S) :
    kleisliStep H A s = PFunctor.DynSystem.kleisliStep H A s := rfl

example (H : ProbHandler spec) (A : OracleStrategy S spec) (n : ℕ) (s : S) :
    kleisliIterate H A n s = PFunctor.DynSystem.kleisliIterate H A n s := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih => exact congrArg (kleisliStep H A s >>= ·) (funext ih)

/-- One wired round of an adversary strategy against a stateful responder: the
responder answers the exposed query (jointly drawing its successor state), and the
adversary advances along the answer. This is the upstream stateful-handler step
`PFunctor.DynSystem.stepWith` at `m := ProbComp`: the wiring itself is deterministic
interface data; only the states advance stochastically. -/
noncomputable def stepAgainst (A : OracleStrategy S spec) (R : ProbResponder spec)
    [R.IsExecutable] :
    R.State × S → ProbComp (R.State × S) :=
  PFunctor.DynSystem.stepWith R.toQueryImpl A

@[simp] theorem stepAgainst_apply (A : OracleStrategy S spec) (R : ProbResponder spec)
    [R.IsExecutable]
    (p : R.State × S) :
    stepAgainst A R p =
      (fun q => (q.2, A.update p.2 q.1)) <$>
        ProbResponder.IsExecutable.answerComp (R := R) p.1 (A.expose p.2) := rfl

/-- The `n`-round wired run: the Markov chain on the product state space generated by
`stepAgainst` — the upstream `PFunctor.DynSystem.iterWith` at `m := ProbComp`. -/
noncomputable def iterateAgainst (A : OracleStrategy S spec) (R : ProbResponder spec)
    [R.IsExecutable] :
    ℕ → R.State × S → ProbComp (R.State × S) :=
  PFunctor.DynSystem.iterWith R.toQueryImpl A

@[simp] theorem iterateAgainst_zero (A : OracleStrategy S spec) (R : ProbResponder spec)
    [R.IsExecutable]
    (p : R.State × S) : iterateAgainst A R 0 p = pure p := rfl

theorem iterateAgainst_succ (A : OracleStrategy S spec) (R : ProbResponder spec)
    [R.IsExecutable] (n : ℕ)
    (p : R.State × S) :
    iterateAgainst A R (n + 1) p = stepAgainst A R p >>= iterateAgainst A R n := rfl

/-- The executable one-round run denotes exactly the kernel one-round semantics. -/
theorem stepAgainstKernel_eq_evalDist [MeasurableSpace S]
    (A : OracleStrategy S spec) (R : ProbResponder spec) [R.IsExecutable]
    (hUpdate : ∀ p : R.State × S,
      letI := R.instMeasurableSpaceRange (A.expose p.2)
      Measurable fun q : spec.Range (A.expose p.2) × R.State =>
        (q.2, A.update p.2 q.1))
    (hFamily : Measurable (stepAgainstMeasure A R hUpdate))
    (p : R.State × S) :
    stepAgainstKernel A R hUpdate hFamily p = 𝒟[stepAgainst A R p] := by
  let _ := R.instMeasurableSpaceRange (A.expose p.2)
  rw [stepAgainstKernel_apply, stepAgainstMeasure, stepAgainst_apply,
    ProbResponder.IsExecutable.answerKernel_eq_evalDist, evalDist_map _ (hUpdate p)]

/-- On countable discrete state spaces, the executable `n`-round run denotes exactly
the corresponding power of the one-round kernel. -/
theorem iterateAgainstKernel_eq_evalDist [MeasurableSpace S]
    (A : OracleStrategy S spec) (R : ProbResponder spec) [R.IsExecutable]
    [Countable R.State] [DiscreteMeasurableSpace R.State]
    [Countable S] [DiscreteMeasurableSpace S]
    (hUpdate : ∀ p : R.State × S,
      letI := R.instMeasurableSpaceRange (A.expose p.2)
      Measurable fun q : spec.Range (A.expose p.2) × R.State =>
        (q.2, A.update p.2 q.1))
    (hFamily : Measurable (stepAgainstMeasure A R hUpdate))
    (n : ℕ) (p : R.State × S) :
    iterateAgainstKernel A R hUpdate hFamily n p = 𝒟[iterateAgainst A R n p] := by
  induction n generalizing p with
  | zero =>
      rw [iterateAgainstKernel, pow_zero]
      change Measure.dirac p = 𝒟[iterateAgainst A R 0 p]
      rw [iterateAgainst_zero, evalDist_pure]
  | succ n ih =>
      rw [iterateAgainstKernel, Kernel.pow_add _ n 1, pow_one, Kernel.comp_apply,
        stepAgainstKernel_eq_evalDist A R hUpdate hFamily,
        iterateAgainst_succ, evalDist_bind_of_discrete]
      apply Measure.bind_congr_right
      exact Filter.Eventually.of_forall ih

/-- The joint run over the length-`n` wired transcript and the final product state
(responder state first, matching `stepAgainst`). `QueryLog` is VCVio
vocabulary, so the transcript-recording run lives here rather than upstream. -/
noncomputable def transcriptAgainst (A : OracleStrategy S spec) (R : ProbResponder spec)
    [R.IsExecutable] :
    R.State × S → ℕ → ProbComp (QueryLog spec × (R.State × S))
  | p, 0 => pure ([], p)
  | p, n + 1 => do
      let q ← ProbResponder.IsExecutable.answerComp (R := R) p.1 (A.expose p.2)
      let rest ← transcriptAgainst A R (q.2, A.update p.2 q.1) n
      pure (⟨A.expose p.2, q.1⟩ :: rest.1, rest.2)

/-- The length-`n` wired transcripts. -/
noncomputable def transcriptDistAgainst (A : OracleStrategy S spec) (R : ProbResponder spec)
    [R.IsExecutable]
    (p : R.State × S) (n : ℕ) : ProbComp (QueryLog spec) :=
  Prod.fst <$> transcriptAgainst A R p n

/-! ## Independence of the executable realization

The wired runs read the responder through `ProbResponder.toQueryImpl`, so as programs they
depend on the chosen executable realization; as distributions they do not, because the kernel
determines every realization up to equality in distribution
(`ProbResponder.IsExecutable.answerComp_evalDistEq`). Each congruence takes the two
realizations as explicit arguments and selects them with `letI`, the instance binder of the
runs being anonymous. -/

/-- One wired round has the same distribution under every executable realization. -/
theorem stepAgainst_evalDistEq (A : OracleStrategy S spec) (R : ProbResponder spec)
    (E₁ E₂ : R.IsExecutable) (p : R.State × S) :
    (letI := E₁; stepAgainst A R p) =ᵈ (letI := E₂; stepAgainst A R p) :=
  EvalDistEq.map_congr _
    (ProbResponder.IsExecutable.answerComp_evalDistEq R E₁ E₂ p.1 (A.expose p.2))

/-- The `n`-round wired run has the same distribution under every executable realization. -/
theorem iterateAgainst_evalDistEq (A : OracleStrategy S spec) (R : ProbResponder spec)
    (E₁ E₂ : R.IsExecutable) (n : ℕ) (p : R.State × S) :
    (letI := E₁; iterateAgainst A R n p) =ᵈ (letI := E₂; iterateAgainst A R n p) := by
  induction n generalizing p with
  | zero => exact EvalDistEq.rfl
  | succ n ih =>
    rw [@iterateAgainst_succ _ _ _ A R E₁, @iterateAgainst_succ _ _ _ A R E₂]
    exact (stepAgainst_evalDistEq A R E₁ E₂ p).bind_congr ih

/-- The wired transcript run has the same distribution under every executable realization. -/
theorem transcriptAgainst_evalDistEq (A : OracleStrategy S spec) (R : ProbResponder spec)
    (E₁ E₂ : R.IsExecutable) (p : R.State × S) (n : ℕ) :
    (letI := E₁; transcriptAgainst A R p n) =ᵈ (letI := E₂; transcriptAgainst A R p n) := by
  induction n generalizing p with
  | zero => exact EvalDistEq.rfl
  | succ n ih =>
    simp only [transcriptAgainst]
    exact (ProbResponder.IsExecutable.answerComp_evalDistEq R E₁ E₂ p.1
      (A.expose p.2)).bind_congr fun q =>
        (ih (q.2, A.update p.2 q.1)).bind_congr fun _ => EvalDistEq.rfl

/-- The wired transcripts have the same distribution under every executable realization. -/
theorem transcriptDistAgainst_evalDistEq (A : OracleStrategy S spec) (R : ProbResponder spec)
    (E₁ E₂ : R.IsExecutable) (p : R.State × S) (n : ℕ) :
    (letI := E₁; transcriptDistAgainst A R p n) =ᵈ
      (letI := E₂; transcriptDistAgainst A R p n) :=
  EvalDistEq.map_congr _ (transcriptAgainst_evalDistEq A R E₁ E₂ p n)

/-! ## Deterministic recovery

Against the Dirac lift of a deterministic responder, one wired step is `pure` of the
upstream closed-game step: the state pairs agree on the nose because both put the
responder/challenger state first. -/

/-- Wiring against a deterministic responder is the (Dirac lift of the) upstream closed
game `PFunctor.DynSystem.closedGame`. -/
theorem stepAgainst_ofDet (A : OracleStrategy S spec) {σ : Type}
    (C : PFunctor.Responder σ spec.toPFunctor) (p : σ × S) :
    stepAgainst A (.ofDet C) p = pure ((PFunctor.DynSystem.closedGame C A).step p) := by
  obtain ⟨r, s⟩ := p
  simp [ProbResponder.ofDet, ProbResponder.answerComp_ofQueryImpl]

/-! ## Memoryless recovery

Against a constant-state responder the wired run is the memoryless Kleisli
run against the selected handler, with the setup carried along unchanged — the
setup-indexed family form of the upstream `PFunctor.DynSystem.stepWith_lift` /
`iterWith_lift` collapses (the family handler is state-dependent, so it is not literally
a `StateT.lift`; the same induction applies). -/

theorem stepAgainst_ofHandlerFamily {Γ : Type} (h : Γ → ProbHandler spec)
    (A : OracleStrategy S spec) (p : Γ × S) :
    stepAgainst A (ProbResponder.ofHandlerFamily h) p =
      (fun s' => (p.1, s')) <$> kleisliStep (h p.1) A p.2 := by
  rw [stepAgainst_apply, ProbResponder.answerComp_ofQueryImpl]
  simp only [ProbResponder.ofHandlerFamily, kleisliStep, Functor.map_map]

@[simp] theorem iterateAgainst_ofHandlerFamily {Γ : Type} (h : Γ → ProbHandler spec)
    (A : OracleStrategy S spec) (n : ℕ) (p : Γ × S) :
    iterateAgainst A (ProbResponder.ofHandlerFamily h) n p =
      (fun s' => (p.1, s')) <$> kleisliIterate (h p.1) A n p.2 := by
  induction n generalizing p with
  | zero =>
    simp only [iterateAgainst_zero, kleisliIterate, map_pure]
  | succ n ih =>
    calc iterateAgainst A (ProbResponder.ofHandlerFamily h) (n + 1) p
        = ((fun s' => (p.1, s')) <$> kleisliStep (h p.1) A p.2) >>=
            iterateAgainst A (ProbResponder.ofHandlerFamily h) n := by
          rw [iterateAgainst_succ, stepAgainst_ofHandlerFamily]
      _ = kleisliStep (h p.1) A p.2 >>= fun s' =>
            iterateAgainst A (ProbResponder.ofHandlerFamily h) n (p.1, s') := by
          rw [map_eq_bind_pure_comp, bind_assoc]
          exact congrArg (kleisliStep (h p.1) A p.2 >>= ·)
            (funext fun s' => by rw [Function.comp_apply, pure_bind])
      _ = kleisliStep (h p.1) A p.2 >>= fun s' =>
            (fun s'' => (p.1, s'')) <$> kleisliIterate (h p.1) A n s' :=
          congrArg (kleisliStep (h p.1) A p.2 >>= ·)
            (funext fun s' => ih (p.1, s'))
      _ = (fun s' => (p.1, s')) <$> kleisliIterate (h p.1) A (n + 1) p.2 := by
          rw [kleisliIterate]
          simp only [map_eq_bind_pure_comp, bind_assoc]

/-- Against a memoryless oracle the wired step is the memoryless Kleisli step. -/
theorem stepAgainst_ofHandler (H : ProbHandler spec) (A : OracleStrategy S spec)
    (p : PUnit × S) :
    stepAgainst A (ProbResponder.ofHandler H) p =
      (fun s' => (p.1, s')) <$> kleisliStep H A p.2 :=
  stepAgainst_ofHandlerFamily (fun _ => H) A p

/-- Against a memoryless oracle the wired run is the memoryless Kleisli run. -/
theorem iterateAgainst_ofHandler (H : ProbHandler spec) (A : OracleStrategy S spec)
    (n : ℕ) (p : PUnit × S) :
    iterateAgainst A (ProbResponder.ofHandler H) n p =
      (fun s' => (p.1, s')) <$> kleisliIterate H A n p.2 :=
  iterateAgainst_ofHandlerFamily (fun _ => H) A n p

end Executable

end OracleStrategy
