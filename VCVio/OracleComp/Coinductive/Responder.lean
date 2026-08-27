/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module
public import VCVio.OracleComp.Coinductive.DynSystem
public import VCVio.OracleComp.QueryTracking.RandomOracle.Basic
public import PolyFun.PFunctor.Dynamical.Game

/-!
# Probabilistic Wiring: Adversary Strategies Against Stateful Responders

`ProbResponder spec` is the challenger side of an interactive game presented as a
coalgebra: a state set together with, for each query, a *joint* subdistribution over
the answer and the next state — a Mealy machine in the Kleisli category of `SPMF`.
Unbundled, it is exactly a stateful handler `QueryImpl spec (StateT State SPMF)`
(`ProbResponder.toQueryImpl` / `ofQueryImpl` are definitional inverses): the bundled
probabilistic sibling of PolyFun's deterministic Kleisli–Mealy bridge
`PFunctor.Responder.equivStateHandler`.

Wiring a responder against an adversary `OracleStrategy` is not a hand-rolled
construction: `stepAgainst` / `iterateAgainst` are PolyFun's generic eval-wired runs
`PFunctor.DynSystem.stepWith` / `iterWith` instantiated at `m := SPMF`, driven by the
responder's stateful handler. The responder state comes first in the product state,
matching the upstream handler-state-first convention and the challenger-first state of
`PFunctor.DynSystem.closedGame`; a deterministic responder (`ProbResponder.ofDet`) wires
to `pure` of the closed-game step (`stepAgainst_ofDet`). `transcriptAgainst` additionally
records the exchanged queries and answers — `QueryLog` is VCVio vocabulary, so the
transcript form lives here rather than upstream.

Memoryless oracles embed as responders with trivial (`ProbResponder.ofHandler`) or
constant (`ProbResponder.ofHandlerFamily`) state, and the wired run then collapses to
the existing memoryless runs `OracleStrategy.kleisliStep` / `kleisliIterate`
(`stepAgainst_ofHandler` and companions) — the setup-indexed family form of the upstream
stateless collapses `PFunctor.DynSystem.stepWith_lift` / `iterWith_lift`. The
per-run-sampled oracle of a one-shot security game is exactly the constant-state case.
Genuinely stateful challengers enter through `ProbResponder.ofQueryImpl` (from a
`QueryImpl` into `StateT σ SPMF`) or `ProbResponder.ofStateQueryImpl` (from a
`QueryImpl` into `StateT σ ProbComp`, via its evaluation distribution): the lazy random
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
data and lets the *states* advance in the Kleisli category of the commutative monad
`SPMF` — one synchronized step of the tensor system with the evaluation wiring applied,
which is precisely the upstream `stepWith`. `ProbResponder` is strictly more general
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
a Mealy coalgebra in the Kleisli category of `SPMF`. From a state, each query yields a
joint subdistribution over the answer and the successor state. The joint draw matters:
a lazy random oracle's stored cache entry must be the very answer it returned, which no
answer-then-state factorization expresses. -/
structure ProbResponder {ι : Type u} (spec : OracleSpec.{u, u} ι) where
  /-- The responder's internal state (the challenger's memory). -/
  State : Type u
  /-- Answer a query from a state, jointly drawing the successor state. -/
  answer : State → (t : spec.Domain) → SPMF (spec.Range t × State)

namespace ProbResponder

/-- A responder as a stateful query implementation in `StateT State SPMF`: the
bundled-to-unbundled direction of the Kleisli–Mealy identification, of which
`PFunctor.Responder.equivStateHandler` is the deterministic (`Id`) sibling. -/
def toQueryImpl (R : ProbResponder spec) : QueryImpl spec (StateT R.State SPMF) :=
  fun t s => R.answer s t

/-- A stateful query implementation as a responder; inverse to `toQueryImpl`. -/
@[reducible] def ofQueryImpl {σ : Type u} (impl : QueryImpl spec (StateT σ SPMF)) :
    ProbResponder spec where
  State := σ
  answer s t := impl t s

@[simp] lemma toQueryImpl_ofQueryImpl {σ : Type u}
    (impl : QueryImpl spec (StateT σ SPMF)) : (ofQueryImpl impl).toQueryImpl = impl :=
  rfl

@[simp] lemma ofQueryImpl_toQueryImpl (R : ProbResponder spec) :
    ofQueryImpl R.toQueryImpl = R :=
  rfl

/-- A family of memoryless randomized oracles indexed by a fixed setup value, as a
responder whose state is the setup and never changes: the per-run-sampled oracle of a
one-shot security game (sample the setup, then answer memorylessly) is exactly this
constant-state case. -/
@[reducible] noncomputable def ofHandlerFamily {Γ : Type u} (h : Γ → ProbHandler spec) :
    ProbResponder spec where
  State := Γ
  answer γ t := (fun r => (r, γ)) <$> h γ t

/-- A memoryless randomized oracle as a (trivially) stateful responder. -/
@[reducible] noncomputable def ofHandler (H : ProbHandler spec) : ProbResponder spec :=
  ofHandlerFamily fun _ : PUnit => H

/-- A deterministic responder — PolyFun's `PFunctor.Responder`, a dynamical system over
the internal hom `spec.toPFunctor ⊸ X` — as a Dirac probabilistic responder: the answer
and successor state it commits to, with probability one. Wiring against it recovers the
upstream closed game (`OracleStrategy.stepAgainst_ofDet`). -/
@[reducible] noncomputable def ofDet {σ : Type u} (C : PFunctor.Responder σ spec.toPFunctor) :
    ProbResponder spec where
  State := σ
  answer s t := pure (C.answer s t, C.next s t)

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
  answer s t := (fun q => (w.toFunB t q.1, q.2)) <$> R.answer s (w.toFunA t)

/-- The pulled-back responder's handler translates each query forward and maps the
target responder's answer back through the lens: `toQueryImpl` of `pullback w R` is the
answer-post-composition of `R.toQueryImpl` along `w`. The handler-level form of the
interface-wrapping adjunction. -/
@[simp] theorem toQueryImpl_pullback {ι' : Type u} {spec' : OracleSpec.{u, u} ι'}
    (w : PFunctor.Lens spec.toPFunctor spec'.toPFunctor) (R : ProbResponder spec')
    (t : spec.toPFunctor.A) :
    (pullback w R).toQueryImpl t =
      (fun a => w.toFunB t a) <$> R.toQueryImpl (w.toFunA t) := by
  funext s
  rfl

/-- **`FreeM.liftM` naturality for responder pullback**: interpreting a lens-translated
program through a responder's handler is interpreting the original program through the
pulled-back responder. The handler-level content of the interface-wrapping adjunction —
machine-free, so run-level wrapping laws follow from it by pure congruence. -/
theorem liftM_mapLens_pullback {ι' : Type u} {spec' : OracleSpec.{u, u} ι'}
    (w : PFunctor.Lens spec.toPFunctor spec'.toPFunctor) (R : ProbResponder spec')
    {γ : Type u} : ∀ oa : OracleComp spec γ,
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

/-- Lift a stateful `ProbComp` query implementation to a probabilistic responder via
its evaluation distribution, pointwise in the state. This is the bridge along which
existing stateful challengers (the lazy random oracle, cached LR encryption oracles)
become responders. -/
@[reducible] noncomputable def ofStateQueryImpl {ι₀ : Type} {spec₀ : OracleSpec.{0, 0} ι₀}
    {σ : Type} (impl : QueryImpl spec₀ (StateT σ ProbComp)) : ProbResponder spec₀ where
  State := σ
  answer s t := 𝒟[(impl t).run s]

/-- **The stateful-responder probability bridge**: running an adversary against the
responder built from a `StateT σ ProbComp` handler (`ofStateQueryImpl impl`) is exactly
the evaluation distribution of running it against `impl` itself — the responder's `SPMF`
program-run is `𝒟` of the `ProbComp` program-run, *jointly* in the returned value and the
final state. This is the reusable bridge every stateful-responder consumer needs to move a
game between its `ProbComp` presentation (where probability reasoning happens) and its
`ProbResponder` presentation (the dynamical-systems wiring data).

Structurally it is the naturality of `simulateQ` along the monad morphism
`𝒟 : ProbComp →ᵐ SPMF`, transported through `StateT σ` — i.e. `𝒟 ∘ simulateQ impl =
simulateQ (𝒟 ∘ impl)`. That is exactly `PFunctor.FreeM.run_liftM_mapHom` at the bundled
evaluation-distribution morphism: `simulateQ` is the universal fold
(`simulateQ_def`), `ofStateQueryImpl` post-composes each query with `𝒟` pointwise in the
state, and `StateT.mapHom` is that post-composition as a morphism, so the whole statement
is one instance of the generic law rather than an induction over `OracleComp`. -/
theorem run_simulateQ_toQueryImpl_ofStateQueryImpl {ι₀ : Type}
    {spec₀ : OracleSpec.{0, 0} ι₀} {σ α : Type}
    (impl : QueryImpl spec₀ (StateT σ ProbComp)) (oa : OracleComp spec₀ α) (s : σ) :
    (simulateQ (ofStateQueryImpl impl).toQueryImpl oa).run s =
      𝒟[(simulateQ impl oa).run s] := by
  -- `exact` rather than a term-mode `:=`: matching the generic law needs the unfoldings of
  -- `simulateQ`, `toQueryImpl`, `ofStateQueryImpl`, `StateT.mapHom`, and `𝒟`, which are
  -- definitional but not syntactic.
  exact PFunctor.FreeM.run_liftM_mapHom (MonadHom.ofLift ProbComp SPMF) impl oa s

/-- The state set of a responder built from a stateful `ProbComp` handler is that handler's
state; a `@[simp]` `rfl` bridge so `(ofStateQueryImpl impl).State` reduces to the concrete state
type in downstream goals (the responder-`State` abbrev is otherwise opaque to `simp` and blocks
`StateT` run-map / bind rewriting). -/
@[simp] theorem ofStateQueryImpl_state {ι₀ : Type} {spec₀ : OracleSpec.{0, 0} ι₀} {σ : Type}
    (impl : QueryImpl spec₀ (StateT σ ProbComp)) : (ofStateQueryImpl impl).State = σ := rfl

/-- The post-composed form of `run_simulateQ_toQueryImpl_ofStateQueryImpl`: mapping the returned
value by `f` before running commutes with the bridge, pairing `f` on the value component. The
form security games hit, where the adversary's result is wrapped in `some` before the judge sees
it. -/
theorem run_map_simulateQ_toQueryImpl_ofStateQueryImpl {ι₀ : Type}
    {spec₀ : OracleSpec.{0, 0} ι₀} {σ α γ : Type}
    (impl : QueryImpl spec₀ (StateT σ ProbComp)) (f : α → γ) (oa : OracleComp spec₀ α) (s : σ) :
    (f <$> simulateQ (ofStateQueryImpl impl).toQueryImpl oa).run s =
      (fun p => (f p.1, p.2)) <$> 𝒟[(simulateQ impl oa).run s] := by
  rw [StateT.run_map, run_simulateQ_toQueryImpl_ofStateQueryImpl]

end ProbResponder

/-- The lazy random oracle as a probabilistic responder: the state is the query cache,
and each fresh query jointly draws a uniform answer and the cache extended by it. The
canonical example of a challenger whose answer and successor state must be drawn
jointly. -/
noncomputable def randomOracleResponder {ι₀ : Type} [DecidableEq ι₀]
    {spec₀ : OracleSpec.{0, 0} ι₀} [∀ t : spec₀.Domain, SampleableType (spec₀.Range t)] :
    ProbResponder spec₀ :=
  .ofStateQueryImpl spec₀.randomOracle

namespace OracleStrategy

/-! ## Wired runs

`stepAgainst` / `iterateAgainst` are the upstream eval-wired runs
`PFunctor.DynSystem.stepWith` / `iterWith` at `m := SPMF`, driven by the responder's
stateful handler `ProbResponder.toQueryImpl`. The responder state comes first in the
product, mirroring the upstream handler-state-first convention (and the challenger-first
state of `PFunctor.DynSystem.closedGame`). Likewise, the memoryless Kleisli runs of
`VCVio.OracleComp.Coinductive.DynSystem` are the upstream stateless runs at `m := SPMF`:
the step identification is definitional, the iterate agrees by fuel induction (the two
equation-compiler recursions do not unify definitionally at a variable fuel). Regression
guards below keep both identifications tight. -/

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
`PFunctor.DynSystem.stepWith` at `m := SPMF`: the wiring itself is deterministic
interface data; only the states advance stochastically. -/
noncomputable def stepAgainst (A : OracleStrategy S spec) (R : ProbResponder spec) :=
  PFunctor.DynSystem.stepWith R.toQueryImpl A

@[simp] theorem stepAgainst_apply (A : OracleStrategy S spec) (R : ProbResponder spec)
    (p : R.State × S) :
    stepAgainst A R p =
      (fun q => (q.2, A.update p.2 q.1)) <$> R.answer p.1 (A.expose p.2) := rfl

/-- The `n`-round wired run: the Markov chain on the product state space generated by
`stepAgainst` — the upstream `PFunctor.DynSystem.iterWith` at `m := SPMF`. -/
noncomputable def iterateAgainst (A : OracleStrategy S spec) (R : ProbResponder spec) :
    ℕ → R.State × S → SPMF (R.State × S) :=
  PFunctor.DynSystem.iterWith R.toQueryImpl A

@[simp] theorem iterateAgainst_zero (A : OracleStrategy S spec) (R : ProbResponder spec)
    (p : R.State × S) : iterateAgainst A R 0 p = pure p := rfl

theorem iterateAgainst_succ (A : OracleStrategy S spec) (R : ProbResponder spec) (n : ℕ)
    (p : R.State × S) :
    iterateAgainst A R (n + 1) p = stepAgainst A R p >>= iterateAgainst A R n := rfl

/-- The joint subdistribution over the length-`n` wired transcript and the final
product state (responder state first, matching `stepAgainst`). `QueryLog` is VCVio
vocabulary, so the transcript-recording run lives here rather than upstream. -/
noncomputable def transcriptAgainst (A : OracleStrategy S spec) (R : ProbResponder spec) :
    R.State × S → ℕ → SPMF (QueryLog spec × (R.State × S))
  | p, 0 => pure ([], p)
  | p, n + 1 => do
      let q ← R.answer p.1 (A.expose p.2)
      let rest ← transcriptAgainst A R (q.2, A.update p.2 q.1) n
      pure (⟨A.expose p.2, q.1⟩ :: rest.1, rest.2)

/-- The subdistribution over length-`n` wired transcripts. -/
noncomputable def transcriptDistAgainst (A : OracleStrategy S spec) (R : ProbResponder spec)
    (p : R.State × S) (n : ℕ) : SPMF (QueryLog spec) :=
  Prod.fst <$> transcriptAgainst A R p n

/-! ## Deterministic recovery

Against the Dirac lift of a deterministic responder, one wired step is `pure` of the
upstream closed-game step: the state pairs agree on the nose because both put the
responder/challenger state first. -/

/-- Wiring against a deterministic responder is the (Dirac lift of the) upstream closed
game `PFunctor.DynSystem.closedGame`. -/
@[simp] theorem stepAgainst_ofDet (A : OracleStrategy S spec) {σ : Type u}
    (C : PFunctor.Responder σ spec.toPFunctor) (p : σ × S) :
    stepAgainst A (.ofDet C) p = pure ((PFunctor.DynSystem.closedGame C A).step p) := by
  obtain ⟨r, s⟩ := p
  simp [ProbResponder.ofDet]

/-! ## Memoryless recovery

Against a constant-state responder the wired run is the existing memoryless Kleisli
run against the selected handler, with the setup carried along unchanged — the
setup-indexed family form of the upstream `PFunctor.DynSystem.stepWith_lift` /
`iterWith_lift` collapses (the family handler is state-dependent, so it is not literally
a `StateT.lift`; the same induction applies). -/

@[simp] theorem stepAgainst_ofHandlerFamily {Γ : Type u} (h : Γ → ProbHandler spec)
    (A : OracleStrategy S spec) (p : Γ × S) :
    stepAgainst A (ProbResponder.ofHandlerFamily h) p =
      (fun s' => (p.1, s')) <$> kleisliStep (h p.1) A p.2 := by
  simp only [stepAgainst_apply, ProbResponder.ofHandlerFamily, kleisliStep, Functor.map_map]

@[simp] theorem iterateAgainst_ofHandlerFamily {Γ : Type u} (h : Γ → ProbHandler spec)
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
@[simp] theorem stepAgainst_ofHandler (H : ProbHandler spec) (A : OracleStrategy S spec)
    (p : PUnit × S) :
    stepAgainst A (ProbResponder.ofHandler H) p =
      (fun s' => (p.1, s')) <$> kleisliStep H A p.2 :=
  stepAgainst_ofHandlerFamily (fun _ => H) A p

/-- Against a memoryless oracle the wired run is the memoryless Kleisli run. -/
@[simp] theorem iterateAgainst_ofHandler (H : ProbHandler spec) (A : OracleStrategy S spec)
    (n : ℕ) (p : PUnit × S) :
    iterateAgainst A (ProbResponder.ofHandler H) n p =
      (fun s' => (p.1, s')) <$> kleisliIterate H A n p.2 :=
  iterateAgainst_ofHandlerFamily (fun _ => H) A n p

end OracleStrategy
