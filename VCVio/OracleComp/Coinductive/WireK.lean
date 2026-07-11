/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import VCVio.OracleComp.Coinductive.DynSystem
import VCVio.OracleComp.QueryTracking.RandomOracle.Basic
import PolyFun.PFunctor.Dynamical.Game

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
construction: `wireKStep` / `wireKIterate` are PolyFun's generic eval-wired runs
`PFunctor.DynSystem.stepWith` / `iterWith` instantiated at `m := SPMF`, driven by the
responder's stateful handler. The responder state comes first in the product state,
matching the upstream handler-state-first convention and the challenger-first state of
`PFunctor.DynSystem.closedGame`; a deterministic responder (`ProbResponder.ofDet`) wires
to `pure` of the closed-game step (`wireKStep_ofDet`). `wireKTranscript` additionally
records the exchanged queries and answers — `QueryLog` is VCVio vocabulary, so the
transcript form lives here rather than upstream.

Memoryless oracles embed as responders with trivial (`ProbResponder.ofHandler`) or
constant (`ProbResponder.ofHandlerFamily`) state, and the wired run then collapses to
the existing memoryless runs `OracleStrategy.kleisliStep` / `kleisliIterate`
(`wireKStep_ofHandler` and companions) — the setup-indexed family form of the upstream
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
`eval : [p, y] ⊗ p → y`: `wireKStep` keeps that wiring as deterministic combinatorial
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
def ofQueryImpl {σ : Type u} (impl : QueryImpl spec (StateT σ SPMF)) :
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
noncomputable def ofHandlerFamily {Γ : Type u} (h : Γ → ProbHandler spec) :
    ProbResponder spec where
  State := Γ
  answer γ t := (fun r => (r, γ)) <$> h γ t

/-- A memoryless randomized oracle as a (trivially) stateful responder. -/
noncomputable def ofHandler (H : ProbHandler spec) : ProbResponder spec :=
  ofHandlerFamily fun _ : PUnit => H

/-- A deterministic responder — PolyFun's `PFunctor.Responder`, a dynamical system over
the internal hom `spec.toPFunctor ⊸ X` — as a Dirac probabilistic responder: the answer
and successor state it commits to, with probability one. Wiring against it recovers the
upstream closed game (`OracleStrategy.wireKStep_ofDet`). -/
noncomputable def ofDet {σ : Type u} (C : PFunctor.Responder σ spec.toPFunctor) :
    ProbResponder spec where
  State := σ
  answer s t := pure (C.answer s t, C.next s t)

/-- Pull a responder back along an interface lens: translate each query forward through
the lens, ask the target responder, and pull its answer back through the lens, keeping
the target's state. This is the challenger side of interface wrapping — dual to
installing an adversary forward along a lens (`OracleStrategy.reduce`). -/
noncomputable def pullback {ι' : Type u} {spec' : OracleSpec.{u, u} ι'}
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

/-- Lift a stateful `ProbComp` query implementation to a probabilistic responder via
its evaluation distribution, pointwise in the state. This is the bridge along which
existing stateful challengers (the lazy random oracle, cached LR encryption oracles)
become responders. -/
noncomputable def ofStateQueryImpl {ι₀ : Type} {spec₀ : OracleSpec.{0, 0} ι₀}
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
simulateQ (𝒟 ∘ impl)`. It is proved here by a bespoke `OracleComp` induction for want of a
generic *naturality of the universal fold along a monad morphism* law: `simulateQ'` is
already a bundled `OracleComp spec →ᵐ r`, but there is no `φ ∘ₘ simulateQ' impl =
simulateQ' (φ ∘ impl)`, nor a `StateT`-functoriality lemma for `→ᵐ`, so this and its
siblings (`evalDist_simulateQ_run'_eq_evalDist`, `evalDist_simulateQ_run_congr`) are each
re-derived by hand. See the PolyFun Kleisli/handler pain-point ledger. -/
theorem run_simulateQ_toQueryImpl_ofStateQueryImpl {ι₀ : Type}
    {spec₀ : OracleSpec.{0, 0} ι₀} {σ α : Type}
    (impl : QueryImpl spec₀ (StateT σ ProbComp)) (oa : OracleComp spec₀ α) (s : σ) :
    (simulateQ (ofStateQueryImpl impl).toQueryImpl oa).run s =
      𝒟[(simulateQ impl oa).run s] := by
  induction oa generalizing s with
  | pure x =>
    show (simulateQ (ofStateQueryImpl impl).toQueryImpl (pure x)).run s =
      𝒟[(simulateQ impl (pure x)).run s]
    rw [simulateQ_pure, simulateQ_pure, StateT.run_pure, StateT.run_pure, evalDist_pure]
    rfl
  | queryBind t k ih =>
    have hqb : ∀ {r : Type → Type} [Monad r] [LawfulMonad r] (impl' : QueryImpl spec₀ r),
        simulateQ impl' (OracleComp.queryBind t k) =
          impl' t >>= fun u => simulateQ impl' (k u) := by
      intro r _ _ impl'
      rw [show OracleComp.queryBind t k =
        (liftM (spec₀.query t) : OracleComp spec₀ (spec₀.Range t)) >>= k from rfl,
        simulateQ_bind, simulateQ_spec_query]
    rw [hqb, hqb, StateT.run_bind, StateT.run_bind, evalDist_bind]
    exact bind_congr fun p => ih p.1 p.2

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

`wireKStep` / `wireKIterate` are the upstream eval-wired runs
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
noncomputable def wireKStep (A : OracleStrategy S spec) (R : ProbResponder spec) :
    R.State × S → SPMF (R.State × S) :=
  PFunctor.DynSystem.stepWith R.toQueryImpl A

@[simp] theorem wireKStep_apply (A : OracleStrategy S spec) (R : ProbResponder spec)
    (p : R.State × S) :
    wireKStep A R p =
      (fun q => (q.2, A.update p.2 q.1)) <$> R.answer p.1 (A.expose p.2) := rfl

/-- The `n`-round wired run: the Markov chain on the product state space generated by
`wireKStep` — the upstream `PFunctor.DynSystem.iterWith` at `m := SPMF`. -/
noncomputable def wireKIterate (A : OracleStrategy S spec) (R : ProbResponder spec) :
    ℕ → R.State × S → SPMF (R.State × S) :=
  PFunctor.DynSystem.iterWith R.toQueryImpl A

@[simp] theorem wireKIterate_zero (A : OracleStrategy S spec) (R : ProbResponder spec)
    (p : R.State × S) : wireKIterate A R 0 p = pure p := rfl

theorem wireKIterate_succ (A : OracleStrategy S spec) (R : ProbResponder spec) (n : ℕ)
    (p : R.State × S) :
    wireKIterate A R (n + 1) p = wireKStep A R p >>= wireKIterate A R n := rfl

/-- The joint subdistribution over the length-`n` wired transcript and the final
product state (responder state first, matching `wireKStep`). `QueryLog` is VCVio
vocabulary, so the transcript-recording run lives here rather than upstream. -/
noncomputable def wireKTranscript (A : OracleStrategy S spec) (R : ProbResponder spec) :
    R.State × S → ℕ → SPMF (QueryLog spec × (R.State × S))
  | p, 0 => pure ([], p)
  | p, n + 1 => do
      let q ← R.answer p.1 (A.expose p.2)
      let rest ← wireKTranscript A R (q.2, A.update p.2 q.1) n
      pure (⟨A.expose p.2, q.1⟩ :: rest.1, rest.2)

/-- The subdistribution over length-`n` wired transcripts. -/
noncomputable def wireKTranscriptDist (A : OracleStrategy S spec) (R : ProbResponder spec)
    (p : R.State × S) (n : ℕ) : SPMF (QueryLog spec) :=
  Prod.fst <$> wireKTranscript A R p n

/-! ## Deterministic recovery

Against the Dirac lift of a deterministic responder, one wired step is `pure` of the
upstream closed-game step: the state pairs agree on the nose because both put the
responder/challenger state first. -/

/-- Wiring against a deterministic responder is the (Dirac lift of the) upstream closed
game `PFunctor.DynSystem.closedGame`. -/
@[simp] theorem wireKStep_ofDet (A : OracleStrategy S spec) {σ : Type u}
    (C : PFunctor.Responder σ spec.toPFunctor) (p : σ × S) :
    wireKStep A (.ofDet C) p = pure ((PFunctor.DynSystem.closedGame C A).step p) := by
  obtain ⟨r, s⟩ := p
  simp [ProbResponder.ofDet]

/-! ## Memoryless recovery

Against a constant-state responder the wired run is the existing memoryless Kleisli
run against the selected handler, with the setup carried along unchanged — the
setup-indexed family form of the upstream `PFunctor.DynSystem.stepWith_lift` /
`iterWith_lift` collapses (the family handler is state-dependent, so it is not literally
a `StateT.lift`; the same induction applies). -/

@[simp] theorem wireKStep_ofHandlerFamily {Γ : Type u} (h : Γ → ProbHandler spec)
    (A : OracleStrategy S spec) (p : Γ × S) :
    wireKStep A (ProbResponder.ofHandlerFamily h) p =
      (fun s' => (p.1, s')) <$> kleisliStep (h p.1) A p.2 := by
  simp only [wireKStep_apply, ProbResponder.ofHandlerFamily, kleisliStep, Functor.map_map]
  rfl

@[simp] theorem wireKIterate_ofHandlerFamily {Γ : Type u} (h : Γ → ProbHandler spec)
    (A : OracleStrategy S spec) (n : ℕ) (p : Γ × S) :
    wireKIterate A (ProbResponder.ofHandlerFamily h) n p =
      (fun s' => (p.1, s')) <$> kleisliIterate (h p.1) A n p.2 := by
  induction n generalizing p with
  | zero =>
    simp only [wireKIterate_zero, kleisliIterate, map_pure]
    rfl
  | succ n ih =>
    calc wireKIterate A (ProbResponder.ofHandlerFamily h) (n + 1) p
        = ((fun s' => (p.1, s')) <$> kleisliStep (h p.1) A p.2) >>=
            wireKIterate A (ProbResponder.ofHandlerFamily h) n := by
          rw [wireKIterate_succ, wireKStep_ofHandlerFamily]
          rfl
      _ = kleisliStep (h p.1) A p.2 >>= fun s' =>
            wireKIterate A (ProbResponder.ofHandlerFamily h) n (p.1, s') := by
          rw [map_eq_bind_pure_comp, bind_assoc]
          exact congrArg (kleisliStep (h p.1) A p.2 >>= ·)
            (funext fun s' => by rw [Function.comp_apply, pure_bind]; rfl)
      _ = kleisliStep (h p.1) A p.2 >>= fun s' =>
            (fun s'' => (p.1, s'')) <$> kleisliIterate (h p.1) A n s' :=
          congrArg (kleisliStep (h p.1) A p.2 >>= ·)
            (funext fun s' => ih (p.1, s'))
      _ = (fun s' => (p.1, s')) <$> kleisliIterate (h p.1) A (n + 1) p.2 := by
          rw [kleisliIterate]
          simp only [map_eq_bind_pure_comp, bind_assoc]

/-- Against a memoryless oracle the wired step is the memoryless Kleisli step. -/
@[simp] theorem wireKStep_ofHandler (H : ProbHandler spec) (A : OracleStrategy S spec)
    (p : PUnit × S) :
    wireKStep A (ProbResponder.ofHandler H) p =
      (fun s' => (p.1, s')) <$> kleisliStep H A p.2 :=
  wireKStep_ofHandlerFamily (fun _ => H) A p

/-- Against a memoryless oracle the wired run is the memoryless Kleisli run. -/
@[simp] theorem wireKIterate_ofHandler (H : ProbHandler spec) (A : OracleStrategy S spec)
    (n : ℕ) (p : PUnit × S) :
    wireKIterate A (ProbResponder.ofHandler H) n p =
      (fun s' => (p.1, s')) <$> kleisliIterate H A n p.2 :=
  wireKIterate_ofHandlerFamily (fun _ => H) A n p

end OracleStrategy
