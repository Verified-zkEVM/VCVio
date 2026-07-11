/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import VCVio.OracleComp.Coinductive.DynSystem
import VCVio.OracleComp.QueryTracking.RandomOracle.Basic

/-!
# Probabilistic Wiring: Adversary Strategies Against Stateful Responders

`ProbResponder spec` is the challenger side of an interactive game presented as a
coalgebra: a state set together with, for each query, a *joint* subdistribution over
the answer and the next state — a Mealy machine in the Kleisli category of `SPMF`.
Wiring one against an adversary `OracleStrategy` closes the query interface and yields
a Markov chain on the product state space (`wireKStep`, `wireKIterate`);
`wireKTranscript` additionally records the exchanged queries and answers.

Memoryless oracles embed as responders with trivial (`ProbResponder.ofHandler`) or
constant (`ProbResponder.ofHandlerFamily`) state, and the wired run then collapses to
the existing memoryless runs `OracleStrategy.kleisliStep` / `kleisliIterate`
(`wireKStep_ofHandler` and companions). The per-run-sampled oracle of a one-shot
security game is exactly the constant-state case. Genuinely stateful challengers enter
through `ProbResponder.ofQueryImpl` (from a `QueryImpl` into `StateT σ SPMF`) or
`ProbResponder.ofStateQueryImpl` (from a `QueryImpl` into `StateT σ ProbComp`, via its
evaluation distribution): the lazy random oracle (`randomOracleResponder`) is the
motivating instance, and cached LR encryption oracles fit the same constructor at the
`CryptoFoundations` layer. The joint answer/state draw is essential for these — the
cache entry a random oracle stores must be the very answer it returned.

## Categorical view (Spivak–Niu)

A *deterministic* responder is a dynamical system over the internal hom `[p, y]` of
Spivak–Niu §4.5 (for `p` the interface polynomial `spec.toPFunctor`): its positions
are the sections of the interface — exactly `OracleHandler spec` — and closing an
adversary against it is wiring along the evaluation map `eval : [p, y] ⊗ p → y`.
`wireKStep` keeps that wiring as deterministic combinatorial data and lets the
*states* advance in the Kleisli category of the commutative monad `SPMF`: one
synchronized step of the tensor system with the evaluation wiring applied.
`ProbResponder` is strictly more general than a Kleisli lift of an `[p, y]`-system,
because the answer and the next state are drawn jointly rather than the state first
determining a handler. The UC layer's `processSemanticsOracle` is the heavyweight
sibling of this construction (multi-party, scheduler-driven); this file is the minimal
two-party core, and neither is derived from the other.

Wired runs of machine adversaries (an `OracleMachine.runK` against a responder rather
than a memoryless handler) are a deliberate follow-on, driven by the random-oracle-model
use case.
-/

universe u v

open OracleSpec

variable {ι : Type u} {spec : OracleSpec.{u, u} ι}

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

/-- A responder as a stateful query implementation in `StateT State SPMF`. -/
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

/-- Lift a stateful `ProbComp` query implementation to a probabilistic responder via
its evaluation distribution, pointwise in the state. This is the bridge along which
existing stateful challengers (the lazy random oracle, cached LR encryption oracles)
become responders. -/
noncomputable def ofStateQueryImpl {ι₀ : Type} {spec₀ : OracleSpec.{0, 0} ι₀}
    {σ : Type} (impl : QueryImpl spec₀ (StateT σ ProbComp)) : ProbResponder spec₀ where
  State := σ
  answer s t := 𝒟[(impl t).run s]

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

/-! ## Wired runs -/

/-- One wired round of an adversary strategy against a stateful responder: the
responder answers the exposed query (jointly drawing its successor state), and the
adversary advances along the answer. The wiring itself is deterministic interface
data; only the states advance stochastically. -/
noncomputable def wireKStep (A : OracleStrategy spec) (R : ProbResponder spec)
    (p : A.State × R.State) : SPMF (A.State × R.State) :=
  (fun q => (A.update p.1 q.1, q.2)) <$> R.answer p.2 (A.expose p.1)

/-- The `n`-round wired run: the Markov chain on the product state space generated by
`wireKStep`. -/
noncomputable def wireKIterate (A : OracleStrategy spec) (R : ProbResponder spec) :
    ℕ → A.State × R.State → SPMF (A.State × R.State)
  | 0, p => pure p
  | n + 1, p => wireKStep A R p >>= wireKIterate A R n

/-- The joint subdistribution over the length-`n` wired transcript and the final
product state. -/
noncomputable def wireKTranscript (A : OracleStrategy spec) (R : ProbResponder spec) :
    A.State × R.State → ℕ → SPMF (QueryLog spec × (A.State × R.State))
  | p, 0 => pure ([], p)
  | p, n + 1 => do
      let q ← R.answer p.2 (A.expose p.1)
      let rest ← wireKTranscript A R (A.update p.1 q.1, q.2) n
      pure (⟨A.expose p.1, q.1⟩ :: rest.1, rest.2)

/-- The subdistribution over length-`n` wired transcripts. -/
noncomputable def wireKTranscriptDist (A : OracleStrategy spec) (R : ProbResponder spec)
    (p : A.State × R.State) (n : ℕ) : SPMF (QueryLog spec) :=
  Prod.fst <$> wireKTranscript A R p n

/-! ## Memoryless recovery

Against a constant-state responder the wired run is the existing memoryless Kleisli
run against the selected handler, with the setup carried along unchanged. -/

@[simp] theorem wireKStep_ofHandlerFamily {Γ : Type u} (h : Γ → ProbHandler spec)
    (A : OracleStrategy spec) (p : A.State × Γ) :
    wireKStep A (ProbResponder.ofHandlerFamily h) p =
      (fun s' => (s', p.2)) <$> kleisliStep (h p.2) A p.1 := by
  simp only [wireKStep, ProbResponder.ofHandlerFamily, kleisliStep, Functor.map_map]
  rfl

@[simp] theorem wireKIterate_ofHandlerFamily {Γ : Type u} (h : Γ → ProbHandler spec)
    (A : OracleStrategy spec) (n : ℕ) (p : A.State × Γ) :
    wireKIterate A (ProbResponder.ofHandlerFamily h) n p =
      (fun s' => (s', p.2)) <$> kleisliIterate (h p.2) A n p.1 := by
  induction n generalizing p with
  | zero =>
    simp only [wireKIterate, kleisliIterate, map_pure]
    rfl
  | succ n ih =>
    calc wireKIterate A (ProbResponder.ofHandlerFamily h) (n + 1) p
        = ((fun s' => (s', p.2)) <$> kleisliStep (h p.2) A p.1) >>=
            wireKIterate A (ProbResponder.ofHandlerFamily h) n := by
          rw [wireKIterate, wireKStep_ofHandlerFamily]
          rfl
      _ = kleisliStep (h p.2) A p.1 >>= fun s' =>
            wireKIterate A (ProbResponder.ofHandlerFamily h) n (s', p.2) := by
          rw [map_eq_bind_pure_comp, bind_assoc]
          exact congrArg (kleisliStep (h p.2) A p.1 >>= ·)
            (funext fun s' => by rw [Function.comp_apply, pure_bind]; rfl)
      _ = kleisliStep (h p.2) A p.1 >>= fun s' =>
            (fun s'' => (s'', p.2)) <$> kleisliIterate (h p.2) A n s' :=
          congrArg (kleisliStep (h p.2) A p.1 >>= ·)
            (funext fun s' => ih (s', p.2))
      _ = (fun s' => (s', p.2)) <$> kleisliIterate (h p.2) A (n + 1) p.1 := by
          rw [kleisliIterate]
          simp only [map_eq_bind_pure_comp, bind_assoc]

/-- Against a memoryless oracle the wired step is the memoryless Kleisli step. -/
@[simp] theorem wireKStep_ofHandler (H : ProbHandler spec) (A : OracleStrategy spec)
    (p : A.State × PUnit) :
    wireKStep A (ProbResponder.ofHandler H) p =
      (fun s' => (s', p.2)) <$> kleisliStep H A p.1 :=
  wireKStep_ofHandlerFamily (fun _ => H) A p

/-- Against a memoryless oracle the wired run is the memoryless Kleisli run. -/
@[simp] theorem wireKIterate_ofHandler (H : ProbHandler spec) (A : OracleStrategy spec)
    (n : ℕ) (p : A.State × PUnit) :
    wireKIterate A (ProbResponder.ofHandler H) n p =
      (fun s' => (s', p.2)) <$> kleisliIterate H A n p.1 :=
  wireKIterate_ofHandlerFamily (fun _ => H) A n p

end OracleStrategy
