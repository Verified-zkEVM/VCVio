/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import VCVio.CryptoFoundations.Asymptotics.PolyTime
import VCVio.OracleComp.Coinductive.WiredRun

/-!
# Single-Phase Games as Dynamical Systems

A `Challenger spec α β` is the generic single-phase security experiment, presented as a
dynamical system: a hidden **`State`** carrier, a Kleisli-Mealy **`answer`** transition that
answers every adversary query while jointly advancing that state, an input sampler, and a judge
scoring the adversary's (possibly unresolved) result against the final state. The `State`/`answer`
pair bundles as the `Challenger.responder` accessor (a `ProbResponder`), with its handler as
`Challenger.oracle`. Exposing the carrier as an explicit field — rather than folding it into an
opaque responder projection — is what lets a stateful game identify its program-level advantage
with a concrete `ProbComp` experiment (`ofStateOracle` / `advantage_toProgGame_ofStateOracle`). The
two game readings below close an adversary against the responder in its two presentations:

* `Challenger.toMachineGame` — the **primary**, coalgebraic reading over bundled
  polynomial-time machine adversaries, closed against the responder by the eval-wired
  dynamical-system run `OracleMachine.wireKRun` at the adversary's round budget. This is
  the game stated in dynamical-systems vocabulary; reductions target it.
* `Challenger.toProgGame` — the algebraic reading over program families, via `simulateQ`
  through the responder's handler. The definitional home of advantage, where probability
  reasoning happens; it is *not* derivable from the machine game (an arbitrary program has
  no canonical machine bundle, and `simulateQ` is unfuelled).

The two agree on implementing adversaries (`advantage_toMachineGame_eq`), which is an
instance of the master transfer equation `MachineAdversary.exec_eq_of_implements` — the
monad-parametric `OracleMachine.Implements` is exactly what lets the transfer hold
against a *stateful* responder. Security transfers along it
(`secureAgainst_isPolyTime_of_machineGame`).

Statefulness of the oracle is the point: a memoryless `ProbHandler` cannot express a
keyed left-right encryption oracle (IND-CPA) or a decryption oracle that refuses the
challenge ciphertext (IND-CCA). Memoryless games embed via `QueryImpl.stateless`,
keeping the single-phase former strictly more general than an unstated one-shot form.
-/

open OracleComp OracleSpec Computability
open scoped MachineAdversary

universe u v

section Stateless

variable {ι : Type} [DecidableEq ι]

/-- Lift a query implementation to a stateful monad by ignoring the state: the
memoryless embedding of a plain randomized oracle into a challenger's oracle slot. -/
def QueryImpl.stateless {spec : OracleSpec ι} {m : Type → Type} [Monad m] (σ : Type)
    (H : QueryImpl spec m) : QueryImpl spec (StateT σ m) :=
  fun t => StateT.lift (H t)

omit [DecidableEq ι] in
@[simp] theorem QueryImpl.stateless_apply {spec : OracleSpec ι} {m : Type → Type}
    [Monad m] (σ : Type) (H : QueryImpl spec m) (t : spec.Domain) :
    QueryImpl.stateless σ H t = StateT.lift (H t) := rfl

omit [DecidableEq ι] in
/-- Bundling a fixed memoryless oracle as a constant-state responder
(`ProbResponder.ofHandlerFamily`) and reading back its stateful handler is exactly the
memoryless embedding `QueryImpl.stateless`: the two presentations of a stateless oracle
in a challenger's oracle slot agree. -/
@[simp] theorem ProbResponder.toQueryImpl_ofHandlerFamily_const {spec : OracleSpec ι}
    {σ : Type} (H : ProbHandler spec) :
    (ProbResponder.ofHandlerFamily fun _ : σ => H).toQueryImpl =
      QueryImpl.stateless σ H := by
  funext t s
  simp only [ProbResponder.toQueryImpl, ProbResponder.ofHandlerFamily,
    QueryImpl.stateless_apply, StateT.lift, map_eq_bind_pure_comp]
  rfl

omit [DecidableEq ι] in
/-- `simulateQ` through the memoryless embedding threads the state unchanged: running
against a stateless oracle from state `s` is the plain simulation paired with `s`. -/
@[simp] theorem OracleComp.simulateQ_stateless_run {spec : OracleSpec ι}
    {m : Type → Type} [Monad m] [LawfulMonad m] {σ β : Type}
    (H : QueryImpl spec m) (oa : OracleComp spec β) (s : σ) :
    (simulateQ (QueryImpl.stateless σ H) oa).run s
      = (fun r => (r, s)) <$> simulateQ H oa := by
  induction oa generalizing s with
  | pure x =>
    change (simulateQ (QueryImpl.stateless σ H) (pure x)).run s
      = (fun r => (r, s)) <$> simulateQ H (pure x)
    simp only [simulateQ_pure, StateT.run_pure, map_pure]
  | queryBind t k ih =>
    rw [OracleComp.simulateQ_queryBind, OracleComp.simulateQ_queryBind, map_bind,
      StateT.run_bind]
    simp only [QueryImpl.stateless_apply, StateT.run_lift, bind_assoc, pure_bind]
    exact bind_congr fun r => ih r s

end Stateless

/-! ## The single-phase challenger -/

variable {ι : ℕ → Type} [∀ n, DecidableEq (ι n)]

/-- A single-phase game challenger presented as a dynamical system, with the hidden **carrier
exposed as an explicit `State` field** (rather than folded into a `ProbResponder`, whose state
projection is opaque to `simp`/instance resolution): a state family, a Kleisli-Mealy `answer`
transition jointly drawing the successor state, an input sampler, and a judge scoring the
adversary's (possibly unresolved) result against the final state. `none` marks an adversary run
that did not resolve (machine reading); program adversaries always resolve.

The `State`/`answer` pair *is* the game's wiring data, bundled as the `Challenger.responder`
accessor: closing an adversary against it is the eval-wired dynamical system
`OracleMachine.wireKRun` (machine reading, the primary game `toMachineGame`) or `simulateQ` through
the responder's handler (program reading, `toProgGame`). Exposing the carrier is what lets stateful
games identify their program-level advantage with a concrete `ProbComp` experiment
(`ofStateOracle` / `advantage_toProgGame_ofStateOracle`). -/
structure Challenger (spec : (n : ℕ) → OracleSpec.{0, 0} (ι n)) (α β : ℕ → Type) where
  /-- The challenger's hidden state at each security parameter (its carrier, exposed). -/
  State : (n : ℕ) → Type
  /-- Answer a query from a hidden state, jointly drawing the successor state — the responder's
  Kleisli-Mealy transition in the Kleisli category of `SPMF`. -/
  answer : (n : ℕ) → State n → (t : (spec n).Domain) → SPMF ((spec n).Range t × State n)
  /-- Sample the initial hidden state together with the adversary's input. -/
  setup : (n : ℕ) → SPMF (State n × α n)
  /-- Score the adversary's (possibly unresolved) result against the final state. -/
  score : (n : ℕ) → State n → Option (β n) → SPMF Bool

namespace Challenger

variable {spec : (n : ℕ) → OracleSpec.{0, 0} (ι n)} {α β : ℕ → Type}

/-- The challenger's stateful responder: its `State`/`answer` data bundled as a `ProbResponder`.
The game's wiring data in dynamical-systems form. -/
def responder (G : Challenger spec α β) (n : ℕ) : ProbResponder (spec n) :=
  ⟨G.State n, G.answer n⟩

omit [∀ n, DecidableEq (ι n)] in
@[simp] theorem responder_State (G : Challenger spec α β) (n : ℕ) :
    (G.responder n).State = G.State n := rfl

/-- The challenger's oracle: the responder's stateful handler in `StateT (State n) SPMF`. -/
def oracle (G : Challenger spec α β) (n : ℕ) :
    QueryImpl (spec n) (StateT (G.State n) SPMF) :=
  fun t s => G.answer n s t

omit [∀ n, DecidableEq (ι n)] in
@[simp] theorem oracle_eq_toQueryImpl (G : Challenger spec α β) (n : ℕ) :
    G.oracle n = (G.responder n).toQueryImpl := rfl

/-- A memoryless challenger: a plain randomized oracle carried as a constant state (the input,
kept unchanged), an input sampler, and a score that sees the input. The old one-shot game shape. -/
noncomputable def ofProbHandler (oracle : (n : ℕ) → ProbHandler (spec n))
    (gen : (n : ℕ) → SPMF (α n)) (score : (n : ℕ) → α n → Option (β n) → SPMF Bool) :
    Challenger spec α β where
  State n := α n
  answer n x t := (fun r => (r, x)) <$> oracle n t
  setup n := (fun x => (x, x)) <$> gen n
  score := score

omit [∀ n, DecidableEq (ι n)] in
@[simp] theorem ofProbHandler_State (oracle : (n : ℕ) → ProbHandler (spec n))
    (gen : (n : ℕ) → SPMF (α n)) (score : (n : ℕ) → α n → Option (β n) → SPMF Bool) (n : ℕ) :
    (ofProbHandler oracle gen score).State n = α n := rfl

omit [∀ n, DecidableEq (ι n)] in
@[simp] theorem ofProbHandler_responder (oracle : (n : ℕ) → ProbHandler (spec n))
    (gen : (n : ℕ) → SPMF (α n)) (score : (n : ℕ) → α n → Option (β n) → SPMF Bool) (n : ℕ) :
    (ofProbHandler oracle gen score).responder n =
      ProbResponder.ofHandlerFamily (fun _ : α n => oracle n) := rfl

omit [∀ n, DecidableEq (ι n)] in
@[simp] theorem ofProbHandler_setup (oracle : (n : ℕ) → ProbHandler (spec n))
    (gen : (n : ℕ) → SPMF (α n)) (score : (n : ℕ) → α n → Option (β n) → SPMF Bool) (n : ℕ) :
    (ofProbHandler oracle gen score).setup n = (fun x => (x, x)) <$> gen n := rfl

omit [∀ n, DecidableEq (ι n)] in
@[simp] theorem ofProbHandler_score (oracle : (n : ℕ) → ProbHandler (spec n))
    (gen : (n : ℕ) → SPMF (α n)) (score : (n : ℕ) → α n → Option (β n) → SPMF Bool) :
    (ofProbHandler oracle gen score).score = score := rfl

/-! ## The algebraic reading: program families -/

/-- The game over program-family adversaries: sample state and input, interpret the
program's queries through the responder's handler, and score the result against the final
state. The definitional home of the game's advantage; it is *not* derivable from the
machine game (an arbitrary `oa` has no canonical machine bundle, and `simulateQ` is
unfuelled). -/
noncomputable def toProgGame (G : Challenger spec α β) :
    SecurityGame ((n : ℕ) → α n → OracleComp (spec n) (β n)) where
  advantage oa n :=
    (G.setup n >>= fun sx =>
      (simulateQ (G.oracle n) (oa n sx.2)).run sx.1 >>= fun rs =>
      G.score n rs.2 (some rs.1)) true

/-! ## The coalgebraic reading: machine adversaries (primary) -/

/-- **The primary game**: bundled polynomial-time machine adversaries at boundaries `bd`
closed against the challenger's responder by the eval-wired dynamical-system run
`OracleMachine.wireKRun` at the adversary's round budget. This is the game stated in
dynamical-systems vocabulary; reductions target it. -/
noncomputable def toMachineGame (G : Challenger spec α β) (bd : BoundaryData spec α β) :
    SecurityGame (MachineAdversary bd) where
  advantage D n :=
    (G.setup n >>= fun sx =>
      (D.M n).wireKRun (G.responder n) (D.steps.eval n) (sx.1, (D.M n).init sx.2) >>=
        fun rs => G.score n rs.2 rs.1) true

/-- The primary game's advantage in `MachineAdversary.exec` form: the wired run unfolds
back to the security-game execution against the responder's handler. Definitional (the
run-level bridge `MachineAdversary.exec_run_eq_wireKRun` is `rfl`). -/
theorem advantage_toMachineGame_eq_exec (G : Challenger spec α β)
    (bd : BoundaryData spec α β) (D : MachineAdversary bd) (n : ℕ) :
    (G.toMachineGame bd).advantage D n =
      (G.setup n >>= fun sx =>
        (D.exec n (G.oracle n) sx.2).run sx.1 >>= fun rs =>
        G.score n rs.2 rs.1) true := rfl

/-- **Advantage transfer**: a machine adversary implementing a program family has exactly
the program's advantage, against the responder's handler. An instance of the master
transfer equation `MachineAdversary.exec_eq_of_implements` at `m := StateT _ SPMF` —
available precisely because `OracleMachine.Implements` is monad-parametric. -/
theorem advantage_toMachineGame_eq (G : Challenger spec α β)
    {bd : BoundaryData spec α β} {D : MachineAdversary bd}
    {oa : (n : ℕ) → α n → OracleComp (spec n) (β n)}
    (h : D ⊨ oa) (n : ℕ) :
    (G.toMachineGame bd).advantage D n = G.toProgGame.advantage oa n := by
  rw [advantage_toMachineGame_eq_exec]
  refine congrArg (fun p : SPMF Bool => p true) (bind_congr fun sx => ?_)
  rw [MachineAdversary.exec_eq_of_implements h, StateT.run_map, bind_map_left]

/-- **Security transfer**: if every bundled polynomial-time machine adversary has
negligible advantage in the primary machine-level game, the program-level game is secure
against `OracleComp.IsPolyTime`. -/
theorem secureAgainst_isPolyTime_of_machineGame (G : Challenger spec α β)
    (bd : BoundaryData spec α β)
    (hsec : ∀ D : MachineAdversary bd, negligible ((G.toMachineGame bd).advantage D)) :
    G.toProgGame.secureAgainstPolyTime bd := by
  rintro oa ⟨w⟩
  have heq : G.toProgGame.advantage oa = (G.toMachineGame bd).advantage w.A :=
    funext fun n => (G.advantage_toMachineGame_eq w.implements n).symm
  exact heq ▸ hsec w.A

/-! ## Memoryless characterizations

Advantage formulas for the memoryless challenger `ofProbHandler` with the responder
plumbing discharged, so callers rewrite to a clean form instead of hand-unfolding the
structure (the σ-projection simp-blocker lesson). -/

omit [∀ n, DecidableEq (ι n)] in
/-- The program-game advantage of a memoryless challenger: sample the input, simulate the
program against the plain handler, and score. -/
@[simp] theorem advantage_toProgGame_ofProbHandler
    (oracle : (n : ℕ) → ProbHandler (spec n)) (gen : (n : ℕ) → SPMF (α n))
    (score : (n : ℕ) → α n → Option (β n) → SPMF Bool)
    (oa : (n : ℕ) → α n → OracleComp (spec n) (β n)) (n : ℕ) :
    (ofProbHandler oracle gen score).toProgGame.advantage oa n =
      (gen n >>= fun x => simulateQ (oracle n) (oa n x) >>= fun r =>
        score n x (some r)) true := by
  refine congrArg (fun p : SPMF Bool => p true) ?_
  change ((fun x => (x, x)) <$> gen n >>= fun sx =>
      (simulateQ (QueryImpl.stateless (α n) (oracle n)) (oa n sx.2)).run
        sx.1 >>= fun rs => score n rs.2 (some rs.1)) = _
  simp only [OracleComp.simulateQ_stateless_run, bind_map_left]

/-- The machine-game advantage of a memoryless challenger: sample the input, run the
machine against the plain handler at its round budget, and score. The wired run collapses
to the memoryless `OracleMachine.runK` (`wireKRun_ofHandlerFamily`). -/
@[simp] theorem advantage_toMachineGame_ofProbHandler
    (oracle : (n : ℕ) → ProbHandler (spec n)) (gen : (n : ℕ) → SPMF (α n))
    (score : (n : ℕ) → α n → Option (β n) → SPMF Bool)
    (bd : BoundaryData spec α β) (D : MachineAdversary bd) (n : ℕ) :
    ((ofProbHandler oracle gen score).toMachineGame bd).advantage D n =
      (gen n >>= fun x => (D.M n).runK (oracle n) (D.steps.eval n) ((D.M n).init x) >>=
        fun ob => score n x ob) true := by
  refine congrArg (fun p : SPMF Bool => p true) ?_
  simp only [ofProbHandler_State, ofProbHandler_responder, ofProbHandler_setup,
    ofProbHandler_score, OracleMachine.wireKRun_ofHandlerFamily]
  rw [bind_map_left]
  exact bind_congr fun x => bind_map_left _ _ _

/-! ## Stateful challengers: the `ofStateQueryImpl` former

A challenger whose oracle is a genuinely stateful `StateT σ ProbComp` handler, carried at the
explicit state `σ`. Because the carrier is exposed as the `State` field (not folded behind an
opaque responder projection), its program-game advantage identifies with a concrete `ProbComp`
experiment (`advantage_toProgGame_ofStateOracle`) — the stateful analogue of
`advantage_toProgGame_ofProbHandler`, and the connection a keyed encryption oracle or lazy random
oracle needs. -/

/-- A stateful challenger built from a `StateT σ ProbComp` oracle, a `ProbComp` state/input
sampler, and a `ProbComp` judge — read into `SPMF` by their evaluation distributions. -/
noncomputable def ofStateOracle {σ : ℕ → Type}
    (impl : (n : ℕ) → QueryImpl (spec n) (StateT (σ n) ProbComp))
    (gen : (n : ℕ) → ProbComp (σ n × α n))
    (scoreP : (n : ℕ) → σ n → Option (β n) → ProbComp Bool) : Challenger spec α β where
  State n := σ n
  answer n s t := 𝒟[(impl n t).run s]
  setup n := 𝒟[gen n]
  score n s ob := 𝒟[scoreP n s ob]

variable {σ : ℕ → Type}

omit [∀ n, DecidableEq (ι n)] in
@[simp] theorem ofStateOracle_State
    (impl : (n : ℕ) → QueryImpl (spec n) (StateT (σ n) ProbComp))
    (gen : (n : ℕ) → ProbComp (σ n × α n))
    (scoreP : (n : ℕ) → σ n → Option (β n) → ProbComp Bool) (n : ℕ) :
    (ofStateOracle impl gen scoreP).State n = σ n := rfl

omit [∀ n, DecidableEq (ι n)] in
@[simp] theorem ofStateOracle_oracle
    (impl : (n : ℕ) → QueryImpl (spec n) (StateT (σ n) ProbComp))
    (gen : (n : ℕ) → ProbComp (σ n × α n))
    (scoreP : (n : ℕ) → σ n → Option (β n) → ProbComp Bool) (n : ℕ) :
    (ofStateOracle impl gen scoreP).oracle n =
      (ProbResponder.ofStateQueryImpl (impl n)).toQueryImpl := rfl

omit [∀ n, DecidableEq (ι n)] in
@[simp] theorem ofStateOracle_setup
    (impl : (n : ℕ) → QueryImpl (spec n) (StateT (σ n) ProbComp))
    (gen : (n : ℕ) → ProbComp (σ n × α n))
    (scoreP : (n : ℕ) → σ n → Option (β n) → ProbComp Bool) (n : ℕ) :
    (ofStateOracle impl gen scoreP).setup n = 𝒟[gen n] := rfl

omit [∀ n, DecidableEq (ι n)] in
@[simp] theorem ofStateOracle_score
    (impl : (n : ℕ) → QueryImpl (spec n) (StateT (σ n) ProbComp))
    (gen : (n : ℕ) → ProbComp (σ n × α n))
    (scoreP : (n : ℕ) → σ n → Option (β n) → ProbComp Bool) (n : ℕ) (s : σ n)
    (ob : Option (β n)) :
    (ofStateOracle impl gen scoreP).score n s ob = 𝒟[scoreP n s ob] := rfl

omit [∀ n, DecidableEq (ι n)] in
/-- **The stateful challenger's program-game advantage is a concrete `ProbComp` experiment**:
sample the state and input, run the program against the stateful oracle from that state, and score
the result paired with the final state — all in `ProbComp`. The responder's `SPMF` run collapses to
the `ProbComp` run via `ProbResponder.run_simulateQ_toQueryImpl_ofStateQueryImpl`; exposing the
carrier `σ` (the `State` field) is exactly what lets the run rewriting go through. The stateful
analogue of `advantage_toProgGame_ofProbHandler`. -/
theorem advantage_toProgGame_ofStateOracle
    (impl : (n : ℕ) → QueryImpl (spec n) (StateT (σ n) ProbComp))
    (gen : (n : ℕ) → ProbComp (σ n × α n))
    (scoreP : (n : ℕ) → σ n → Option (β n) → ProbComp Bool)
    (oa : (n : ℕ) → α n → OracleComp (spec n) (β n)) (n : ℕ) :
    (ofStateOracle impl gen scoreP).toProgGame.advantage oa n =
      Pr[= true | do
        let sx ← gen n
        let rs ← (simulateQ (impl n) (oa n sx.2)).run sx.1
        scoreP n rs.2 (some rs.1)] := by
  rw [probOutput_def]
  refine congrFun (congrArg DFunLike.coe ?_) true
  change (𝒟[gen n] >>= fun sx : σ n × α n =>
      (simulateQ (ProbResponder.ofStateQueryImpl (impl n)).toQueryImpl (oa n sx.2) :
        StateT (σ n) SPMF (β n)).run sx.1 >>= fun rs => 𝒟[scoreP n rs.2 (some rs.1)]) = _
  rw [evalDist_bind]
  refine bind_congr fun sx => ?_
  rw [ProbResponder.run_simulateQ_toQueryImpl_ofStateQueryImpl (impl n) (oa n sx.2) sx.1,
    evalDist_bind]
  exact bind_congr fun rs => rfl

/-! ## Reductions from lenses: interface wrapping

A same-interface security reduction is a lens. Pulling a challenger back along an
interface lens `w` is the challenger-side dual of wrapping an adversary machine forward
along `w` (`OracleMachine.wrapIface`), and the two are adjoint: an adversary playing the
pulled-back game equals the *wrapped* adversary playing the original game
(`advantage_toMachineGame_pullbackIface`, the game-level image of
`OracleMachine.wireKRun_wrapIface`). This is the game-facing combinator behind the §3.5
PRF⇒CPA workhorse; the polynomial-time closure of the wrapped adversary
(`MachineAdversary.wrapIface` / `IsPolyTime.wrapIface`, an honest base-machine witness
for the answer-translation transducer) is the remaining frontier, and genuinely
non-lens reductions (translating one query into an oracle *computation*, e.g. encrypting
under a PRF key) route through the challenger-side `ProbResponder.simulate` rather than a
single lens. -/

variable {ι' : ℕ → Type} {spec' : (n : ℕ) → OracleSpec.{0, 0} (ι' n)}

/-- Pull a challenger's game back along an interface lens family `w : spec ⇆ spec'`: the
challenger now speaks `spec`, answering each `spec`-query by translating it forward
through `w`, consulting the original `spec'`-responder, and mapping the answer back
(`ProbResponder.pullback`). Its hidden state, input sampler, and score are unchanged —
`pullback` preserves the responder's state set. The challenger-side dual of
`OracleMachine.wrapIface`. -/
noncomputable def pullbackIface
    (w : (n : ℕ) → PFunctor.Lens (spec n).toPFunctor (spec' n).toPFunctor)
    (G : Challenger spec' α β) : Challenger spec α β where
  State n := G.State n
  answer n := ((G.responder n).pullback (w n)).answer
  setup := G.setup
  score := G.score

omit [∀ n, DecidableEq (ι n)] in
@[simp] theorem pullbackIface_responder
    (w : (n : ℕ) → PFunctor.Lens (spec n).toPFunctor (spec' n).toPFunctor)
    (G : Challenger spec' α β) (n : ℕ) :
    (pullbackIface w G).responder n = (G.responder n).pullback (w n) := rfl

/-- **The game-level interface-wrapping adjunction**: an adversary machine playing the
pulled-back game `G.pullbackIface w` has exactly the advantage of the *wrapped* adversary
machine `(D.M n).wrapIface (w n)` playing the original game `G`. The game-level image of
`OracleMachine.wireKRun_wrapIface`: wrapping the adversary forward along `w` is pulling
the challenger back along `w`. -/
theorem advantage_toMachineGame_pullbackIface
    (w : (n : ℕ) → PFunctor.Lens (spec n).toPFunctor (spec' n).toPFunctor)
    (G : Challenger spec' α β) (bd : BoundaryData spec α β) (D : MachineAdversary bd)
    (n : ℕ) :
    ((G.pullbackIface w).toMachineGame bd).advantage D n =
      (G.setup n >>= fun sx =>
        ((D.M n).wrapIface (w n)).wireKRun (G.responder n) (D.steps.eval n)
          (sx.1, (D.M n).init sx.2) >>= fun rs => G.score n rs.2 rs.1) true := by
  refine congrArg (fun p : SPMF Bool => p true) (bind_congr fun sx => ?_)
  rw [OracleMachine.wireKRun_wrapIface]
  rfl

end Challenger
