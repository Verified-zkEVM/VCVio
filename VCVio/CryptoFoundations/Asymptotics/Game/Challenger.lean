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
dynamical system: a stateful probabilistic **responder** (`ProbResponder`) that samples
an input for the adversary, answers every adversary query while advancing its hidden
state, and scores the adversary's (possibly unresolved) result against its final state.
The responder *is* the game's wiring data; the folded-away `State`/`oracle` fields survive
as the `Challenger.State` / `Challenger.oracle` accessors (the responder's state set and
its `StateT (State n) SPMF` handler). The two game readings below close an adversary
against the responder in its two presentations:

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

/-- A single-phase game challenger presented as a dynamical system: a stateful
probabilistic **responder** answering every adversary query (its state set is the
challenger's hidden state), an input sampler, and a judge scoring the adversary's result
against the final responder state. `none` marks an adversary run that did not resolve
(machine reading); program adversaries always resolve.

The `responder` field *is* the game's wiring data: closing an adversary against it is the
eval-wired dynamical system `OracleMachine.wireKRun` (machine reading, the primary game
`toMachineGame`) or `simulateQ` through the responder's handler (program reading,
`toProgGame`). The folded-away `State`/`oracle` fields survive as the `Challenger.State`
/ `Challenger.oracle` accessors. -/
structure Challenger (spec : (n : ℕ) → OracleSpec.{0, 0} (ι n)) (α β : ℕ → Type) where
  /-- The challenger's stateful responder at each security parameter: for each query, a
  joint subdistribution over the answer and the successor hidden state. -/
  responder : (n : ℕ) → ProbResponder (spec n)
  /-- Sample the initial hidden (responder) state together with the adversary's input. -/
  setup : (n : ℕ) → SPMF ((responder n).State × α n)
  /-- Score the adversary's (possibly unresolved) result against the final state. -/
  score : (n : ℕ) → (responder n).State → Option (β n) → SPMF Bool

namespace Challenger

variable {spec : (n : ℕ) → OracleSpec.{0, 0} (ι n)} {α β : ℕ → Type}

/-- The challenger's hidden state at security parameter `n`: the responder's state.
A compatibility accessor for the folded-away `State` field. -/
abbrev State (G : Challenger spec α β) (n : ℕ) : Type := (G.responder n).State

/-- The challenger's oracle: the responder's stateful handler in `StateT (State n) SPMF`.
A compatibility accessor for the folded-away `oracle` field. -/
abbrev oracle (G : Challenger spec α β) (n : ℕ) :
    QueryImpl (spec n) (StateT (G.State n) SPMF) :=
  (G.responder n).toQueryImpl

/-- A memoryless challenger: a plain randomized oracle bundled as a constant-state
responder, an input sampler, and a score that sees the input (kept as the trivial state).
The old one-shot game shape. -/
noncomputable def ofProbHandler (oracle : (n : ℕ) → ProbHandler (spec n))
    (gen : (n : ℕ) → SPMF (α n)) (score : (n : ℕ) → α n → Option (β n) → SPMF Bool) :
    Challenger spec α β where
  responder n := ProbResponder.ofHandlerFamily fun _ : α n => oracle n
  setup n := (fun x => (x, x)) <$> gen n
  score := score

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
      (some <$> simulateQ (G.oracle n) (oa n sx.2)).run sx.1 >>= fun rs =>
      G.score n rs.2 rs.1) true

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
  rw [MachineAdversary.exec_eq_of_implements h]

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
      (some <$> simulateQ (QueryImpl.stateless (α n) (oracle n)) (oa n sx.2)).run
        sx.1 >>= fun rs => score n rs.2 rs.1) = _
  simp only [map_eq_bind_pure_comp, StateT.run_bind, OracleComp.simulateQ_stateless_run,
    StateT.run_pure, bind_assoc, pure_bind, Function.comp]

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
  simp only [ofProbHandler, OracleMachine.wireKRun_ofHandlerFamily]
  rw [bind_map_left]
  exact bind_congr fun x => bind_map_left _ _ _

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
  responder n := (G.responder n).pullback (w n)
  setup := G.setup
  score := G.score

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
