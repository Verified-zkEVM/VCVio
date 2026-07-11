/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import VCVio.CryptoFoundations.Asymptotics.PolyTime

/-!
# Single-Phase Games as Stateful Kleisli Challengers

A `Challenger spec α β` is the generic single-phase security experiment: a challenger
with hidden per-parameter state that samples an input for the adversary, answers every
adversary query through a *stateful* oracle in `StateT (State n) SPMF`, and scores the
adversary's (possibly unresolved) result against its final state. Categorically the
oracle is a Kleisli coalgebra over the spec's polynomial — the SPMF-with-state instance
of a PolyFun handler — and the two game readings below wire the adversary against it in
its two presentations:

* `Challenger.toProgGame` — the **algebraic** reading over program families, via
  `simulateQ` into `StateT (State n) SPMF`. This is the definitional home of advantage,
  where probability reasoning happens.
* `Challenger.toMachineGame` — the **coalgebraic** reading over bundled polynomial-time
  machine adversaries, via the machine run `MachineAdversary.exec` at
  `m := StateT (State n) SPMF`.

The two agree on implementing adversaries (`advantage_toMachineGame_eq`), which is an
instance of the master transfer equation `MachineAdversary.exec_eq_of_implements` — the
monad-parametric `OracleMachine.Implements` is exactly what lets the transfer hold
against a *stateful* oracle. Security transfers along it
(`secureAgainst_isPolyTime_of_machineGame`).

Statefulness of the oracle is the point: a memoryless `ProbHandler` cannot express a
keyed left-right encryption oracle (IND-CPA) or a decryption oracle that refuses the
challenge ciphertext (IND-CCA). Memoryless games embed via `QueryImpl.stateless`,
keeping the single-phase former strictly more general than an unstated one-shot form.
-/

open OracleComp OracleSpec Computability
open scoped MachineAdversary

universe u v

variable {ι : Type} [DecidableEq ι]

/-- Lift a query implementation to a stateful monad by ignoring the state: the
memoryless embedding of a plain randomized oracle into a challenger's oracle slot. -/
def QueryImpl.stateless {spec : OracleSpec ι} {m : Type → Type} [Monad m] (σ : Type)
    (H : QueryImpl spec m) : QueryImpl spec (StateT σ m) :=
  fun t => StateT.lift (H t)

@[simp] theorem QueryImpl.stateless_apply {spec : OracleSpec ι} {m : Type → Type}
    [Monad m] (σ : Type) (H : QueryImpl spec m) (t : spec.Domain) :
    QueryImpl.stateless σ H t = StateT.lift (H t) := rfl

/-- `simulateQ` through the memoryless embedding threads the state unchanged: running
against a stateless oracle from state `s` is the plain simulation paired with `s`. -/
@[simp] theorem OracleComp.simulateQ_stateless_run {spec : OracleSpec ι}
    {m : Type → Type} [Monad m] [LawfulMonad m] {σ β : Type}
    (H : QueryImpl spec m) (oa : OracleComp spec β) (s : σ) :
    (simulateQ (QueryImpl.stateless σ H) oa).run s
      = (fun r => (r, s)) <$> simulateQ H oa := by
  induction oa generalizing s with
  | pure x =>
    show (simulateQ (QueryImpl.stateless σ H) (pure x)).run s
      = (fun r => (r, s)) <$> simulateQ H (pure x)
    simp only [simulateQ_pure, StateT.run_pure, map_pure]
  | queryBind t k ih =>
    show (simulateQ (QueryImpl.stateless σ H) (OracleComp.queryBind t k)).run s
      = (fun r => (r, s)) <$> simulateQ H (OracleComp.queryBind t k)
    rw [OracleComp.simulateQ_queryBind, OracleComp.simulateQ_queryBind, map_bind,
      StateT.run_bind]
    simp only [QueryImpl.stateless_apply, StateT.run_lift, bind_assoc, pure_bind]
    exact bind_congr fun r => ih r s

/-! ## The single-phase challenger -/

/-- A single-phase game challenger: hidden state, an input sampler, a *stateful* oracle
answering every adversary query, and a judge scoring the adversary's result against the
final challenger state. `none` marks an adversary run that did not resolve (machine
reading); program adversaries always resolve. -/
structure Challenger (spec : ℕ → OracleSpec.{0, 0} ι) (α β : ℕ → Type) where
  /-- The challenger's hidden state at each security parameter. -/
  State : ℕ → Type
  /-- Sample the initial challenger state together with the adversary's input. -/
  setup : (n : ℕ) → SPMF (State n × α n)
  /-- The challenger's oracle: answer each query monadically, reading and updating the
  hidden state. -/
  oracle : (n : ℕ) → QueryImpl (spec n) (StateT (State n) SPMF)
  /-- Score the adversary's (possibly unresolved) result against the final state. -/
  score : (n : ℕ) → State n → Option (β n) → SPMF Bool

namespace Challenger

variable {spec : ℕ → OracleSpec.{0, 0} ι} {α β : ℕ → Type}

/-- A memoryless challenger: a plain randomized oracle, an input sampler, and a score
that sees the input (kept as the trivial state). The old one-shot game shape. -/
noncomputable def ofProbHandler (oracle : (n : ℕ) → ProbHandler (spec n))
    (gen : (n : ℕ) → SPMF (α n)) (score : (n : ℕ) → α n → Option (β n) → SPMF Bool) :
    Challenger spec α β where
  State := α
  setup n := (fun x => (x, x)) <$> gen n
  oracle n := QueryImpl.stateless (α n) (oracle n)
  score := score

/-! ## The algebraic reading: program families -/

/-- The game over program-family adversaries: sample state and input, interpret the
program's queries through the stateful oracle, and score the result against the final
state. The definitional home of the game's advantage. -/
noncomputable def toProgGame (G : Challenger spec α β) :
    SecurityGame ((n : ℕ) → α n → OracleComp (spec n) (β n)) where
  advantage oa n :=
    (G.setup n >>= fun sx =>
      (some <$> simulateQ (G.oracle n) (oa n sx.2)).run sx.1 >>= fun rs =>
      G.score n rs.2 rs.1) true

/-! ## The coalgebraic reading: machine adversaries -/

/-- The game over bundled polynomial-time machine adversaries at boundaries `bd`: the
machine run `MachineAdversary.exec` against the stateful oracle, at
`m := StateT (G.State n) SPMF`. -/
noncomputable def toMachineGame (G : Challenger spec α β) (bd : BoundaryData spec α β) :
    SecurityGame (MachineAdversary bd) where
  advantage D n :=
    (G.setup n >>= fun sx =>
      (D.exec n (G.oracle n) sx.2).run sx.1 >>= fun rs =>
      G.score n rs.2 rs.1) true

/-- **Advantage transfer**: a machine adversary implementing a program family has
exactly the program's advantage, against the stateful oracle. An instance of the master
transfer equation `MachineAdversary.exec_eq_of_implements` at `m := StateT _ SPMF` —
available precisely because `OracleMachine.Implements` is monad-parametric. -/
theorem advantage_toMachineGame_eq (G : Challenger spec α β)
    {bd : BoundaryData spec α β} {D : MachineAdversary bd}
    {oa : (n : ℕ) → α n → OracleComp (spec n) (β n)}
    (h : D ⊨ oa) (n : ℕ) :
    (G.toMachineGame bd).advantage D n = G.toProgGame.advantage oa n := by
  refine congrArg (fun p : SPMF Bool => p true) (bind_congr fun sx => ?_)
  rw [MachineAdversary.exec_eq_of_implements h]

/-- **Security transfer**: if every bundled polynomial-time machine adversary has
negligible advantage in the machine-level game, the program-level game is secure
against `OracleComp.IsPolyTime`. -/
theorem secureAgainst_isPolyTime_of_machineGame (G : Challenger spec α β)
    (bd : BoundaryData spec α β)
    (hsec : ∀ D : MachineAdversary bd, negligible ((G.toMachineGame bd).advantage D)) :
    G.toProgGame.secureAgainstPolyTime bd := by
  rintro oa ⟨w⟩
  have heq : G.toProgGame.advantage oa = (G.toMachineGame bd).advantage w.A :=
    funext fun n => (G.advantage_toMachineGame_eq w.implements n).symm
  exact heq ▸ hsec w.A

end Challenger
