/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import VCVio.CryptoFoundations.Asymptotics.Game.Challenger

/-!
# Two-Phase Games as Stateful Kleisli Challengers

A `Challenger₂` is the commit-then-guess experiment shape: the challenger samples a
phase-one state and input, answers the adversary's first phase through a stateful
oracle, turns the phase-one result into a phase-two state and input (the *challenge*
step — where a hidden bit typically enters), answers the second phase through a
possibly different stateful oracle, and scores against the final state. This is the
Kleisli-weighted reading of a lens into the composite `ph₁ ◁ ph₂` (Spivak–Niu
Example 6.40, `PFunctor.Lens.CompTriple`): `setup`/`challenge`/`score` are the
three components with SPMF-valued policies, and the per-phase hidden state is what a
memoryless oracle field could not carry across queries.

Hidden-bit indistinguishability experiments such as `PrivK^eav` take `σ₂ := Bool × …`
(the challenge bit lives in the phase-two state, correlated with the phase-two input
but invisible to the adversary); a keyed encryption oracle keeps the key in both phase
states.

Both adversary presentations are supported, as in `Challenger`: program-family pairs
via `toProgGame`, machine pairs via `toMachineGame`, connected per phase by the master
transfer equation (`advantage_toMachineGame_eq`) and the security transfer
`secureAgainst_isPolyTimePair_of_machineGame` at the pair predicate
`OracleComp.IsPolyTimePair`. An adversary's own cross-phase state is not a parameter of
the former; instantiators fold it into the phase-one output and phase-two input types.
-/

open OracleComp OracleSpec Computability
open scoped MachineAdversary

variable {ι : Type} [DecidableEq ι]

/-! ## Polynomial time for adversary pairs -/

/-- The polynomial-time predicate for a pair of program families, the `isPPT` slot for
two-phase games: both phases are Turing-machine-grounded polynomial time, each at its
own pinned boundaries. -/
def OracleComp.IsPolyTimePair {spec : ℕ → OracleSpec.{0, 0} ι} {α₁ β₁ α₂ β₂ : ℕ → Type}
    (bd₁ : BoundaryData spec α₁ β₁) (bd₂ : BoundaryData spec α₂ β₂)
    (oa : ((n : ℕ) → α₁ n → OracleComp (spec n) (β₁ n)) ×
      ((n : ℕ) → α₂ n → OracleComp (spec n) (β₂ n))) : Prop :=
  OracleComp.IsPolyTime bd₁ oa.1 ∧ OracleComp.IsPolyTime bd₂ oa.2

/-! ## The two-phase challenger -/

/-- A two-phase game challenger: per-phase hidden states `σ₁`/`σ₂` and stateful
oracles, with the challenge step consuming the phase-one final state and the
phase-one result to produce the phase-two state and input. The Kleisli image of a
`CompTriple`: `(setup, challenge, score)` decorated with per-phase oracle policies. -/
structure Challenger₂ (spec : ℕ → OracleSpec.{0, 0} ι) (α₁ β₁ α₂ β₂ : ℕ → Type) where
  /-- The challenger's hidden phase-one state. -/
  σ₁ : ℕ → Type
  /-- The challenger's hidden phase-two state. -/
  σ₂ : ℕ → Type
  /-- Sample the initial state together with the phase-one input. -/
  setup : (n : ℕ) → SPMF (σ₁ n × α₁ n)
  /-- The phase-one oracle. -/
  oracle₁ : (n : ℕ) → QueryImpl (spec n) (StateT (σ₁ n) SPMF)
  /-- The challenger: consume the phase-one final state and result (`none` = the run
  did not resolve) and produce the phase-two state and input. -/
  challenge : (n : ℕ) → σ₁ n → Option (β₁ n) → SPMF (σ₂ n × α₂ n)
  /-- The phase-two oracle. -/
  oracle₂ : (n : ℕ) → QueryImpl (spec n) (StateT (σ₂ n) SPMF)
  /-- Score the phase-two result against the final challenger state. -/
  score : (n : ℕ) → σ₂ n → Option (β₂ n) → SPMF Bool

namespace Challenger₂

variable {spec : ℕ → OracleSpec.{0, 0} ι} {α₁ β₁ α₂ β₂ : ℕ → Type}

/-- The game over pairs of program families, via `simulateQ` through each phase's
stateful oracle. -/
noncomputable def toProgGame (G : Challenger₂ spec α₁ β₁ α₂ β₂) :
    SecurityGame (((n : ℕ) → α₁ n → OracleComp (spec n) (β₁ n)) ×
      ((n : ℕ) → α₂ n → OracleComp (spec n) (β₂ n))) where
  advantage oa n :=
    (G.setup n >>= fun sx =>
      (some <$> simulateQ (G.oracle₁ n) (oa.1 n sx.2)).run sx.1 >>= fun rs₁ =>
      G.challenge n rs₁.2 rs₁.1 >>= fun sy =>
      (some <$> simulateQ (G.oracle₂ n) (oa.2 n sy.2)).run sy.1 >>= fun rs₂ =>
      G.score n rs₂.2 rs₂.1) true

/-- The game over pairs of bundled polynomial-time machine adversaries, via the machine
runs `MachineAdversary.exec` at the per-phase stateful oracles. -/
noncomputable def toMachineGame (G : Challenger₂ spec α₁ β₁ α₂ β₂)
    (bd₁ : BoundaryData spec α₁ β₁) (bd₂ : BoundaryData spec α₂ β₂) :
    SecurityGame (MachineAdversary bd₁ × MachineAdversary bd₂) where
  advantage D n :=
    (G.setup n >>= fun sx =>
      (D.1.exec n (G.oracle₁ n) sx.2).run sx.1 >>= fun rs₁ =>
      G.challenge n rs₁.2 rs₁.1 >>= fun sy =>
      (D.2.exec n (G.oracle₂ n) sy.2).run sy.1 >>= fun rs₂ =>
      G.score n rs₂.2 rs₂.1) true

/-! ## Memoryless challengers -/

section ofMemoryless

variable {γ : ℕ → Type}

/-- A memoryless two-phase challenger: a plain randomized oracle shared by both phases,
an input sampler, a challenge step reading the (retained) phase-one input, and hidden
challenge data `γ` carried as the phase-two state. The commit-then-guess shape of
hidden-bit experiments whose oracle needs no memory. -/
noncomputable def ofMemoryless (oracle : (n : ℕ) → ProbHandler (spec n))
    (gen : (n : ℕ) → SPMF (α₁ n))
    (challenge : (n : ℕ) → α₁ n → Option (β₁ n) → SPMF (γ n × α₂ n))
    (score : (n : ℕ) → γ n → Option (β₂ n) → SPMF Bool) :
    Challenger₂ spec α₁ β₁ α₂ β₂ where
  σ₁ := α₁
  σ₂ := γ
  setup n := (fun x => (x, x)) <$> gen n
  oracle₁ n := QueryImpl.stateless (α₁ n) (oracle n)
  challenge := challenge
  oracle₂ n := QueryImpl.stateless (γ n) (oracle n)
  score := score

/-- The program-level advantage of a memoryless two-phase challenger, with the state
threading stripped: sample, simulate phase one, challenge, simulate phase two, score.
The reusable characterization instantiations rewrite with, so they never manipulate the
`StateT` plumbing themselves. -/
theorem advantage_toProgGame_ofMemoryless (oracle : (n : ℕ) → ProbHandler (spec n))
    (gen : (n : ℕ) → SPMF (α₁ n))
    (challenge : (n : ℕ) → α₁ n → Option (β₁ n) → SPMF (γ n × α₂ n))
    (score : (n : ℕ) → γ n → Option (β₂ n) → SPMF Bool)
    (oa : ((n : ℕ) → α₁ n → OracleComp (spec n) (β₁ n)) ×
      ((n : ℕ) → α₂ n → OracleComp (spec n) (β₂ n))) (n : ℕ) :
    (ofMemoryless oracle gen challenge score).toProgGame.advantage oa n =
      (gen n >>= fun x =>
        (some <$> simulateQ (oracle n) (oa.1 n x)) >>= fun r₁ =>
        challenge n x r₁ >>= fun gy =>
        (some <$> simulateQ (oracle n) (oa.2 n gy.2)) >>= fun r₂ =>
        score n gy.1 r₂) true := by
  refine congrArg (fun p : SPMF Bool => p true) ?_
  show ((fun x => (x, x)) <$> gen n >>= fun sx =>
      (some <$> simulateQ (QueryImpl.stateless (α₁ n) (oracle n)) (oa.1 n sx.2)).run
        sx.1 >>= fun rs₁ =>
      challenge n rs₁.2 rs₁.1 >>= fun sy =>
      (some <$> simulateQ (QueryImpl.stateless (γ n) (oracle n)) (oa.2 n sy.2)).run
        sy.1 >>= fun rs₂ =>
      score n rs₂.2 rs₂.1) = _
  simp only [map_eq_bind_pure_comp, StateT.run_bind, OracleComp.simulateQ_stateless_run,
    StateT.run_pure, bind_assoc, pure_bind, Function.comp]

end ofMemoryless

/-- **Advantage transfer**: machines implementing the two phases have exactly the
advantage of the implemented program pair — the master transfer equation
`MachineAdversary.exec_eq_of_implements` applied once per phase, each at its own
`StateT` instance. -/
theorem advantage_toMachineGame_eq (G : Challenger₂ spec α₁ β₁ α₂ β₂)
    {bd₁ : BoundaryData spec α₁ β₁} {bd₂ : BoundaryData spec α₂ β₂}
    {D₁ : MachineAdversary bd₁} {D₂ : MachineAdversary bd₂}
    {oa₁ : (n : ℕ) → α₁ n → OracleComp (spec n) (β₁ n)}
    {oa₂ : (n : ℕ) → α₂ n → OracleComp (spec n) (β₂ n)}
    (h₁ : D₁ ⊨ oa₁) (h₂ : D₂ ⊨ oa₂) (n : ℕ) :
    (G.toMachineGame bd₁ bd₂).advantage (D₁, D₂) n
      = G.toProgGame.advantage (oa₁, oa₂) n := by
  refine congrArg (fun p : SPMF Bool => p true) (bind_congr fun sx => ?_)
  rw [MachineAdversary.exec_eq_of_implements h₁]
  refine bind_congr fun rs₁ => bind_congr fun sy => ?_
  rw [MachineAdversary.exec_eq_of_implements h₂]

/-- **Security transfer**: if every pair of bundled polynomial-time machine adversaries
has negligible machine-level advantage, the program-level game is secure against
`OracleComp.IsPolyTimePair`. -/
theorem secureAgainst_isPolyTimePair_of_machineGame (G : Challenger₂ spec α₁ β₁ α₂ β₂)
    (bd₁ : BoundaryData spec α₁ β₁) (bd₂ : BoundaryData spec α₂ β₂)
    (hsec : ∀ (D₁ : MachineAdversary bd₁) (D₂ : MachineAdversary bd₂),
      negligible ((G.toMachineGame bd₁ bd₂).advantage (D₁, D₂))) :
    G.toProgGame.secureAgainst (OracleComp.IsPolyTimePair bd₁ bd₂) := by
  rintro ⟨oa₁, oa₂⟩ ⟨⟨w₁⟩, ⟨w₂⟩⟩
  have heq : G.toProgGame.advantage (oa₁, oa₂)
      = (G.toMachineGame bd₁ bd₂).advantage (w₁.A, w₂.A) :=
    funext fun n => (G.advantage_toMachineGame_eq w₁.implements w₂.implements n).symm
  exact heq ▸ hsec w₁.A w₂.A

end Challenger₂
