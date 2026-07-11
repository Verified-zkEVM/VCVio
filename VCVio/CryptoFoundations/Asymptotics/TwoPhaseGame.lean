/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import VCVio.CryptoFoundations.Asymptotics.PolyTime

/-!
# Two-Phase Security Games with Hidden Challenger State

This file generalizes `OneShotGame` to challenge-style experiments that a single-phase
game cannot express: a `TwoPhaseGame` runs the adversary twice, with a challenger step
in between that consumes the first-phase result and produces both a *hidden* state and
the second-phase input. The score may depend on the hidden state — exactly what
hidden-bit indistinguishability experiments such as `PrivK^eav` require, where the
challenge bit is correlated with the adversary's second-phase input but must be
invisible to it.

As with `OneShotGame`, both adversary presentations are supported: program families via
`toProgGame` and bundled polynomial-time machines via `toPolyGame`, connected by
`advantage_toPolyGame_eq` (two applications of the master transfer equation
`PolyTimeAdversary.exec_eq_of_implements`, one per phase) and the security transfer
`secureAgainst_isPolyTimePair_of_polyGame`. The `isPPT` notion for a pair of program
families is `OracleComp.IsPolyTimePair`: both phases are `OracleComp.IsPolyTime`. An
adversary's own cross-phase state is not a parameter of the game former; instantiators
fold it into the phase-one output and phase-two input types.

Game values are computed against `OracleSpec.probHandler` (the canonical randomized
oracle of a probability spec, defined with the coinductive run layer in
`VCVio.OracleComp.Coinductive.DynSystem`), whose `simulateQ_probHandler` identifies
machine-level game values with `Pr[…]` statements about the program.
-/


open OracleSpec OracleComp Computability

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

/-! ## Two-phase games over both adversary presentations -/

/-- A two-phase game with hidden challenger state: sample a phase-one input, run the
adversary's first phase, let the challenger turn the result into hidden state `γ` plus
a phase-two input, run the second phase, and score against the hidden state.
Generalizes `OneShotGame` in exactly the two ways challenge experiments need: the score
may depend on challenger state correlated with the phase-two input (e.g. a hidden bit),
and the adversary acts twice. -/
structure TwoPhaseGame (spec : ℕ → OracleSpec.{0, 0} ι) (α₁ β₁ γ α₂ β₂ : ℕ → Type) where
  /-- The game's oracle implementation at each security parameter. -/
  oracle : (n : ℕ) → ProbHandler (spec n)
  /-- The phase-one input sampler. -/
  gen : (n : ℕ) → SPMF (α₁ n)
  /-- The challenger: consume the phase-one result (`none` = unresolved run) and
  produce hidden state together with the phase-two input. -/
  challenge : (n : ℕ) → α₁ n → Option (β₁ n) → SPMF (γ n × α₂ n)
  /-- Score the phase-two result against the hidden challenger state. -/
  score : (n : ℕ) → γ n → Option (β₂ n) → SPMF Bool

namespace TwoPhaseGame

variable {spec : ℕ → OracleSpec.{0, 0} ι} {α₁ β₁ γ α₂ β₂ : ℕ → Type}

/-- The game as a `SecurityGame` over pairs of program families, via `simulateQ`. -/
noncomputable def toProgGame (G : TwoPhaseGame spec α₁ β₁ γ α₂ β₂) :
    SecurityGame (((n : ℕ) → α₁ n → OracleComp (spec n) (β₁ n)) ×
      ((n : ℕ) → α₂ n → OracleComp (spec n) (β₂ n))) where
  advantage oa n :=
    (G.gen n >>= fun x =>
      (some <$> simulateQ (G.oracle n) (oa.1 n x)) >>= fun r₁ =>
      G.challenge n x r₁ >>= fun gy =>
      (some <$> simulateQ (G.oracle n) (oa.2 n gy.2)) >>= fun r₂ =>
      G.score n gy.1 r₂) true

/-- The game as a `SecurityGame` over pairs of bundled polynomial-time adversaries, via
the machine runs `PolyTimeAdversary.exec`. -/
noncomputable def toPolyGame (G : TwoPhaseGame spec α₁ β₁ γ α₂ β₂)
    (bd₁ : BoundaryData spec α₁ β₁) (bd₂ : BoundaryData spec α₂ β₂) :
    SecurityGame (MachineAdversary bd₁ × MachineAdversary bd₂) where
  advantage D n :=
    (G.gen n >>= fun x =>
      D.1.exec n (G.oracle n) x >>= fun r₁ =>
      G.challenge n x r₁ >>= fun gy =>
      D.2.exec n (G.oracle n) gy.2 >>= fun r₂ =>
      G.score n gy.1 r₂) true

/-- **Advantage transfer**: machines implementing the two phases have exactly the
advantage of the implemented program pair, by the master transfer equation
`PolyTimeAdversary.exec_eq_of_implements` applied once per phase. -/
theorem advantage_toPolyGame_eq (G : TwoPhaseGame spec α₁ β₁ γ α₂ β₂)
    {bd₁ : BoundaryData spec α₁ β₁} {bd₂ : BoundaryData spec α₂ β₂}
    {D₁ : MachineAdversary bd₁} {D₂ : MachineAdversary bd₂}
    {oa₁ : (n : ℕ) → α₁ n → OracleComp (spec n) (β₁ n)}
    {oa₂ : (n : ℕ) → α₂ n → OracleComp (spec n) (β₂ n)}
    (h₁ : D₁.Implements oa₁) (h₂ : D₂.Implements oa₂) (n : ℕ) :
    (G.toPolyGame bd₁ bd₂).advantage (D₁, D₂) n = G.toProgGame.advantage (oa₁, oa₂) n := by
  refine congrArg (fun p : SPMF Bool => p true) (bind_congr fun x => ?_)
  rw [MachineAdversary.exec_eq_of_implements h₁]
  refine bind_congr fun r₁ => bind_congr fun gy => ?_
  rw [MachineAdversary.exec_eq_of_implements h₂]

/-- **Security transfer**: if every pair of bundled polynomial-time adversaries has
negligible machine-level advantage, the program-level game is secure against
`OracleComp.IsPolyTimePair`. -/
theorem secureAgainst_isPolyTimePair_of_polyGame (G : TwoPhaseGame spec α₁ β₁ γ α₂ β₂)
    (bd₁ : BoundaryData spec α₁ β₁) (bd₂ : BoundaryData spec α₂ β₂)
    (hsec : ∀ (D₁ : MachineAdversary bd₁) (D₂ : MachineAdversary bd₂),
      negligible ((G.toPolyGame bd₁ bd₂).advantage (D₁, D₂))) :
    G.toProgGame.secureAgainst (OracleComp.IsPolyTimePair bd₁ bd₂) := by
  rintro ⟨oa₁, oa₂⟩ ⟨⟨w₁⟩, ⟨w₂⟩⟩
  have heq : G.toProgGame.advantage (oa₁, oa₂) = (G.toPolyGame bd₁ bd₂).advantage (w₁.A, w₂.A) :=
    funext fun n => (G.advantage_toPolyGame_eq w₁.implements w₂.implements n).symm
  exact heq ▸ hsec w₁.A w₂.A

end TwoPhaseGame
