/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import KatzLindell.Chapter03.PrivKEav
import VCVio.CryptoFoundations.Asymptotics.Game.TwoPhase

/-!
# `PrivK^eav` on the Machine-Level Game Pipeline

Wiring of the Katz–Lindell eavesdropping experiment into the two-phase challenger
former: `privKChallenger` presents `PrivK^eav` as a `Challenger₂` over the coin oracle,
with the hidden challenge bit living in the challenger's phase-two state `σ₂ := Bool` —
correlated with the adversary's phase-two input, invisible to the adversary, and read
by the score. `advantage_privKChallenger_toProgGame` identifies the game's
program-level advantage with the success probability of the `ProbComp`-level
experiment `privKEav`. Through `Challenger₂.advantage_toMachineGame_eq` and
`Challenger₂.secureAgainst_isPolyTimePair_of_machineGame`, this places the textbook
experiment on the full Turing-machine adversary pipeline: bounding the advantage of
every pair of bundled `MachineAdversary` machines bounds `privKEav` for every
`OracleComp.IsPolyTimePair` program family.

The coin oracle enters memorylessly (`QueryImpl.stateless`) — fresh coins per query —
so this instance exercises the trivial-state corner of the stateful challenger; the
keyed left-right oracle of IND-CPA is the genuinely stateful instantiation.
-/

open ENNReal OracleComp OracleSpec SymmEncAlg

namespace KatzLindell

variable {M K C : ℕ → Type}

/-- Katz–Lindell `PrivK^eav` as a two-phase challenger over the coin oracle, for
adversaries with cross-phase state family `S`: the challenger consumes the chosen
messages, samples the key and the hidden bit (keeping the bit as its phase-two state
`σ₂ := Bool`), encrypts, and scores the second phase's output against the hidden
bit. -/
noncomputable def privKChallenger (π : (n : ℕ) → SymmEncAlg ProbComp (M n) (K n) (C n))
    (S : ℕ → Type) :
    Challenger₂ (fun _ => coinSpec) (fun _ => Unit) (fun n => M n × M n × S n)
      (fun n => S n × C n) (fun _ => Bool) :=
  Challenger₂.ofMemoryless (γ := fun _ => Bool) (fun _ => coinSpec.probHandler)
    (fun _ => pure ())
    (fun n _ r => match r with
      | none => failure
      | some (m₀, m₁, s) => 𝒟[(do
          let k ← (π n).keygen
          let b ← ($ᵗ Bool)
          let c ← (π n).encrypt k (if b then m₁ else m₀)
          pure (b, (s, c)) : ProbComp (Bool × (S n × C n)))])
    (fun _ b r => pure (some b == r))

/-- The program-level advantage of the two-phase challenger game is exactly the success
probability of the `ProbComp`-level experiment: `PrivK^eav` rides the machine
pipeline. -/
theorem advantage_privKChallenger_toProgGame
    (π : (n : ℕ) → SymmEncAlg ProbComp (M n) (K n) (C n))
    (A : PPTEavAdversary M C) (n : ℕ) :
    (privKChallenger π A.State).toProgGame.advantage
      (fun n _ => A.choose n, fun n p => A.distinguish n p) n =
      Pr[= true | privKEav π A n] := by
  rw [probOutput_def, privKChallenger, Challenger₂.advantage_toProgGame_ofMemoryless]
  refine congrFun (congrArg DFunLike.coe ?_) true
  simp only [privKEav, EavExp, PPTEavAdversary.toEavAdversary,
    OracleSpec.simulateQ_probHandler, pure_bind, evalDist_bind,
    uniformSampleImpl.evalDist_simulateQ, bind_map_left]
  simp [monad_norm]

/-- The machine-level endpoint: bounding every pair of bundled machine adversaries in
the two-phase challenger game bounds the program-level game against every
`OracleComp.IsPolyTimePair` family. Instance of the generic security transfer. -/
example (π : (n : ℕ) → SymmEncAlg ProbComp (M n) (K n) (C n)) (S : ℕ → Type)
    (bd₁ : BoundaryData (fun _ => coinSpec) (fun _ => Unit) (fun n => M n × M n × S n))
    (bd₂ : BoundaryData (fun _ => coinSpec) (fun n => S n × C n) (fun _ => Bool))
    (hsec : ∀ D₁ D₂, negligible
      (((privKChallenger π S).toMachineGame bd₁ bd₂).advantage (D₁, D₂))) :
    (privKChallenger π S).toProgGame.secureAgainst
      (OracleComp.IsPolyTimePair bd₁ bd₂) :=
  Challenger₂.secureAgainst_isPolyTimePair_of_machineGame _ bd₁ bd₂ hsec

end KatzLindell
