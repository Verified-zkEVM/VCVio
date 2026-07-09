/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import Examples.KatzLindell.PrivKEav
import VCVio.CryptoFoundations.Asymptotics.TwoPhaseGame

/-!
# `PrivK^eav` on the Machine-Level Game Pipeline

Wiring of the Katz–Lindell eavesdropping experiment into the two-phase machine game
former: `privKTwoPhaseGame` presents `PrivK^eav` as a `TwoPhaseGame` over the coin
oracle, with the challenger holding the hidden bit as its private state, and
`advantage_privKTwoPhaseGame_toProgGame` identifies the game's program-level advantage
with the success probability of the `ProbComp`-level experiment `privKEav`. Through
`TwoPhaseGame.advantage_toPolyGame_eq` and
`TwoPhaseGame.secureAgainst_isPolyTimePair_of_polyGame`, this places the textbook
experiment on the full Turing-machine adversary pipeline: bounding the advantage of
every pair of bundled `PolyTimeAdversary` machines bounds `privKEav` for every
`OracleComp.IsPolyTimePair` program family.
-/

open ENNReal OracleComp OracleSpec SymmEncAlg

namespace KatzLindell

variable {M K C : ℕ → Type}

/-- Katz–Lindell `PrivK^eav` as a two-phase machine game over the coin oracle, for
adversaries with cross-phase state family `S`: the challenger consumes the chosen
messages, samples the key and the hidden bit (keeping the bit as its private state
`γ := Bool`), encrypts, and scores the second phase's output against the hidden bit. -/
noncomputable def privKTwoPhaseGame (π : (n : ℕ) → SymmEncAlg ProbComp (M n) (K n) (C n))
    (S : ℕ → Type) :
    TwoPhaseGame (fun _ => coinSpec) (fun _ => Unit) (fun n => M n × M n × S n)
      (fun _ => Bool) (fun n => S n × C n) (fun _ => Bool) where
  oracle _ := coinSpec.probHandler
  gen _ := pure ()
  challenge n _ r := match r with
    | none => failure
    | some (m₀, m₁, s) => 𝒟[(do
        let k ← (π n).keygen
        let b ← ($ᵗ Bool)
        let c ← (π n).encrypt k (if b then m₁ else m₀)
        pure (b, (s, c)) : ProbComp (Bool × (S n × C n)))]
  score _ b r := pure (some b == r)

/-- The program-level advantage of the two-phase machine game is exactly the success
probability of the `ProbComp`-level experiment: `PrivK^eav` rides the machine
pipeline. -/
theorem advantage_privKTwoPhaseGame_toProgGame
    (π : (n : ℕ) → SymmEncAlg ProbComp (M n) (K n) (C n))
    (A : PPTEavAdversary M C) (n : ℕ) :
    (privKTwoPhaseGame π A.State).toProgGame.advantage
      (fun n _ => A.choose n, fun n p => A.distinguish n p) n =
      Pr[= true | privKEav π A n] := by
  rw [probOutput_def]
  refine congrFun (congrArg DFunLike.coe ?_) true
  simp only [privKTwoPhaseGame, privKEav, EavExp,
    PPTEavAdversary.toEavAdversary, OracleSpec.simulateQ_probHandler, pure_bind,
    evalDist_bind, uniformSampleImpl.evalDist_simulateQ, bind_map_left]
  simp [monad_norm]

end KatzLindell
