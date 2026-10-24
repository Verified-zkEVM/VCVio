/-
Copyright (c) 2026 Tom Wambsgans. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Wambsgans
-/

module

public import HashSig.SLHDSA.SHAKE128s.Proof.GrowthCharge

/-!
# Guessing a secret

Guessing a secret is not an event about a query's *answer*: the randomness is the seed sampled at
key generation, and what matters is a query's *input*. An input of the secret-bearing format
determines the secret it is guessing (the payload of `PK.seed ‖ ADRS ‖ payload` is the guess), so
a run that has queried a finite set of inputs has staked at most that many guesses, and each
guess is right against a uniform `128`-bit secret with probability `2 ^ -128`
(`prob_single_guess`). The secret must be sampled independently of the queried inputs. -/

public section

open OracleComp OracleSpec ENNReal

namespace SlhDsaSecurity.SecretGuessCharge

/-- A single input guesses the secret with probability `2 ^ -128`. -/
theorem prob_single_guess (guess : Digest) :
    Pr{let secret ← ($ᵗ Digest : ProbComp Digest)}[guess = secret] =
      1 / ((2 ^ 128 : Nat) : ℝ≥0∞) := by
  have h : Pr{let secret ← ($ᵗ Digest : ProbComp Digest)}[guess = secret] =
      Pr{let secret ← ($ᵗ Digest : ProbComp Digest)}[secret = guess] := by
    exact prEvent_congr _ _ _ fun _ => eq_comm
  let _ : MeasurableSpace Digest := ⊤
  rw [h, prEvent_eq_evalDist_singleton, SampleableType.evalDist_uniformSample,
    ProbabilityTheory.uniformOn_univ_apply_singleton]
  rw [Fintype.card_bitVec, one_div]
  rfl

end SlhDsaSecurity.SecretGuessCharge
