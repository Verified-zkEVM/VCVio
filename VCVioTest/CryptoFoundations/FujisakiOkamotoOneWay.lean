/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import VCVio.CryptoFoundations.FujisakiOkamoto.Defs

/-!
# One-wayness canaries for the Fujisaki-Okamoto definitions

The OW-PCVA validity oracle refuses the challenge ciphertext (HHK17, Definition 2.1 and Figure 3).
Against identity encryption, an adversary that guesses the challenge ciphertext when the validity
oracle accepts it, and its complement otherwise, loses with probability one; it would win with
probability one if the oracle decrypted the challenge.

A toy scheme whose decryption flips the plaintext separates the usual win condition `m' = m*`
from the plaintext-checking win condition `Dec(sk, c*) = m'` of HHK17: echoing the challenge wins
the first and loses the second, and the decryption error is one.
-/

public section

open OracleComp OracleSpec

namespace FujisakiOkamotoOneWayTest

/-- Identity encryption of a bit, with decryption returning the ciphertext. -/
@[expose, simps]
def idAlg : AsymmEncAlg ProbComp Bool Unit Unit Bool where
  keygen := pure ((), ())
  encrypt _ msg := pure msg
  decrypt _ c := pure (some c)

/-- Identity encryption of a bit whose decryption flips the ciphertext, so that every honest
ciphertext decrypts to the wrong plaintext. -/
@[expose, simps]
def flipAlg : AsymmEncAlg ProbComp Bool Unit Unit Bool where
  keygen := pure ((), ())
  encrypt _ msg := pure msg
  decrypt _ c := pure (some (!c))

/-- The validity oracle answers `false` on the challenge ciphertext. -/
example (cStar : Bool) : OW_PCVA_queryImpl idAlg () cStar (.inr (.inr cStar)) = pure false := by
  simp

/-- The validity oracle still decrypts every other ciphertext. -/
example : OW_PCVA_queryImpl idAlg () true (.inr (.inr false)) = pure true := by
  simp [OW_PCVA_queryImpl]

/-- The plaintext-checking oracle answers on the challenge ciphertext. -/
example : OW_PCVA_queryImpl idAlg () true (.inr (.inl (true, true))) = pure true := by
  simp [OW_PCVA_queryImpl]

/-- The canonical `ProbComp` runtime lifts public randomness by the identity. -/
lemma liftProbComp_probComp {α : Type} (x : ProbComp α) :
    ProbCompRuntime.probComp.liftProbComp x = x := rfl

/-- Query the validity oracle on the challenge and guess the challenge exactly when it answers
`true`. -/
@[expose]
def validityEchoAdv : OW_PCVA_Adversary idAlg := fun _ cStar => do
  let valid ← (OW_PCVA_oracleSpec idAlg).query (.inr (.inr cStar))
  return cond valid cStar (!cStar)

/-- The refused validity query makes the echoing adversary lose. -/
example : OW_PCVA_Advantage ProbCompRuntime.probComp validityEchoAdv = 0 := by
  simp [OW_PCVA_Advantage, OW_PCVA_Experiment, validityEchoAdv, liftProbComp_probComp]

/-- Guess the challenge ciphertext itself. -/
@[expose]
def echoAdv : OW_PCVA_Adversary flipAlg := fun _ cStar => pure cStar

/-- Echoing the challenge wins the usual OW-PCVA game against the flipping scheme. -/
example : OW_PCVA_Advantage ProbCompRuntime.probComp echoAdv = 1 := by
  simp [OW_PCVA_Advantage, OW_PCVA_Experiment, echoAdv, liftProbComp_probComp]

/-- Echoing the challenge loses the HHK17 OW-PCVA game against the flipping scheme. -/
example : OW_PCVA_PcoAdvantage ProbCompRuntime.probComp echoAdv = 0 := by
  simp [OW_PCVA_PcoAdvantage, OW_PCVA_PcoExperiment, echoAdv, liftProbComp_probComp]

/-- The flipping scheme always decrypts the challenge incorrectly. -/
example : OW_PCVA_DecryptionError ProbCompRuntime.probComp echoAdv = 1 := by
  simp [OW_PCVA_DecryptionError, OW_PCVA_DecryptionErrorExperiment, echoAdv, liftProbComp_probComp]

/-- The explicit-coins flipping scheme, with unit coins. -/
@[expose, simps]
def flipPKE : AsymmEncAlg.ExplicitCoins ProbComp Bool Unit Unit Unit Bool where
  keygen := pure ((), ())
  encrypt _ msg _ := msg
  decrypt _ c := some (!c)

/-- Guess the OW-CPA challenge ciphertext itself. -/
@[expose]
def cpaEchoAdv : flipPKE.OW_CPA_Adversary := fun _ c => pure c

/-- Echoing the challenge wins the usual OW-CPA game against the flipping scheme. -/
example : flipPKE.OW_CPA_Advantage cpaEchoAdv = 1 := by
  simp [AsymmEncAlg.ExplicitCoins.OW_CPA_Advantage, AsymmEncAlg.ExplicitCoins.OW_CPA_Experiment,
    cpaEchoAdv]

/-- Echoing the challenge loses the HHK17 OW-CPA game against the flipping scheme. -/
example : flipPKE.OW_CPA_PcoAdvantage cpaEchoAdv = 0 := by
  simp [AsymmEncAlg.ExplicitCoins.OW_CPA_PcoAdvantage,
    AsymmEncAlg.ExplicitCoins.OW_CPA_PcoExperiment, cpaEchoAdv]

end FujisakiOkamotoOneWayTest
