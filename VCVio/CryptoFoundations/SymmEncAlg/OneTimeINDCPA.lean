/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import VCVio.CryptoFoundations.SecExp.Measure
public import VCVio.CryptoFoundations.SymmEncAlg.Defs
public import VCVio.OracleComp.Constructions.SampleableType.NativeMeasure
public import VCVio.OracleComp.ProbComp.Basic

/-!
# One-time IND-CPA for symmetric encryption

This file defines the left-or-right one-time IND-CPA game for a symmetric encryption scheme whose
algorithms run in `ProbComp`. The key is hidden from the adversary, which chooses two messages,
receives an encryption of one of them under a fresh key, and guesses which one was encrypted.
The advantage is the Boolean bias `ProbComp.boolBiasAdvantage` of the hidden-bit game.
-/

public section

open OracleComp

namespace SymmEncAlg

variable {M K C : Type}

/-- Two-phase one-time IND-CPA adversary against a `ProbComp` symmetric encryption scheme. The
key is secret, so the message-selection phase receives no input. -/
structure OneTimeINDCPAAdversary (_encAlg : SymmEncAlg ProbComp M K C) where
  /-- State passed from message selection to the guessing phase. -/
  State : Type
  /-- Choose the two challenge messages. -/
  chooseMessages : ProbComp (M × M × State)
  /-- Guess the hidden bit from the challenge ciphertext. -/
  distinguish : State → C → ProbComp Bool

variable {encAlg : SymmEncAlg ProbComp M K C}

/-- One-time left-or-right IND-CPA game: sample a key and a hidden bit, encrypt the message the bit
selects, and return whether the adversary recovers the bit. -/
@[expose]
def oneTimeINDCPAGame (adv : OneTimeINDCPAAdversary encAlg) : ProbComp Bool := do
  let k ← encAlg.keygen
  let b ← ($ᵗ Bool)
  let msgs ← adv.chooseMessages
  let c ← encAlg.encrypt k (if b then msgs.1 else msgs.2.1)
  let b' ← adv.distinguish msgs.2.2 c
  pure (b == b')

/-- One-time IND-CPA advantage: the Boolean bias `|Pr[true] - Pr[false]|` of
`oneTimeINDCPAGame`, equal to `2 * |Pr[b = b'] - 1/2|`. -/
@[expose]
noncomputable def oneTimeINDCPAAdvantage (adv : OneTimeINDCPAAdversary encAlg) : ℝ :=
  (oneTimeINDCPAGame adv).boolBiasAdvantage

end SymmEncAlg
