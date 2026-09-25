/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma, Quang Dao
-/

module
public import VCVio.CryptoFoundations.AsymmEncAlg.Defs
public import VCVio.CryptoFoundations.SecExp

/-!
# Asymmetric Encryption Schemes: One-Time IND-CPA

This file contains the standard two-phase one-time IND-CPA game and its advantage.
-/

@[expose] public section

open OracleSpec OracleComp ENNReal

universe v

namespace AsymmEncAlg

variable {m : Type → Type v} [Monad m] {M PK SK C : Type}

section IND_CPA_TwoPhase

variable {ι : Type} {spec : OracleSpec ι}

/-- Two-phase adversary for IND-CPA security. -/
structure IND_CPA_OneTime_Adversary (encAlg : AsymmEncAlg m M PK SK C) where
  /-- State carried from the message-choice phase to the distinguishing phase. -/
  State : Type
  /-- Given the public key, choose the two challenge messages and a state. -/
  chooseMessages : PK → m (M × M × State)
  /-- Given the state and the challenge ciphertext, guess which message was encrypted. -/
  distinguish : State → C → m Bool

variable {encAlg : AsymmEncAlg (OracleComp spec) M PK SK C}
  (adv : IND_CPA_OneTime_Adversary encAlg)

/-- One-time IND-CPA experiment for an asymmetric encryption algorithm:
sample keys, let the adversary choose challenge messages, encrypt one branch, and return whether
the adversary guessed the hidden bit. -/
noncomputable def IND_CPA_OneTime_Game
    (runtime : ProbCompRuntime (OracleComp spec)) : MeasureTheory.Measure Bool :=
  runtime.evalDist do
    let b : Bool ← runtime.liftProbComp ($ᵗ Bool)
    let (pk, _) ← encAlg.keygen
    let (m₁, m₂, state) ← adv.chooseMessages pk
    let msg := if b then m₁ else m₂
    let c ← encAlg.encrypt pk msg
    let b' ← adv.distinguish state c
    return (b == b')

/-- One-time IND-CPA advantage: the Boolean bias `Measure.boolBias` of `IND_CPA_OneTime_Game`. -/
noncomputable def IND_CPA_OneTime_Advantage
    (encAlg : AsymmEncAlg (OracleComp spec) M PK SK C)
    (runtime : ProbCompRuntime (OracleComp spec))
    (adv : IND_CPA_OneTime_Adversary encAlg) : ℝ≥0∞ :=
  (IND_CPA_OneTime_Game (encAlg := encAlg) adv runtime).boolBias

end IND_CPA_TwoPhase

end AsymmEncAlg
