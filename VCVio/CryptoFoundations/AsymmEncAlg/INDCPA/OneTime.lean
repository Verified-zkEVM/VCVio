/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma, Quang Dao
-/

module
public import VCVio.CryptoFoundations.AsymmEncAlg.Defs
public import VCVio.CryptoFoundations.SecExp.Measure
public import VCVio.OracleComp.QueryTracking.QueryBound

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

/-- The adversary's raw guess when the challenge bit is fixed. A true bit selects the first
message, and both branches retain the state from message selection. -/
def IND_CPA_OneTime_branch (b : Bool) : OracleComp spec Bool := do
  let keys ← encAlg.keygen
  let choice ← adv.chooseMessages keys.1
  let ct ← encAlg.encrypt keys.1 (if b then choice.1 else choice.2.1)
  adv.distinguish choice.2.2 ct

/-- One-time IND-CPA experiment for an asymmetric encryption algorithm:
sample keys, let the adversary choose challenge messages, encrypt one branch, and return whether
the adversary guessed the hidden bit. -/
noncomputable def IND_CPA_OneTime_Game
    (runtime : ProbCompRuntime (OracleComp spec)) : OracleComp spec Bool := do
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
  (runtime.evalDist (IND_CPA_OneTime_Game (encAlg := encAlg) adv runtime)).boolBias

/-- The bias of the one-time hidden-bit experiment is the distance between the distributions
of the adversary's guesses in the two fixed-bit experiments. -/
theorem IND_CPA_OneTime_Advantage_eq_boolDist {enc : AsymmEncAlg ProbComp M PK SK C}
    (a : enc.IND_CPA_OneTime_Adversary) :
    enc.IND_CPA_OneTime_Advantage ProbCompRuntime.probComp a =
      (𝒟[IND_CPA_OneTime_branch a false]).boolDist (𝒟[IND_CPA_OneTime_branch a true]) := by
  have h : IND_CPA_OneTime_Game a ProbCompRuntime.probComp = (do
      let b ← uniformSample Bool
      let g ← if b then IND_CPA_OneTime_branch a true else IND_CPA_OneTime_branch a false
      pure (b == g)) := by
    change (uniformSample Bool >>= _) = (uniformSample Bool >>= _)
    apply congrArg (fun f => uniformSample Bool >>= f)
    funext b
    cases b <;> simp [IND_CPA_OneTime_branch, monad_norm]
  rw [IND_CPA_OneTime_Advantage, ProbCompRuntime.probComp_evalDist, h,
    evalDist_boolBias_bind_uniformBool, MeasureTheory.Measure.boolDist_comm]

end IND_CPA_TwoPhase

end AsymmEncAlg
