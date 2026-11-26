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

This file contains the standard two-phase one-time IND-CPA game and its advantage, the
fixed-branch experiment `IND_CPA_OneTime_Experiment` that the game runs at its hidden bit, and
admissibility of an adversary for a leakage function.

At the `ProbComp` runtime the advantage is the distance between the two fixed-branch experiments
(`IND_CPA_OneTime_Advantage_eq_boolDist`), the one-time form of
`IND_CPA_Advantage_eq_boolDist_LR`. The game places no restriction on the chosen messages, so
against a scheme whose ciphertexts reveal something about the message, such as its length, an
adversary can choose two messages that differ in it. Security of such a scheme is stated for
adversaries that are admissible for that leakage (`IND_CPA_OneTime_Adversary.IsAdmissible`),
the pairs `LeftOrRight.oracle` accepts.
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

/-- Fixed-branch one-time IND-CPA experiment: generate keys, let the adversary choose two
messages, encrypt the first if `b` and the second otherwise, and return the adversary's guess.
`IND_CPA_OneTime_Game` runs it at a uniform hidden bit. -/
def IND_CPA_OneTime_Experiment {encAlg : AsymmEncAlg m M PK SK C}
    (adv : IND_CPA_OneTime_Adversary encAlg) (b : Bool) : m Bool := do
  let (pk, _) ← encAlg.keygen
  let (m₁, m₂, state) ← adv.chooseMessages pk
  let c ← encAlg.encrypt pk (if b then m₁ else m₂)
  adv.distinguish state c

variable {encAlg : AsymmEncAlg (OracleComp spec) M PK SK C}
  (adv : IND_CPA_OneTime_Adversary encAlg)

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

/-- A one-time IND-CPA adversary is admissible for the leakage function `leak` when, on every
public key, every pair of messages it may choose has equal leakage. With the message length as
`leak` these are the adversaries of the standard game for variable-length encryption; with a
constant `leak` every adversary is admissible. -/
def IND_CPA_OneTime_Adversary.IsAdmissible {Λ : Type*} (leak : M → Λ)
    (adv : IND_CPA_OneTime_Adversary encAlg) : Prop :=
  ∀ pk, ∀ z ∈ support (adv.chooseMessages pk), leak z.1 = leak z.2.1

end IND_CPA_TwoPhase

section ProbComp

variable {encAlg : AsymmEncAlg ProbComp M PK SK C}

/-- At the `ProbComp` runtime, the one-time IND-CPA advantage is the distance between the
probabilities that the adversary answers `true` in the two fixed-branch experiments. There is no
factor of two: the advantage is the bias of the hidden-bit game. -/
theorem IND_CPA_OneTime_Advantage_eq_boolDist (adv : IND_CPA_OneTime_Adversary encAlg) :
    IND_CPA_OneTime_Advantage encAlg ProbCompRuntime.probComp adv =
      𝒟[IND_CPA_OneTime_Experiment adv true].boolDist
        𝒟[IND_CPA_OneTime_Experiment adv false] := by
  have hgame : IND_CPA_OneTime_Game adv ProbCompRuntime.probComp = (do
      let b ← $ᵗ Bool
      let z ← if b then IND_CPA_OneTime_Experiment adv true
        else IND_CPA_OneTime_Experiment adv false
      pure (b == z)) := by
    refine bind_congr fun b => ?_
    cases b <;> simp [IND_CPA_OneTime_Experiment]
  rw [IND_CPA_OneTime_Advantage, ProbCompRuntime.probComp_evalDist, hgame,
    evalDist_boolBias_bind_uniformBool]

end ProbComp

end AsymmEncAlg
