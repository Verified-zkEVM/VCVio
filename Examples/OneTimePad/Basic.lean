/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma, Quang Dao
-/

module
public import VCVio.CryptoFoundations.SymmEncAlg
public import VCVio.OracleComp.Constructions.BitVec
public import VCVio.ProgramLogic.Tactics.Relational
public import VCVio.OracleComp.Constructions.SampleableType.Basic
public import VCVioWidgets.GameHop.Panel

/-!
# One Time Pad

This file defines the one-time pad scheme, proves correctness, and proves perfect secrecy
in both the independence form `SymmEncAlg.perfectSecrecyAt` and the channel form
`SymmEncAlg.ciphertextRowsEqualAt`.

The measure laws give the Dirac correctness distribution, a product distribution for message
and ciphertext, and a uniform ciphertext measure for every fixed message, so the ciphertexts of
any two messages are equal in distribution.
-/

@[expose] public section

show_panel_widgets [local VCVioWidgets.GameHop.GameHopPanel]

open Mathlib OracleSpec OracleComp ENNReal

/-- The one-time-pad scheme body, parameterized only by its key sampler.

Keeping encryption and decryption here gives the discrete and measure-native examples one shared
scheme implementation. -/
abbrev oneTimePadOfKeygen {m : Type → Type} [Monad m] (sp : ℕ) (keygen : m (BitVec sp)) :
    SymmEncAlg m (BitVec sp) (BitVec sp) (BitVec sp) where
  keygen := keygen
  encrypt k m := return k ^^^ m
  decrypt k σ := return some (k ^^^ σ)

/-- The ordinary probabilistic one-time pad with the standard uniform `BitVec` sampler. -/
def oneTimePad (sp : ℕ) :
    SymmEncAlg ProbComp (BitVec sp) (BitVec sp) (BitVec sp) :=
  oneTimePadOfKeygen sp ($ᵗ BitVec sp)

namespace oneTimePad

/-- The one-time-pad experiment has independent message and ciphertext measures under
the native uniform-oracle interpretation. -/
theorem evalDist_perfectSecrecyExperiment (sp : ℕ) (mgen : ProbComp (BitVec sp)) :
    𝒟[(oneTimePad sp).perfectSecrecyExperiment mgen] =
      𝒟[mgen].prod (ProbabilityTheory.uniformOn Set.univ :
        MeasureTheory.Measure (BitVec sp)) := by
  simpa [SymmEncAlg.perfectSecrecyExperiment, oneTimePad, monad_norm] using
    evalDist_pair_xor_uniformSample sp mgen

/-- A one-time-pad round trip denotes the Dirac measure at the original message. -/
theorem evalDist_completenessExperiment (sp : ℕ) (msg : BitVec sp) :
    𝒟[(oneTimePad sp).completenessExperiment msg] = MeasureTheory.Measure.dirac (some msg) := by
  have hsimp : (oneTimePad sp).completenessExperiment msg =
      (fun _ : BitVec sp => (some msg : Option (BitVec sp))) <$>
        ($ᵗ BitVec sp : ProbComp (BitVec sp)) := by
    simp [SymmEncAlg.completenessExperiment, oneTimePad, monad_norm]
  rw [hsimp, evalDist_map_of_discrete, MeasureTheory.Measure.map_const,
    OracleComp.evalDist_apply_univ_eq_one]
  simp

/-- Encryption and decryption are inverses for any OTP key. -/
lemma complete (sp : ℕ) : (oneTimePad sp).Complete :=
  evalDist_completenessExperiment sp

/-- The one-time-pad ciphertext has a uniform measure for every message sampler. -/
theorem evalDist_perfectSecrecyCipherExperiment (sp : ℕ) (mgen : ProbComp (BitVec sp)) :
    𝒟[(oneTimePad sp).perfectSecrecyCipherExperiment mgen] =
      (ProbabilityTheory.uniformOn Set.univ : MeasureTheory.Measure (BitVec sp)) := by
  simpa [SymmEncAlg.perfectSecrecyCipherExperiment, SymmEncAlg.perfectSecrecyExperiment, oneTimePad,
    monad_norm] using evalDist_cipher_from_pair_uniformSample sp mgen

/-- The one-time pad is perfectly secret in the canonical independence form. -/
lemma perfectSecrecyAt (sp : ℕ) : (oneTimePad sp).perfectSecrecyAt := fun mgen _ ↦ by
  rw [evalDist_perfectSecrecyExperiment, evalDist_perfectSecrecyCipherExperiment]

/-- The one-time pad is perfectly secret for all security parameters. -/
lemma perfectSecrecy : ∀ sp, (oneTimePad sp).perfectSecrecyAt := perfectSecrecyAt

/-! ### Relational proof of ciphertext uniformity

Fixed-message uniformity identifies each ciphertext row with the same measure. -/

/-- Every fixed message has the uniform ciphertext measure. -/
theorem evalDist_perfectSecrecyCipherGivenMsgExperiment (sp : ℕ) (msg : BitVec sp) :
    𝒟[(oneTimePad sp).perfectSecrecyCipherGivenMsgExperiment msg] =
      (ProbabilityTheory.uniformOn Set.univ : MeasureTheory.Measure (BitVec sp)) := by
  simpa [SymmEncAlg.perfectSecrecyCipherGivenMsgExperiment, oneTimePad, monad_norm] using
    evalDist_xor_uniformSample sp msg

/-- The one-time pad has equal ciphertext rows: all messages yield the same
ciphertext distribution. -/
@[game_hop_root]
lemma ciphertextRowsEqual (sp : ℕ) : (oneTimePad sp).ciphertextRowsEqualAt :=
  fun msg₀ msg₁ => EvalDistEq.of_evalDist_eq
    ((evalDist_perfectSecrecyCipherGivenMsgExperiment sp msg₀).trans
      (evalDist_perfectSecrecyCipherGivenMsgExperiment sp msg₁).symm)

end oneTimePad
