/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma, Quang Dao
-/

module
public import VCVio.CryptoFoundations.SymmEncAlg
public import VCVio.OracleComp.Constructions.BitVec
public import VCVio.ProgramLogic.Tactics.Relational
public import VCVio.OracleComp.Constructions.SampleableType.MeasureCompatibility
public import VCVioWidgets.GameHop.Panel
import VCVio.OracleComp.EvalDist.UniformCompatibility

/-!
# One Time Pad

This file defines the one-time pad scheme, proves correctness, and proves perfect secrecy
in the canonical independence form used by `SymmEncAlg.perfectSecrecyAt`.

The native measure laws give the Dirac correctness distribution and a product distribution
for message and ciphertext. Their singleton consequences supply the discrete `SymmEncAlg`
predicates during migration.

Fixed-message uniformity gives equal ciphertext rows directly, and a compatibility bridge
exports the corresponding `GameEquiv` statement.
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
theorem evalDist_perfectSecrecyExp (sp : ℕ) (mgen : ProbComp (BitVec sp)) :
    𝒟[(oneTimePad sp).PerfectSecrecyExp mgen] =
      𝒟[mgen].prod (ProbabilityTheory.uniformOn Set.univ :
        MeasureTheory.Measure (BitVec sp)) := by
  simpa [SymmEncAlg.PerfectSecrecyExp, oneTimePad, monad_norm] using
    evalDist_pair_xor_uniformSample sp mgen

/-- A one-time-pad round trip denotes the Dirac measure at the original message. -/
theorem evalDist_completeExp (sp : ℕ) (msg : BitVec sp) :
    𝒟[(oneTimePad sp).CompleteExp msg] = MeasureTheory.Measure.dirac (some msg) := by
  have hsimp : (oneTimePad sp).CompleteExp msg =
      (fun _ : BitVec sp => (some msg : Option (BitVec sp))) <$>
        ($ᵗ BitVec sp : ProbComp (BitVec sp)) := by
    simp [SymmEncAlg.CompleteExp, oneTimePad, monad_norm]
  rw [hsimp, evalDist_map_of_discrete, MeasureTheory.Measure.map_const,
    OracleComp.evalDist_apply_univ_eq_one]
  simp

/-- Encryption and decryption are inverses for any OTP key. -/
lemma complete (sp : ℕ) : (oneTimePad sp).Complete := by
  intro msg
  rw [← evalDist_apply_singleton, evalDist_completeExp]
  simp

/-- The one-time-pad ciphertext has a uniform measure for every message sampler. -/
theorem evalDist_perfectSecrecyCipherExp (sp : ℕ) (mgen : ProbComp (BitVec sp)) :
    𝒟[(oneTimePad sp).PerfectSecrecyCipherExp mgen] =
      (ProbabilityTheory.uniformOn Set.univ : MeasureTheory.Measure (BitVec sp)) := by
  simpa [SymmEncAlg.PerfectSecrecyCipherExp, SymmEncAlg.PerfectSecrecyExp, oneTimePad,
    monad_norm] using evalDist_cipher_from_pair_uniformSample sp mgen

lemma probOutput_cipher_uniform (sp : ℕ)
    (mgen : ProbComp (BitVec sp)) (σ : BitVec sp) :
    Pr[= σ | (oneTimePad sp).PerfectSecrecyCipherExp mgen] =
      (Fintype.card (BitVec sp) : ℝ≥0∞)⁻¹ := by
  rw [← evalDist_apply_singleton, evalDist_perfectSecrecyCipherExp,
    ProbabilityTheory.uniformOn_univ_apply_singleton]

/-- The one-time pad is perfectly secret in the canonical independence form. -/
lemma perfectSecrecyAt (sp : ℕ) : (oneTimePad sp).perfectSecrecyAt := by
  intro mgen msg σ
  simp only [← evalDist_apply_singleton, evalDist_perfectSecrecyExp,
    evalDist_perfectSecrecyCipherExp]
  simpa only [Set.singleton_prod_singleton] using
    (MeasureTheory.Measure.prod_prod (μ := 𝒟[mgen])
      (ν := ProbabilityTheory.uniformOn Set.univ) {msg} {σ})

/-- The one-time pad is perfectly secret for all security parameters. -/
lemma perfectSecrecy : ∀ sp, (oneTimePad sp).perfectSecrecyAt := perfectSecrecyAt

/-! ### Relational proof of ciphertext uniformity

Fixed-message uniformity identifies each ciphertext row with the same measure. -/

/-- Every fixed message has the uniform ciphertext measure. -/
theorem evalDist_perfectSecrecyCipherGivenMsgExp (sp : ℕ) (msg : BitVec sp) :
    𝒟[(oneTimePad sp).PerfectSecrecyCipherGivenMsgExp msg] =
      (ProbabilityTheory.uniformOn Set.univ : MeasureTheory.Measure (BitVec sp)) := by
  simpa [SymmEncAlg.PerfectSecrecyCipherGivenMsgExp, oneTimePad, monad_norm] using
    evalDist_xor_uniformSample sp msg

open OracleComp.ProgramLogic in
/-- Encrypting any two fixed messages has the same ciphertext distribution. -/
lemma cipherGivenMsg_equiv (sp : ℕ) (msg₀ msg₁ : BitVec sp) :
    GameEquiv
      ((oneTimePad sp).PerfectSecrecyCipherGivenMsgExp msg₀)
      ((oneTimePad sp).PerfectSecrecyCipherGivenMsgExp msg₁) := by
  apply evalSPMF_eq_of_evalDist_eq
  rw [evalDist_perfectSecrecyCipherGivenMsgExp, evalDist_perfectSecrecyCipherGivenMsgExp]

/-- The one-time pad has equal ciphertext rows: all messages yield the same
ciphertext distribution. Derived from the relational `GameEquiv` proof above. -/
@[game_hop_root]
lemma ciphertextRowsEqual (sp : ℕ) : (oneTimePad sp).ciphertextRowsEqualAt :=
  fun msg₀ msg₁ σ => (cipherGivenMsg_equiv sp msg₀ msg₁).probOutput_eq σ

end oneTimePad
