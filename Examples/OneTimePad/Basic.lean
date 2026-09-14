/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma, Quang Dao
-/

module
public import VCVio.CryptoFoundations.SymmEncAlg
public import VCVio.OracleComp.Constructions.BitVec
public import VCVio.ProgramLogic.Tactics.Relational
public import VCVioWidgets.GameHop.Panel
import VCVio.OracleComp.EvalDist.UniformCompatibility

/-!
# One Time Pad

This file defines the one-time pad scheme, proves correctness, and proves perfect secrecy
in the canonical independence form used by `SymmEncAlg.perfectSecrecyAt`.

The native measure laws give the Dirac correctness distribution and a product distribution
for message and ciphertext. Their singleton consequences supply the discrete `SymmEncAlg`
predicates during migration.

The relational proof (`cipherGivenMsg_equiv`, `ciphertextRowsEqual`) also shows that any two
messages yield the same ciphertext distribution via a bijection coupling, using the
`by_equiv` / `rvcstep` tactic workflow.
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
theorem evalDist_perfectSecrecyExp [OracleSpec.IsUniformMeasureSpec unifSpec]
    (sp : ℕ) (mgen : ProbComp (BitVec sp)) :
    𝒟[(oneTimePad sp).PerfectSecrecyExp mgen] =
      𝒟[mgen].prod (ProbabilityTheory.uniformOn Set.univ :
        MeasureTheory.Measure (BitVec sp)) := by
  simpa [SymmEncAlg.PerfectSecrecyExp, oneTimePad, monad_norm] using
    evalDist_pair_xor_uniformSample sp mgen

/-- A one-time-pad round trip denotes the Dirac measure at the original message. -/
theorem evalDist_completeExp [OracleSpec.IsUniformMeasureSpec unifSpec]
    (sp : ℕ) (msg : BitVec sp) :
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
theorem evalDist_perfectSecrecyCipherExp [OracleSpec.IsUniformMeasureSpec unifSpec]
    (sp : ℕ) (mgen : ProbComp (BitVec sp)) :
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
  have hpair :
      Pr[= (msg, σ) | (oneTimePad sp).PerfectSecrecyExp mgen] =
        Pr[= msg | mgen] *
          (Fintype.card (BitVec sp) : ℝ≥0∞)⁻¹ := by
    simpa [SymmEncAlg.PerfectSecrecyExp, oneTimePad,
      monad_norm] using
      probOutput_pair_xor_uniform sp (mx := mgen) msg σ
  rw [hpair, ← probOutput_cipher_uniform]

/-- The one-time pad is perfectly secret for all security parameters. -/
lemma perfectSecrecy : ∀ sp, (oneTimePad sp).perfectSecrecyAt := perfectSecrecyAt

/-! ### Relational proof of ciphertext uniformity

Alternative proof that encrypting any two messages with a random OTP key yields
the same ciphertext distribution. Uses the bijection coupling `k ↦ k ⊕ m₀ ⊕ m₁`. -/

open OracleComp.ProgramLogic in
/-- Encrypting any two messages with a random OTP key yields the same distribution,
proved via a bijection coupling. -/
lemma cipherGivenMsg_equiv (sp : ℕ) (msg₀ msg₁ : BitVec sp) :
    GameEquiv
      ((oneTimePad sp).PerfectSecrecyCipherGivenMsgExp msg₀)
      ((oneTimePad sp).PerfectSecrecyCipherGivenMsgExp msg₁) := by
  simp only [SymmEncAlg.PerfectSecrecyCipherGivenMsgExp, oneTimePad]
  let c := msg₀ ^^^ msg₁
  have hxor : Function.Bijective (fun x : BitVec sp => x ^^^ c) :=
    Function.Involutive.bijective fun x => by
      rw [BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]
  change GameEquiv (($ᵗ BitVec sp) >>= fun k => pure (k ^^^ msg₀))
    (($ᵗ BitVec sp) >>= fun k => pure (k ^^^ msg₁))
  by_equiv
  rvcstep using (fun k : BitVec sp => k ^^^ c)
  · apply Relational.relTriple_pure_pure
    simp only [show c = msg₀ ^^^ msg₁ from rfl,
      BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]
    rfl
  · exact hxor

/-- The one-time pad has equal ciphertext rows: all messages yield the same
ciphertext distribution. Derived from the relational `GameEquiv` proof above. -/
@[game_hop_root]
lemma ciphertextRowsEqual (sp : ℕ) : (oneTimePad sp).ciphertextRowsEqualAt :=
  fun msg₀ msg₁ σ => (cipherGivenMsg_equiv sp msg₀ msg₁).probOutput_eq σ

end oneTimePad
