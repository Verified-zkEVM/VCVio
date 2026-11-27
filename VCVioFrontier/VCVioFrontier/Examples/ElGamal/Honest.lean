/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module
-- frontier: CslibFrontier.Crypto.Computational.ElGamal.ProbComp

public import VCVioFrontier.Examples.ElGamal.Choice
public import VCVioFrontier.Examples.ElGamal.HonestPrograms
public import VCVio.CryptoFoundations.AsymmEncAlg.INDCPA.OneTime
public import VCVioFrontier.OracleComp.Measure
public import VCVioFrontier.CryptoFoundations.Asymptotics

/-!
# ElGamal with bounded fair-coin exponent sampling

The public and secret keys, messages and ciphertexts in the scheme are words. Correctness is
stated for encoded group elements. In each of the two chosen-message experiments the honest
algorithms incur a distinguishing error of at most `2 / 2^n` relative to exact uniform exponents.
-/

public section

namespace VCVioFrontier.ElGamal

open Turing.MultiTapeTM Cslib.Crypto Cslib.Probability OracleComp
open scoped ENNReal NNReal

variable (F : PrimeOrderGroupFamily) (desc : ℕ → F.Desc)

/-- VCVio's public-key encryption interface with frontier's bounded fair-coin key generation
and encryption. A ciphertext decrypts to its candidate group-element word. -/
@[expose] noncomputable def wordScheme (n : ℕ) :
    AsymmEncAlg _root_.ProbComp (List Bool) (List Bool) (List Bool) (List Bool) where
  keygen := (Honest.keygen F desc n).liftM (Honest.sample F)
  encrypt pk msg := (Honest.encrypt F desc n pk msg).liftM (Honest.sample F)
  decrypt sk ct := (Honest.decrypt F desc n sk ct).liftM (Honest.sample F)

/-- The installed key generator runs Frontier's bounded fair-coin program. -/
theorem wordScheme_keygen (n : ℕ) :
    (wordScheme F desc n).keygen = F.elGamalKeyGenProb desc n :=
  Honest.liftM_keygen F desc n

/-- The installed encryptor runs Frontier's bounded fair-coin program for every input. -/
theorem wordScheme_encrypt (n : ℕ) :
    (wordScheme F desc n).encrypt = F.elGamalEncryptProb (fun _ m => m) desc n := by
  funext pk msg
  exact Honest.liftM_encrypt F desc n pk msg

/-- The installed decryptor computes the option-valued result of the certified local function. -/
theorem wordScheme_decrypt (n : ℕ) (sk ct : List Bool) :
    (wordScheme F desc n).decrypt sk ct = pure (some (F.elGamalDecryptDet desc n sk ct)) :=
  Honest.liftM_decrypt F desc n sk ct

/-- All three installed algorithms run in uniform probabilistic polynomial time, including
the option-valued result of decryption. -/
theorem wordScheme_efficient (hd : ComputableInPolyTime desc encUnary F.encDesc) :
    IsPPTOn encUnary (encPair encBits encBits) (fun n => (wordScheme F desc n).keygen) ∧
    IsPPTOn (encKeyedInput encBits) encBits
      (fun ⟨n, pk, m⟩ => (wordScheme F desc n).encrypt pk m) ∧
    IsPPTOn (encKeyedInput encBits) (encOption encBits)
      (fun ⟨n, sk, ct⟩ => (wordScheme F desc n).decrypt sk ct) :=
  ⟨(Honest.keygen_realized F hd).isPPTOn, (Honest.encrypt_realized F hd).isPPTOn,
    (Honest.decrypt_realized F hd).isPPTOn⟩

/-- Every supported honest key and encryption of a group element decrypts to the original word. -/
theorem wordScheme_decrypt_encrypt (n : ℕ) (m : F.Carrier (desc n))
    {keys : List Bool × List Bool} {ct : List Bool}
    (hk : keys ∈ (Cslib.ProbComp.eval (wordScheme F desc n).keygen).support)
    (hc : ct ∈ (Cslib.ProbComp.eval ((wordScheme F desc n).encrypt keys.1
      (F.encode (desc n) m))).support) :
    (wordScheme F desc n).decrypt keys.2 ct = pure (some (F.encode (desc n) m)) := by
  rw [wordScheme_keygen] at hk
  rw [wordScheme_encrypt] at hc
  rw [wordScheme_decrypt]
  rw [F.elGamalDecryptDet_elGamalEncryptProb desc n hk m hc]

/-- The single-challenge word game run with the exported VCVio scheme. `valid` receives the
public key and the two proposed message words. -/
@[expose] noncomputable def wordGame (valid : ℕ → List Bool → List Bool → List Bool → Bool)
    (adv : Encryption.WordAdversary) (bit : Bool) (n : ℕ) : _root_.ProbComp Bool :=
  Encryption.gameOn valid (fun k => (wordScheme F desc k).keygen)
    (fun k => (wordScheme F desc k).encrypt) adv bit n

/-- The finite-coin game is close to its exact-uniform exponent idealization for each challenge
bit and every adversary, including computationally unbounded ones. -/
theorem wordGame_approximation (valid : ℕ → List Bool → List Bool → List Bool → Bool)
    (adv : Encryption.WordAdversary) (bit : Bool) (n : ℕ) :
    Game.advantage (Cslib.ProbComp.eval (wordGame F desc valid adv bit n))
      (F.elGamalGroupCPAGameOn valid (fun k => PMF.pure (desc k)) adv bit n) ≤ 2 / 2 ^ n := by
  simpa only [wordGame, wordScheme_keygen, wordScheme_encrypt] using
    F.advantage_gameOn_elGamalMsgCPAGameOn_le valid (fun _ m => m) desc adv bit n

/-- With a polynomial-time guard admitting only encodings of group elements for the selected
public descriptions, DDH makes the two honest fair-coin games indistinguishable. -/
theorem wordGame_negligible {valid : ℕ → List Bool → List Bool → List Bool → Bool}
    (hDDH : F.DDH (fun k => PMF.pure (desc k)))
    (hv : ComputableInPolyTime (fun ⟨n, pk, a, b⟩ => valid n pk a b)
      (Encryption.encChallengePairInput encBits) encBool)
    (hsound : F.AdmitsGroupElementsOn (fun k => PMF.pure (desc k)) (fun _ m => m) valid)
    {adv : Encryption.WordAdversary} (hA : adv.IsPPT) :
    Cslib.Crypto.Negligible fun n =>
      Game.advantage (Cslib.ProbComp.eval (wordGame F desc valid adv false n))
        (Cslib.ProbComp.eval (wordGame F desc valid adv true n)) := by
  simpa only [wordGame, wordScheme_keygen, wordScheme_encrypt] using
    hDDH.indcpaOn_elGamalEncryptProb_on hv hsound (.snd _ _) adv hA

/-- VCVio's ciphertext game measure has distinguishing error at most `2 / 2^n` per challenge
bit, even for an unbounded two-stage adversary. -/
theorem wordGame_measure_approximation (valid : ℕ → List Bool → List Bool → List Bool → Bool)
    (adv : Encryption.WordAdversary) (bit : Bool) (n : ℕ) :
    (𝒟[wordGame F desc valid adv bit n]).boolDist
      (F.elGamalGroupCPAGameOn valid (fun k => PMF.pure (desc k)) adv bit n).toMeasure ≤
      ((2 / 2 ^ n : ℝ≥0) : ℝ≥0∞) := by
  rw [evalDist_eq_toMeasure, boolDist_toMeasure_eq_advantage]
  exact_mod_cast wordGame_approximation F desc valid adv bit n

/-- Security of the bounded fair-coin implementation in VCVio's measure semantics. -/
theorem wordGame_measure_negligible {valid : ℕ → List Bool → List Bool → List Bool → Bool}
    (hDDH : F.DDH (fun k => PMF.pure (desc k)))
    (hv : ComputableInPolyTime (fun ⟨n, pk, a, b⟩ => valid n pk a b)
      (Encryption.encChallengePairInput encBits) encBool)
    (hsound : F.AdmitsGroupElementsOn (fun k => PMF.pure (desc k)) (fun _ m => m) valid)
    {adv : Encryption.WordAdversary} (hA : adv.IsPPT) :
    negligible fun n => (𝒟[wordGame F desc valid adv false n]).boolDist
      (𝒟[wordGame F desc valid adv true n]) := by
  simp only [evalDist_eq_toMeasure, boolDist_toMeasure_eq_advantage]
  exact (negligible_coe_iff _).2 (wordGame_negligible F desc hDDH hv hsound hA)

/-- Single-bit messages encode as the identity or the generator. Both challenge messages are
always admissible. The encryptor is the same word scheme as for group-element payloads. -/
@[expose] noncomputable def bitGame (adv : Encryption.Adversary) :
    Bool → ℕ → _root_.ProbComp Bool :=
  Encryption.game (fun n => (wordScheme F desc n).keygen)
    (fun n pk b => (wordScheme F desc n).encrypt pk (F.encodeBit (desc n) b)) adv

/-- A two-stage chosen-bit adversary against VCVio's word scheme. Its bit-valued messages are
encoded as group elements, and its entire saved word passes to the guessing procedure. -/
@[expose] noncomputable def bitAdversary (adv : Encryption.Adversary) (n : ℕ) :
    (wordScheme F desc n).IND_CPA_OneTime_Adversary where
  State := List Bool
  chooseMessages pk := oneTimeChoice (F.encodeBit (desc n)) <$> adv.choose n pk
  distinguish := adv.guess n

/-- VCVio's hidden-bit one-time advantage for the implemented scheme equals the distance
between the two fixed-bit honest experiments. -/
theorem bitAdversary_advantage (adv : Encryption.Adversary) (n : ℕ) :
    (wordScheme F desc n).IND_CPA_OneTime_Advantage ProbCompRuntime.probComp
      (bitAdversary F desc adv n) = (𝒟[bitGame F desc adv false n]).boolDist
        (𝒟[bitGame F desc adv true n]) := by
  rw [AsymmEncAlg.IND_CPA_OneTime_Advantage_eq_boolDist]
  simp [AsymmEncAlg.IND_CPA_OneTime_branch, bitAdversary, oneTimeChoice, bitGame, Encryption.game,
    Encryption.gameOn, Encryption.ChoiceOut.msg₀, Encryption.ChoiceOut.msg₁,
    Encryption.ChoiceOut.msgs, monad_norm]

/-- Every admissible strict-PPT bit adversary has negligible VCVio distinguishing advantage,
with all message pairs accepted and the bounded fair-coin algorithms used on both branches. -/
theorem bitGame_secure (hDDH : F.DDH (fun k => PMF.pure (desc k)))
    {adv : Encryption.Adversary} (hA : adv.IsPPT) :
    negligible fun n => (𝒟[bitGame F desc adv false n]).boolDist
      (𝒟[bitGame F desc adv true n]) := by
  simp only [evalDist_eq_toMeasure, boolDist_toMeasure_eq_advantage]
  apply (negligible_coe_iff _).2
  have enc : (fun n pk b => (wordScheme F desc n).encrypt pk (F.encodeBit (desc n) b)) =
      F.elGamalEncryptProb F.encodeBit desc := by
    funext n pk b
    rw [wordScheme_encrypt]
    rfl
  simp only [bitGame, wordScheme_keygen, enc]
  exact hDDH.indcpa_elGamalBitEncryptProb adv hA

/-- The bounded fair-coin scheme satisfies VCVio's one-time IND-CPA experiment on encoded bit
messages against every uniform strict-PPT adversary under DDH. -/
theorem bitAdversary_secure (hDDH : F.DDH (fun k => PMF.pure (desc k)))
    {adv : Encryption.Adversary} (hA : adv.IsPPT) :
    negligible fun n => (wordScheme F desc n).IND_CPA_OneTime_Advantage ProbCompRuntime.probComp
      (bitAdversary F desc adv n) := by
  simp only [bitAdversary_advantage]
  exact bitGame_secure F desc hDDH hA

end VCVioFrontier.ElGamal
