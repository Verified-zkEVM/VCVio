/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module
-- frontier: CslibFrontier.Crypto.Computational.ElGamal.ProbComp

public import CslibFrontier.Crypto.Computational.ElGamal.ProbComp
public import PolyFunFrontier.PFunctor.Free.Realization
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Pair.Projections
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Nat.WordsRoundTrip

/-!
# Honest ElGamal programs over a bounded exponent sampler

A request supplies a security parameter and a group description. Its response is the natural
exponent returned by the bounded fair-coin sampler. The honest algorithms compose these draws
with deterministic operations on encoded group elements and framed words.
-/

public section

namespace VCVioFrontier.ElGamal.Honest

open PFunctor Turing.MultiTapeTM Cslib.Crypto

variable (F : PrimeOrderGroupFamily)

/-- An exponent request specifies its precision parameter and the group order to sample modulo. -/
abbrev signature := monomial (ℕ × F.Desc) ℕ

/-- Realize each request with Frontier's bounded fair-coin sampler. -/
@[expose] noncomputable def sample : Handler Cslib.ProbComp (signature F) :=
  fun q => F.sampleExp q.1 q.2

variable (desc : ℕ → F.Desc)

/-- Draw the exponent for a single operation in the group selected at security parameter `n`. -/
@[expose] def exponent (n : ℕ) : (signature F).FreeM ℕ :=
  FreeM.lift (P := signature F) (n, desc n)

/-- Draw a secret exponent and derive its framed public key and encoded secret key. -/
@[expose] def keygen (n : ℕ) : (signature F).FreeM (List Bool × List Bool) :=
  (fun a => (encPair F.encDesc encBits (desc n, F.encodeElGamalPublicKey (desc n, a)), encNat a))
    <$> exponent F desc n

/-- Draw fresh randomness and mask the input group-element word under the supplied public key. -/
@[expose] def encrypt (n : ℕ) (pk msg : List Bool) : (signature F).FreeM (List Bool) :=
  (fun b => encPair encBits encBits (F.encodeElGamalEncrypt (desc n, dropFrame pk, msg, b)))
    <$> exponent F desc n

/-- Unpack the ciphertext and secret exponent, then return the recovered group-element word. -/
@[expose] def decrypt (n : ℕ) (sk ct : List Bool) : (signature F).FreeM (Option (List Bool)) :=
  pure (some (F.elGamalDecryptDet desc n sk ct))

/-- A sampler request receives exactly the answer supplied at its precision and description. -/
theorem liftM_exponent {m : Type → Type} [Monad m] [LawfulMonad m]
    (H : Handler m (signature F)) (n : ℕ) :
    (exponent F desc n).liftM H = H (n, desc n) :=
  FreeM.liftM_lift (P := signature F) H (n, desc n)

/-- Handling key generation yields Frontier's bounded key generator as a program. -/
theorem liftM_keygen (n : ℕ) :
    (keygen F desc n).liftM (sample F) = F.elGamalKeyGenProb desc n := by
  simp only [keygen, FreeM.liftM_map, liftM_exponent,
    PrimeOrderGroupFamily.elGamalKeyGenProb, sample, bind_pure_comp]

/-- Handling encryption yields Frontier's bounded encryptor, including framing. -/
theorem liftM_encrypt (n : ℕ) (pk msg : List Bool) :
    (encrypt F desc n pk msg).liftM (sample F) =
      F.elGamalEncryptProb (fun _ m => m) desc n pk msg := by
  simp only [encrypt, FreeM.liftM_map, liftM_exponent,
    PrimeOrderGroupFamily.elGamalEncryptProb, sample, bind_pure_comp]

/-- Decryption is independent of each sampling request. -/
theorem liftM_decrypt (n : ℕ) (sk ct : List Bool) :
    (decrypt F desc n sk ct).liftM (sample F) = pure (some (F.elGamalDecryptDet desc n sk ct)) :=
  FreeM.liftM_pure _ _

/-- Install a caller-supplied exponent in a deterministic run of an honest algorithm. -/
@[expose] def fixedExponent (a : ℕ) : Handler Id (signature F) := fun _ => a

/-- With a chosen exponent the generator returns its encoded key pair. -/
theorem keygen_fixedExponent (n a : ℕ) :
    (keygen F desc n).liftM (fixedExponent F a) =
      (encPair F.encDesc encBits (desc n, F.encodeElGamalPublicKey (desc n, a)), encNat a) := by
  rw [keygen, FreeM.liftM_map, liftM_exponent]
  rfl

/-- With a chosen nonce the encryptor returns its deterministic framed ciphertext. -/
theorem encrypt_fixedExponent (n b : ℕ) (pk msg : List Bool) :
    (encrypt F desc n pk msg).liftM (fixedExponent F b) =
      encPair encBits encBits (F.encodeElGamalEncrypt (desc n, dropFrame pk, msg, b)) := by
  rw [encrypt, FreeM.liftM_map, liftM_exponent]
  rfl

/-- Installing exponents `a` and `b` in the key generator and encryptor recovers the message
after decryption, for *all* natural exponents, independently of the law used to draw them. -/
theorem decrypt_encrypt_fixedExponent (n a b : ℕ) (m : F.Carrier (desc n)) :
    let keys := (keygen F desc n).liftM (fixedExponent F a)
    let ct := (encrypt F desc n keys.1 (F.encode (desc n) m)).liftM (fixedExponent F b)
    (decrypt F desc n keys.2 ct).liftM (fixedExponent F a) = some (F.encode (desc n) m) := by
  dsimp only
  rw [keygen_fixedExponent, encrypt_fixedExponent, decrypt, FreeM.liftM_pure]
  change some (F.elGamalDecryptDet _ _ _ _) = _
  simp only [PrimeOrderGroupFamily.elGamalDecryptDet, PrimeOrderGroupFamily.encodeElGamalEncrypt,
    ofBits_encNat, unframe_encPair_encBits, dropFrame_encPair_encBits]
  exact congrArg some (F.decodeElGamal_encodeElGamalEncrypt (desc n) a b m)

variable {desc} (hd : ComputableInPolyTime desc encUnary F.encDesc)
include hd

/-- A sampler request is efficient for a polynomial-time family of group descriptions. -/
theorem exponent_realized :
    FreeM.PPTProgram (sample F) encUnary encNat (exponent F desc) := by
  change FreeM.PPTProgram _ encUnary encNat (fun n => FreeM.lift (P := signature F) (n, desc n))
  simpa only [id_map] using FreeM.PPTProgram.call
    (H := sample F) (query := fun n => (n, desc n)) (answer := fun _ => id)
    (by simpa only [sample, id_map] using F.isPPTOn_sampleExp ComputableInPolyTime.id' hd)

/-- The key-generation certificate composes its exponent draw with public-key derivation. -/
theorem keygen_realized :
    FreeM.PPTProgram (sample F) encUnary (encPair encBits encBits) (keygen F desc) := by
  apply (exponent_realized F hd).mapWith
  let hd' := hd.comp' (ComputableInPolyTime.fst encUnary encNat)
  let ha := ComputableInPolyTime.snd encUnary encNat
  exact (hd'.prod (F.computableInPolyTime_encodeElGamalPublicKey.comp'
    (hd'.prod ha))).encoding_comp.prod ha.encoding_comp

/-- The encryption certificate accounts for randomness, ciphertext construction and framing. -/
theorem encrypt_realized :
    FreeM.PPTProgram (sample F) (encKeyedInput encBits) encBits
      (fun p : ℕ × List Bool × List Bool => encrypt F desc p.1 p.2.1 p.2.2) := by
  let ein := encKeyedInput encBits
  let hn := ComputableInPolyTime.fst encUnary (encPair encBits encBits)
  apply ((exponent_realized F hd).preprocess hn).mapWith
  let hp := ComputableInPolyTime.fst ein encNat
  let hb := ComputableInPolyTime.snd ein encNat
  exact (F.computableInPolyTime_encodeElGamalEncrypt.comp'
    ((hd.comp' hp.fst').prod ((ComputableInPolyTime.dropFrame.comp' hp.snd'.fst').prod
      (hp.snd'.snd'.prod hb)))).encoding_comp

/-- The deterministic decryption certificate includes the result's option tag. -/
theorem decrypt_realized :
    FreeM.PPTProgram (sample F) (encKeyedInput encBits) (encOption encBits)
      (fun p : ℕ × List Bool × List Bool => decrypt F desc p.1 p.2.1 p.2.2) := by
  apply FreeM.PPTProgram.localMap
  exact (ComputableInPolyTime.optionSome encBits).comp'
    (F.computableInPolyTime_elGamalDecryptDet hd)

end VCVioFrontier.ElGamal.Honest
