/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import VCVio.CryptoFoundations.SymmEncAlg
import VCVio.OracleComp.Constructions.BitVec

/-!
# XOR-Keystream Symmetric Encryption

This file defines `SymmEncAlg.keystreamEnc`, the XOR-keystream shape of a symmetric encryption
scheme (Katz–Lindell Construction 3.17): a key is sampled by `keygen`, a deterministic generator
`gen` stretches it into a `BitVec ℓ` keystream, and a message is masked by XOR with that keystream.
Decryption re-derives the keystream and XORs it back off, so correctness (`keystreamEnc_complete`)
is the involutivity of `XOR`.

The one-time pad is the instance `gen = id`, `keygen = $ᵗ`; the pseudorandom-generator encryption
scheme of §3.3 is the instance where `gen` is a PRG and `keygen` samples a uniform seed. The
generic uniformity of a masked ciphertext lives in `VCVio.OracleComp.Constructions.BitVec`
(`probOutput_cipher_from_pair_uniform`) and is reused by both.
-/

open OracleComp OracleSpec ENNReal

namespace SymmEncAlg

variable {ℓ : ℕ} {K : Type}

/-- The XOR-keystream symmetric encryption scheme (Katz–Lindell Construction 3.17): sample a key
with `keygen`, expand it to a `BitVec ℓ` keystream with the deterministic generator `gen`, and
mask the message by XOR. Decryption re-derives the same keystream and XORs it back off. -/
def keystreamEnc (keygen : ProbComp K) (gen : K → BitVec ℓ) :
    SymmEncAlg ProbComp (BitVec ℓ) K (BitVec ℓ) where
  keygen := keygen
  encrypt k m := pure (m ^^^ gen k)
  decrypt k c := pure (some (c ^^^ gen k))

/-- The XOR-keystream scheme is correct: decryption recovers every message with probability `1`,
since masking twice with the same keystream cancels (`XOR` is involutive). -/
lemma keystreamEnc_complete (keygen : ProbComp K) (gen : K → BitVec ℓ) :
    (keystreamEnc keygen gen).Complete := by
  intro msg
  have hsimp : (keystreamEnc keygen gen).CompleteExp msg =
      keygen >>= fun _ => (pure (some msg) : ProbComp (Option (BitVec ℓ))) := by
    simp only [SymmEncAlg.CompleteExp, keystreamEnc, pure_bind]
    refine bind_congr fun k => ?_
    rw [BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]
  rw [hsimp, probOutput_bind_const, probFailure_of_liftM_PMF, probOutput_pure_self]
  simp

end SymmEncAlg
