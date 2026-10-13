/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import HashSig.GXMSS.Completeness
public import HashSigTest.GXMSS.Merkle
public import HashSigTest.GXMSS.EncodingRetry
import all HashSig.GXMSS.Chain
public import HashSig.GXMSS.Chain
public import HashSig.GXMSS.Merkle
public import HashSig.GXMSS.Encoding.Retry
public import VCVio.CryptoFoundations.SyncSignatureAlg

/-!
# GXMSS construction and correctness audit root

Imports the accepted foundations for the corresponding proof modules.
-/

public section

namespace GXMSS.Probe

open Encoding

/-- A single digit of value three for a width-three chain. -/
@[expose] def word : Codeword 1 8 := fun _ => 3

/-- Exactly the true randomizer encodes successfully, into a singleton global code. -/
@[expose] def enc : IncomparableEncoding Unit Unit Bool (Fin 8) 1 8 where
  code := {word}
  incomparable := by
    intro x hx y hy hne
    exact (hne ((Set.mem_singleton_iff.mp hx).trans (Set.mem_singleton_iff.mp hy).symm)).elim
  encode _ _ r _ := if r then some ⟨word, by simp⟩ else none

/-- The recovered randomizer is the successful one, without replacing it by a fresh draw. -/
theorem randomizer_recovered {PP T X H : Type} {h w v : ℕ}
    (hash : HashInstance PP T X H h w v) (sk : SecretKey PP H h v) (ep : Fin (2 ^ h))
    (wr : Codeword v (2 ^ w) × Bool) :
    (signatureOfWord hash sk ep wr).randomizer = wr.2 := rfl

/-- A zero retry budget returns none on the concrete height-three scheme. -/
theorem zero_retries (sk : SecretKey Unit (List ℕ) 3 1) :
    sign (ChainProbe.traceInstance 3 3) enc 0 sk 2 () = pure none :=
  sign_zero _ _ _ _ _

/-- The false randomizer is rejected by actual all-input verification. -/
theorem encoding_failure (pk : PublicKey Unit (List ℕ))
    (ots : Fin 1 → List ℕ) (path : Fin 3 → List ℕ) :
    verify (ChainProbe.traceInstance 3 3) enc pk 2 () ⟨false, ots, path⟩ = false := by
  apply verify_eq_false_of_encoding_failure
  rfl

/-- Independent expected orientation at index two is left, right, left, with a leaf hash. -/
theorem orientation_two :
    (ChainProbe.traceInstance 3 3).recoverRoot () 2 (fun _ => []) ![[9000], [9001], [9002]] =
      [9001, 2000, 0, 2, 9000, 3000, 1, 1, 3000, 2, 0, 9002, 3000, 3, 0] :=
  MerkleProbe.adapter_recovery_two

/-- Height zero retains the raw leaf input and its explicit leaf hash. -/
theorem leaf_hash_zero :
    (ChainProbe.traceInstance 0 3).merkleRoot () (fun _ _ => [91]) = [91, 2000, 0, 0] :=
  MerkleProbe.adapter_root_zero

/-- Actual Construction 3 verification accepts the successful word at height three, index two. -/
theorem composed_verification :
    verify (ChainProbe.traceInstance 3 3) enc
      (keys (ChainProbe.traceInstance 3 3) () (fun ep _ => [90 + ep.val])).1 2 ()
      (signatureOfWord (ChainProbe.traceInstance 3 3)
        (keys (ChainProbe.traceInstance 3 3) () (fun ep _ => [90 + ep.val])).2
        2 (word, true)) = true := by
  apply verify_signatureOfWord
  · exact consistent_keys _ _ _
  · rfl

/-- A failed draw followed by success returns the true randomizer and consumes exactly two draws. -/
theorem successful_randomizer_recovery :
    (enc.retry Encoding.RetryProbe.draw () () 2 3).run [false, true, false] =
      (some (word, true), [false]) := rfl

/-- The signed prefix at epoch two uses the three positive step labels one, two and three. -/
theorem signature_prefix :
    (signatureOfWord (ChainProbe.traceInstance 3 3)
      (keys (ChainProbe.traceInstance 3 3) () (fun ep _ => [90 + ep.val])).2
      2 (word, true)).ots 0 =
        [92, 1000, 3, 1, 1, 1000, 3, 1, 2, 1000, 3, 1, 3] := by decide

/-- Independent expected orientation at index five is right, left, right, with a leaf hash. -/
theorem orientation_five :
    (ChainProbe.traceInstance 3 3).recoverRoot () 5 (fun _ => []) ![[9000], [9001], [9002]] =
      [9002, 9000, 2000, 0, 5, 3000, 1, 2, 9001, 3000, 2, 1, 3000, 3, 0] :=
  MerkleProbe.adapter_recovery_five

end GXMSS.Probe
