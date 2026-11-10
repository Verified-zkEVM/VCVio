/-
Copyright (c) 2026 VCVio Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: VCVio Contributors
-/

module

public import VCVio.CryptoFoundations.HashChain.Antichain.StrongPayload

/-!
# Strong-payload boundary controls

An unchanged message with a changed nonce still has distinct encoded inputs.
Rejected digests need not have distinct decoder outputs.
No control interprets a projected digest collision as equality of full raw replies.
-/

public section

namespace HashChainStrongPayloadTest

universe u v w x

/-- Same-message, different-nonce pairs retain a typed same-digest collision at distinct inputs. -/
theorem same_message_different_nonce_collision
    {n : Nat} {Message : Type u} {Nonce : Type v} {Input : Type w} {Digest : Type x}
    (input : Message × Nonce → Input) (inputInjective : Function.Injective input)
    (messageHash : Input → Option Digest) (decode : Digest → Option (Fin n → Nat))
    (decodeSuccessInjective : ∀ left right digits,
      decode left = some digits → decode right = some digits → left = right)
    (message : Message) (signedNonce candidateNonce : Nonce)
    (different : candidateNonce ≠ signedNonce) (signedDigest candidateDigest : Digest)
    (digits : Fin n → Nat)
    (signedHash : messageHash (input (message, signedNonce)) = some signedDigest)
    (candidateHash : messageHash (input (message, candidateNonce)) = some candidateDigest)
    (signedParse : decode signedDigest = some digits)
    (candidateParse : decode candidateDigest = some digits) :
    input (message, candidateNonce) ≠ input (message, signedNonce) ∧
      candidateDigest = signedDigest ∧
      messageHash (input (message, candidateNonce)) = some signedDigest ∧
      messageHash (input (message, signedNonce)) = some signedDigest := by
  have sameDigest : candidateDigest = signedDigest :=
    decodeSuccessInjective candidateDigest signedDigest digits candidateParse signedParse
  have distinctInputs : input (message, candidateNonce) ≠ input (message, signedNonce) := by
    intro same
    exact different (congrArg Prod.snd (inputInjective same))
  exact ⟨distinctInputs, sameDigest,
    by simpa only [sameDigest] using candidateHash, signedHash⟩

/-- A missing actual message-hash answer cannot satisfy the successful-call premise. -/
theorem missing_message_hash {Input : Type u} {Digest : Type v}
    (messageHash : Input → Option Digest) (point : Input) (digest : Digest)
    (missing : messageHash point = none) : messageHash point ≠ some digest := by
  intro present
  rw [missing] at present
  cases present

/-- Success injectivity permits many rejected digests to share the result `none`. -/
theorem rejected_digests_need_not_separate {Code : Type u} :
    let decode : Code ⊕ Bool → Option Code := Sum.elim some (fun _ => none)
    (∀ left right code, decode left = some code → decode right = some code → left = right) ∧
      decode (.inr false) = decode (.inr true) ∧
      (.inr false : Code ⊕ Bool) ≠ .inr true := by
  dsimp
  refine ⟨?_, rfl, by simp⟩
  intro left right code hl hr
  cases left <;> cases right <;> simp_all

end HashChainStrongPayloadTest
