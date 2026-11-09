/-
Copyright (c) 2026 VCVio Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: VCVio Contributors
-/

module

public import VCVio.CryptoFoundations.HashChain.Antichain

/-!
# Strong message-and-nonce payload extraction

A successful decoder is injective only where it returns a digit function.
The message digest and chain-value types are independent.
The collision alternative retains two distinct encoded inputs and their actual same-digest calls.
No premise requires that the candidate message differ from the signed message.
-/

public section

namespace HashChain

universe u v w x y z

/-- A valid strong payload is exact, first-merging, earlier, or a typed message-hash collision.

Equality covers the complete message/nonce pair and all chain values.
The collision compares the stated digest type, which need not be a full raw oracle reply.
-/
theorem same_strong_payload_or_first_merge_or_earlier_or_collision
    {n : Nat} {I : Type u} {D : Type v} {Message : Type w} {Nonce : Type x}
    {Input : Type y} {Digest : Type z}
    (height : Fin n → Nat) (address : Fin n → Nat → I) (step : I → D → Option D)
    (honest : Fin n → Nat → D)
    (settled : ∀ i k, k < height i →
      step (address i k) (honest i k) = some (honest i (k + 1)))
    (accepted : Set (Fin n → Nat))
    (bounded : ∀ digits ∈ accepted, ∀ i, digits i ≤ height i)
    (antichain : IsAntichain (· ≤ ·) accepted)
    (input : Message × Nonce → Input) (inputInjective : Function.Injective input)
    (messageHash : Input → Option Digest) (decode : Digest → Option (Fin n → Nat))
    (decodeSuccessInjective : ∀ left right digits,
      decode left = some digits → decode right = some digits → left = right)
    (signedPair candidatePair : Message × Nonce) (signedDigest candidateDigest : Digest)
    (signed digits : Fin n → Nat) (values : Fin n → D)
    (signedHash : messageHash (input signedPair) = some signedDigest)
    (candidateHash : messageHash (input candidatePair) = some candidateDigest)
    (signedParse : decode signedDigest = some signed)
    (candidateParse : decode candidateDigest = some digits)
    (signedAccepted : signed ∈ accepted) (candidateAccepted : digits ∈ accepted)
    (reaches : ∀ i,
      ((List.range' (digits i) (height i - digits i)).map (address i)).foldlM
        (fun value label => step label value) (values i) = some (honest i (height i))) :
    (candidatePair, values) = (signedPair, fun i => honest i (signed i)) ∨
      FirstMerge height address step honest digits values ∨
      (∃ i, digits i < signed i ∧ values i = honest i (digits i)) ∨
      (input candidatePair ≠ input signedPair ∧ candidateDigest = signedDigest ∧
        messageHash (input candidatePair) = some signedDigest ∧
        messageHash (input signedPair) = some signedDigest) := by
  classical
  rcases same_payload_or_first_merge_or_earlier height address step honest settled
    accepted bounded antichain signed digits signedAccepted candidateAccepted values reaches with
    ⟨sameDigits, sameValues⟩ | merge | earlier
  · have sameParse : decode candidateDigest = some signed :=
      candidateParse.trans (congrArg some sameDigits)
    have sameDigest : candidateDigest = signedDigest :=
      decodeSuccessInjective candidateDigest signedDigest signed sameParse signedParse
    by_cases samePair : candidatePair = signedPair
    · exact Or.inl (Prod.ext samePair sameValues)
    · have distinctInputs : input candidatePair ≠ input signedPair := fun h =>
        samePair (inputInjective h)
      exact Or.inr (Or.inr (Or.inr ⟨distinctInputs, sameDigest,
        by simpa only [sameDigest] using candidateHash, signedHash⟩))
  · exact Or.inr (Or.inl merge)
  · exact Or.inr (Or.inr (Or.inl earlier))

end HashChain
