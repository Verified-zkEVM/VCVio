/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module

public import VCVio.CryptoFoundations.HashChain.Antichain.StrongPayload
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Tactic.FinCases

/-!
# Strong-payload boundary controls

An unchanged message with a changed nonce still has distinct encoded inputs.
Rejected digests need not have distinct decoder outputs.
No control interprets a projected digest collision as equality of full raw replies.
A concrete instance with two height-three chains satisfies every premise of the dichotomy.
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

/-! ## A concrete instance -/

/-- Two-chain digit vectors whose coordinates sum to three. -/
def sumThree : Set (Fin 2 → Nat) := {digits | digits 0 + digits 1 = 3}

/-- Digit vectors with a fixed coordinate sum are pairwise incomparable. -/
theorem sumThree_antichain : IsAntichain (· ≤ ·) sumThree := by
  intro left hl right hr different le
  apply different
  have h0 : left 0 ≤ right 0 := le 0
  have h1 : left 1 ≤ right 1 := le 1
  simp only [sumThree, Set.mem_ofPred_eq] at hl hr
  funext i
  revert i
  rw [Fin.forall_fin_two]
  exact ⟨by omega, by omega⟩

/-- A message hash with two digests, one per message bit. -/
def bitHash (point : Bool × Unit) : Option (Fin 2 → Nat) :=
  some (if point.1 then ![1, 2] else ![2, 1])

/-- Every premise of the strong-payload dichotomy holds for two height-three chains over `Nat`
whose steps add one, the sum-three antichain, `decode := some` and `bitHash`. -/
example :=
  HashChain.same_strong_payload_or_first_merge_or_earlier_or_collision
    (fun _ => 3) (fun _ k => k) (fun _ value => some (value + 1)) (fun _ k => k)
    (fun _ _ _ => rfl) sumThree
    (fun digits h i => by
      simp only [sumThree, Set.mem_ofPred_eq] at h
      fin_cases i <;> simp <;> omega)
    sumThree_antichain id Function.injective_id bitHash some
    (fun _ _ _ hl hr => Option.some_injective _ (hl.trans hr.symm))
    (true, ()) (false, ()) ![1, 2] ![2, 1] ![1, 2] ![2, 1] ![2, 1] rfl rfl rfl rfl
    (by simp [sumThree]) (by simp [sumThree])
    (by intro i; fin_cases i <;> rfl)

end HashChainStrongPayloadTest
