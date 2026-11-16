/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import VCVio.CryptoFoundations.IncomparableEncoding.Winternitz
public import VCVio.CryptoFoundations.IncomparableEncoding.TargetSum
public import VCVio.CryptoFoundations.IncomparableEncoding.NonMaximum

/-!
# Concrete encoding instances

Small words distinguish checksum carry and low-first order, globally incomparable codewords,
target-sum acceptance/rejection, and the count and coefficient of an impossible target.
-/

public section

namespace IncomparableEncoding.InstanceProbe

open IncomparableEncoding

/-- The small payload `(1,1)` without vector-notation dependencies. -/
@[expose] def oneOne : Codeword 2 4 := fun _ => 1

/-- The small payload `(1,2)` without vector-notation dependencies. -/
@[expose] def oneTwo : Codeword 2 4 := fun i => if i = 0 then 1 else 2

/-- The all-zero two-digit word. -/
@[expose] def zeroZero : Codeword 2 4 := fun _ => 0

/-- Two radix-four payload digits need two checksum digits. -/
theorem checksum_width_two_two : Winternitz.checksumWidth 2 2 = 2 := by decide

/-- The complement of `(1,1)` is four, encoded low-first as `(0,1)`. -/
theorem checksum_carry :
    (Winternitz.checksum (by decide : 0 < 2) oneOne ⟨0, by decide⟩).val = 0 ∧
    (Winternitz.checksum (by decide : 0 < 2) oneOne ⟨1, by decide⟩).val = 1 := by
  have hrec := Winternitz.checksum_reconstruct (n₀ := 2) (w := 2)
    (by decide) oneOne
  have hcomp : Winternitz.complement (w := 2) oneOne = 4 := by
    decide
  simp only [checksum_width_two_two, hcomp] at hrec
  simp only [List.ofFn_succ, List.ofFn_zero, Nat.ofDigits_cons,
    Nat.ofDigits_nil, mul_zero, add_zero] at hrec
  have hzero := (Winternitz.checksum (by decide : 0 < 2) oneOne
    ⟨0, by decide⟩).isLt
  have hone := (Winternitz.checksum (by decide : 0 < 2) oneOne
    ⟨1, by decide⟩).isLt
  norm_num at hrec hzero hone
  change (Winternitz.checksum (by decide : 0 < 2) oneOne ⟨0, by decide⟩).val +
    4 * (Winternitz.checksum (by decide : 0 < 2) oneOne ⟨1, by decide⟩).val = 4 at hrec
  omega

/-- Changing the payload changes its appended word even across a checksum carry. -/
theorem distinct_checksum_words :
    Winternitz.word (by decide : 0 < 2) oneOne ≠
      Winternitz.word (by decide : 0 < 2) oneTwo := by
  decide

/-- Both words belong to the all-payload checksum-word range and are incomparable. -/
theorem distinct_checksum_words_incomparable :
    IncomparableWords
      (Winternitz.word (by decide : 0 < 2) oneOne)
      (Winternitz.word (by decide : 0 < 2) oneTwo) := by
  exact Winternitz.checksumWordCode_incomparable 2 2 (by decide)
    ⟨oneOne, rfl⟩ ⟨oneTwo, rfl⟩ distinct_checksum_words

/-- A sum-three word belongs to the target-sum code. -/
theorem target_sum_accepts :
    oneTwo ∈ TargetSum.code 2 2 3 := by
  change (∑ i : Fin 2, (oneTwo i).val) = 3
  decide

/-- A sum-zero word is rejected when the target is three. -/
theorem target_sum_rejects :
    zeroZero ∉ TargetSum.code 2 2 3 := by
  change (∑ i : Fin 2, (zeroZero i).val) ≠ 3
  decide

/-- A two-input toy THF exposes the target-sum accept and fail branches. -/
@[expose] def toyTargetParameters :
    TargetSum.Parameters PUnit PUnit Bool PUnit PUnit 2 2 3 where
  thf := {
    seedGen := pure PUnit.unit
    eval := fun _ _ (_, r) => if r then oneTwo else zeroZero
  }
  epochToTweak := fun _ => PUnit.unit

/-- A target-sum hash output returns its word. -/
theorem target_encoding_accepts :
    (TargetSum.encoding toyTargetParameters).value
      PUnit.unit PUnit.unit true PUnit.unit = some oneTwo := by
  apply (TargetSum.value_eq_some_iff toyTargetParameters
    PUnit.unit PUnit.unit true PUnit.unit oneTwo).2
  exact ⟨rfl, by decide⟩

/-- A non-target hash output returns explicit failure. -/
theorem target_encoding_rejects :
    (TargetSum.encoding toyTargetParameters).value
      PUnit.unit PUnit.unit false PUnit.unit = none := by
  rw [TargetSum.value_eq_none_iff]
  decide

/-- Target seven cannot be reached by two radix-four digits. -/
theorem impossible_target_count : TargetSum.acceptedCount 2 2 7 = 0 := by
  decide

/-- The generating-polynomial coefficient is zero for the same impossible target. -/
theorem impossible_target_coefficient : TargetSum.coefficient 2 2 7 = 0 := by
  rw [TargetSum.coefficient_eq_acceptedCount]
  exact impossible_target_count

/-- Four radix-four words of length two have digit sum three. -/
theorem target_count_four : TargetSum.acceptedCount 2 2 3 = 4 := by decide

/-- The same acceptance count is the generating-polynomial coefficient. -/
theorem target_coefficient_four : TargetSum.coefficient 2 2 3 = 4 := by
  rw [TargetSum.coefficient_eq_acceptedCount]
  exact target_count_four

/-- The empty word is the unique word at target zero. -/
theorem empty_word_count : TargetSum.acceptedCount 0 0 0 = 1 := by decide

/-- The empty word cannot attain a positive target. -/
theorem empty_word_impossible : TargetSum.acceptedCount 0 0 1 = 0 := by decide

/-- A singleton digit alphabet has only the zero word. -/
theorem zero_width_count : TargetSum.acceptedCount 2 0 0 = 1 := by decide

/-- A parameter-only count supplies two codewords even without hash surjectivity. -/
theorem target_two_codewords :
    ∃ x y : Codeword 2 4, x ∈ TargetSum.code 2 2 3 ∧
      y ∈ TargetSum.code 2 2 3 ∧ x ≠ y :=
  TargetSum.two_codewords_of_acceptedCount 2 2 3 (by rw [target_count_four]; decide)

/-- The concrete target-sum encoding excludes the maximum word by its global code. -/
theorem target_nonmaximum : (TargetSum.encoding toyTargetParameters).NoMaximumOutput :=
  (TargetSum.encoding toyTargetParameters).noMaximumOutput_of_two_codewords target_two_codewords

/-- A checksum instance with a biased public seed and a two-word message-hash range. -/
@[expose] def toyWinternitzParameters :
    Winternitz.Parameters Bool PUnit Bool PUnit PUnit 2 2 where
  payloadLengthPositive := by decide
  digitWidthPositive := by decide
  thf := {
    seedGen := do
      let r ← $ᵗ (Fin 3)
      return r != 0
    eval := fun _ _ (_, r) => if r then oneOne else oneTwo
  }
  epochToTweak := fun _ => PUnit.unit

/-- Checksum encoding has zero canonical pointwise error without a uniform-seed premise. -/
theorem checksum_canonical_error :
    (Winternitz.encoding toyWinternitzParameters).CanonicalErrorAtMost 0 :=
  Winternitz.canonicalErrorAtMost_zero toyWinternitzParameters

/-- The concrete checksum code supplies the generic nonmaximum premise. -/
theorem checksum_nonmaximum :
    (Winternitz.encoding toyWinternitzParameters).NoMaximumOutput :=
  (Winternitz.encoding toyWinternitzParameters).noMaximumOutput_of_two_codewords
    (Winternitz.two_codewords toyWinternitzParameters)

/-- The checksum bridge preserves its actual seed computation and both capacities. -/
theorem checksum_bridge_parameters (p K : ℕ) :
    let b := WinternitzCollision.bridge toyWinternitzParameters
      (fun _ _ _ => Subsingleton.elim _ _)
    (TargetCollisionReduction.encodingProblem b p K).paramGen =
        toyWinternitzParameters.thf.seedGen ∧
    (TargetCollisionReduction.hashProblem b p K).numTargets = p ∧
    (TargetCollisionReduction.hashProblem b p K).numRetries = K := ⟨rfl, rfl, rfl⟩

/-- Both concrete bridge specializations apply to arbitrary adaptive source adversaries. -/
theorem checksum_bridge_bound (p K : ℕ)
    (source : TargetCollisionResistance.Adversary
      (TargetCollisionReduction.encodingProblem
        (WinternitzCollision.bridge toyWinternitzParameters
          (fun _ _ _ => Subsingleton.elim _ _)) p K)) :
    TargetCollisionResistance.advantage source ≤
      TweakableHash.SM_DT_RTCR_Advantage
        (TargetCollisionReduction.reduction
          (WinternitzCollision.bridge toyWinternitzParameters
            (fun _ _ _ => Subsingleton.elim _ _)) p K source) :=
  WinternitzCollision.advantage_le_hash toyWinternitzParameters
    (fun _ _ _ => Subsingleton.elim _ _) p K source

/-- Target-sum bridge specialization retains failed targets and the configured capacities. -/
theorem target_bridge_bound (p K : ℕ)
    (source : TargetCollisionResistance.Adversary
      (TargetCollisionReduction.encodingProblem
        (TargetSumCollision.bridge toyTargetParameters
          (fun _ _ _ => Subsingleton.elim _ _)) p K)) :
    TargetCollisionResistance.advantage source ≤
      TweakableHash.SM_DT_RTCR_Advantage
        (TargetCollisionReduction.reduction
          (TargetSumCollision.bridge toyTargetParameters
            (fun _ _ _ => Subsingleton.elim _ _)) p K source) :=
  TargetSumCollision.advantage_le_hash toyTargetParameters
    (fun _ _ _ => Subsingleton.elim _ _) p K source

/-- A one-digit zero word fails the target-sum bridge predicate at target one. -/
theorem target_single_digit_rejected :
    TargetSumCollision.accepts (v := 1) (w := 1) (target := 1) (fun _ => 0) = false := by
  decide

end IncomparableEncoding.InstanceProbe
