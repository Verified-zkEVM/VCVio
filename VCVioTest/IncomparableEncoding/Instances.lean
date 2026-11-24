/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import VCVio.CryptoFoundations.IncomparableEncoding.Winternitz
public import VCVio.CryptoFoundations.IncomparableEncoding.TargetSum

/-!
# Concrete encoding instances

Small words check the checksum carry and low-first digit order, incomparability of two checksum
words, target-sum acceptance and rejection, the exact failure probability of a toy target-sum
encoding under a uniform randomizer, and the counts and coefficients of small targets.
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
    (Winternitz.checksum (w := 2) oneOne ⟨0, by decide⟩).val = 0 ∧
    (Winternitz.checksum (w := 2) oneOne ⟨1, by decide⟩).val = 1 := by
  have hrec := Winternitz.checksum_reconstruct (n₀ := 2) (w := 2) (by decide) oneOne
  have hcomp : Winternitz.complement (w := 2) oneOne = 4 := by
    decide
  simp only [checksum_width_two_two, hcomp] at hrec
  simp only [List.ofFn_succ, List.ofFn_zero, Nat.ofDigits_cons,
    Nat.ofDigits_nil, mul_zero, add_zero] at hrec
  have hzero := (Winternitz.checksum (w := 2) oneOne ⟨0, by decide⟩).isLt
  have hone := (Winternitz.checksum (w := 2) oneOne ⟨1, by decide⟩).isLt
  norm_num at hrec hzero hone
  change (Winternitz.checksum (w := 2) oneOne ⟨0, by decide⟩).val +
    4 * (Winternitz.checksum (w := 2) oneOne ⟨1, by decide⟩).val = 4 at hrec
  omega

/-- Changing the payload changes its appended word even across a checksum carry. -/
theorem distinct_checksum_words :
    Winternitz.word (w := 2) oneOne ≠ Winternitz.word (w := 2) oneTwo := by
  decide

/-- Both words belong to the all-payload checksum-word range and are incomparable. -/
theorem distinct_checksum_words_incomparable :
    IncomparableWords (Winternitz.word (w := 2) oneOne) (Winternitz.word (w := 2) oneTwo) :=
  Winternitz.checksumWordCode_incomparable 2 2 (by decide)
    ⟨oneOne, rfl⟩ ⟨oneTwo, rfl⟩ distinct_checksum_words

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

/-- The Winternitz encoding returns the hash payload with its checksum digits. -/
theorem checksum_encoding_returns_word :
    (Winternitz.encoding toyWinternitzParameters).encode true PUnit.unit false PUnit.unit =
      some (Winternitz.word oneTwo) := rfl

/-- A sum-three word belongs to the target-sum code. -/
theorem target_sum_accepts :
    oneTwo ∈ TargetSum.code 2 2 3 := by
  change TargetSum.digitSum oneTwo = 3
  decide

/-- A sum-zero word is rejected when the target is three. -/
theorem target_sum_rejects :
    zeroZero ∉ TargetSum.code 2 2 3 := by
  change TargetSum.digitSum zeroZero ≠ 3
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
    (TargetSum.encoding toyTargetParameters).encode
      PUnit.unit PUnit.unit true PUnit.unit = some oneTwo :=
  (TargetSum.encode_eq_some_iff toyTargetParameters
    PUnit.unit PUnit.unit true PUnit.unit oneTwo).2 ⟨rfl, by decide⟩

/-- A non-target hash output returns explicit failure. -/
theorem target_encoding_rejects :
    (TargetSum.encoding toyTargetParameters).encode
      PUnit.unit PUnit.unit false PUnit.unit = none := by
  rw [TargetSum.encode_eq_none_iff]
  decide

/-- Under a uniform randomizer, the toy target-sum encoding fails with probability exactly `1/2`:
randomizer `false` gives a word with digit sum zero. -/
theorem target_failureMass_uniform :
    (TargetSum.encoding toyTargetParameters).failureMass ProbCompRuntime.probComp ($ᵗ Bool)
      PUnit.unit PUnit.unit PUnit.unit = 1 / 2 := by
  let : MeasurableSpace Bool := ⊤
  rw [failureMass_eq_probability,
    ProbCompRuntime.probComp.evalDist_map _ Measurable.of_discrete,
    MeasureTheory.Measure.map_apply Measurable.of_discrete (MeasurableSet.singleton true)]
  have hpre : (fun r => ((TargetSum.encoding toyTargetParameters).encode
      PUnit.unit PUnit.unit r PUnit.unit).isNone) ⁻¹' ({true} : Set Bool) = {false} := by
    ext r
    cases r
    · simp [target_encoding_rejects]
    · simp [target_encoding_accepts]
  rw [hpre, ProbCompRuntime.probComp_evalDist,
    SampleableType.evalDist_uniformSample_singleton]
  simp

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

/-- A one-digit zero word fails the target-sum test at target one. -/
theorem target_single_digit_rejected :
    TargetSum.accepts 1 (v := 1) (radix := 2) (fun _ => 0) = false := by
  decide

end IncomparableEncoding.InstanceProbe
