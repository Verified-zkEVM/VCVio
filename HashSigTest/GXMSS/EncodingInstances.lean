/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import HashSig.GXMSS.Encoding.Winternitz
public import HashSig.GXMSS.Encoding.TargetSum

/-!
# Exact instantiation convention probes

These small examples check checksum carry, distinct payloads, fixed-sum
acceptance and rejection, and an impossible target.
-/

public section

namespace GXMSS.Encoding.Probe.Instances

open GXMSS.Encoding

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

end GXMSS.Encoding.Probe.Instances
