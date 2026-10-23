/-
Copyright (c) 2026 Tom Wambsgans. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Wambsgans
-/

module

public import HashSig.SLHDSA.SHAKE128s.Proof.Experiment
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Tactic.NormNum

/-!
# Checksum arithmetic

These lemmas count the chain steps specified by Algorithm 8. Connecting this count to an
oracle implementation of the full verifier is a separate proof obligation.
-/

@[expose] public section

namespace SlhDsaSecurity.Checksum

theorem checksum_le (digits : MessageDigits) : checksum digits ≤ 480 := by
  calc
    _ ≤ ∑ _ : Fin messageDigits, (w - 1) :=
      Finset.sum_le_sum (fun _ _ => Nat.sub_le _ _)
    _ = 480 := by norm_num [messageDigits, n, winternitzBits, w]

theorem chainVerificationCalls_eq (digits : MessageDigits) :
    chainVerificationCalls digits =
      45 + 255 * (checksum digits / 256) + 15 * (checksum digits % 256 / 16) := by
  have h := checksum_le digits
  change checksum digits +
    (∑ i : Fin 3, (15 - (checksumDigit (checksum digits) i).val)) = _
  norm_num [Fin.sum_univ_succ, checksumDigit, checksumDigits, w, winternitzBits]
  omega

theorem chainVerificationCalls_bounds (digits : MessageDigits) :
    45 ≤ chainVerificationCalls digits ∧ chainVerificationCalls digits ≤ 510 := by
  rw [chainVerificationCalls_eq]
  have h := checksum_le digits
  omega

end SlhDsaSecurity.Checksum
