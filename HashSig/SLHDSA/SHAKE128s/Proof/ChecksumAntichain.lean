/-
Copyright (c) 2026 Tom Wambsgans. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Wambsgans
-/

module

public import HashSig.SLHDSA.SHAKE128s.Proof.Checksum
public import Mathlib.Data.BitVec

/-! The standard checksum prevents obtaining a different message by advancing every chain. -/

@[expose] public section

namespace SlhDsaSecurity.Checksum

theorem encode_messageDigit (message : Digest) (i : Fin messageDigits) :
    encode message (Fin.castAdd checksumDigits i) = messageDigit message i := by
  simp only [encode, Fin.val_castAdd, dif_pos i.isLt]

theorem encode_checksumDigit (message : Digest) (i : Fin checksumDigits) :
    encode message (Fin.natAdd messageDigits i) =
      checksumDigit (checksum (messageDigit message)) i := by
  simp [encode]

theorem messageDigit_injective : Function.Injective messageDigit := by
  intro left right hdigits
  apply BitVec.eq_of_getLsbD_eq
  intro bit hbit
  have hbelow : bit < 128 := hbit
  let digit : Fin messageDigits := ⟨31 - bit / 4, by change 31 - bit / 4 < 32; omega⟩
  have hoffsetBit : bit % 4 < 4 := Nat.mod_lt bit (by decide)
  have hoffset : 4 * (messageDigits - 1 - digit.val) + bit % 4 = bit := by
    change 4 * (32 - 1 - (31 - bit / 4)) + bit % 4 = bit
    omega
  have hextract :
      left.extractLsb' (winternitzBits * (messageDigits - 1 - digit.val)) winternitzBits =
        right.extractLsb' (winternitzBits * (messageDigits - 1 - digit.val)) winternitzBits := by
    apply BitVec.toFin_injective
    exact congrFun hdigits digit
  have hlocalBit := congrArg (fun value => value.getLsbD (bit % 4)) hextract
  simpa only [BitVec.getLsbD_extractLsb', show winternitzBits = 4 from rfl,
    decide_eq_true hoffsetBit, Bool.true_and, hoffset] using hlocalBit

theorem checksum_eq_digits (csum : Nat) (hcsum : csum < w ^ checksumDigits) :
    csum = w ^ 2 * (checksumDigit csum ⟨0, by decide⟩).val +
      w * (checksumDigit csum ⟨1, by decide⟩).val +
        (checksumDigit csum ⟨2, by decide⟩).val := by
  norm_num [checksumDigit, checksumDigits, w, winternitzBits] at *
  omega

theorem checksum_le_of_digits_le {left right : Nat}
    (hleft : left < w ^ checksumDigits) (hright : right < w ^ checksumDigits)
    (hdigits : ∀ j, checksumDigit left j ≤ checksumDigit right j) : left ≤ right := by
  rw [checksum_eq_digits left hleft, checksum_eq_digits right hright]
  have h0 := hdigits ⟨0, by decide⟩
  have h1 := hdigits ⟨1, by decide⟩
  have h2 := hdigits ⟨2, by decide⟩
  rw [Fin.le_def] at h0 h1 h2
  change 16 ^ 2 * _ + 16 * _ + _ ≤ 16 ^ 2 * _ + 16 * _ + _
  omega

/-- Componentwise advancement of a valid encoding cannot change its message. -/
theorem eq_of_encode_le {left right : Digest}
    (hle : ∀ i, encode left i ≤ encode right i) : left = right := by
  have hmessage : ∀ i, (messageDigit left i).val ≤ (messageDigit right i).val := by
    intro i
    have hi := hle (Fin.castAdd checksumDigits i)
    rw [encode_messageDigit, encode_messageDigit] at hi
    exact Fin.le_def.mp hi
  have hdown : checksum (messageDigit right) ≤ checksum (messageDigit left) :=
    Finset.sum_le_sum fun i _ => Nat.sub_le_sub_left (hmessage i) _
  have hup : checksum (messageDigit left) ≤ checksum (messageDigit right) := by
    apply checksum_le_of_digits_le
      ((checksum_le _).trans_lt (by decide)) ((checksum_le _).trans_lt (by decide))
    intro i
    simpa only [encode_checksumDigit] using hle (Fin.natAdd messageDigits i)
  have hsum := le_antisymm hdown hup
  have hterms := (Finset.sum_eq_sum_iff_of_le
    (fun i (_ : i ∈ Finset.univ) => Nat.sub_le_sub_left (hmessage i) (w - 1))).mp hsum
  apply messageDigit_injective
  funext i
  apply Fin.ext
  have heq := hterms i (Finset.mem_univ i)
  have hl := (messageDigit left i).isLt
  have hr := (messageDigit right i).isLt
  change (messageDigit left i).val < 16 at hl
  change (messageDigit right i).val < 16 at hr
  change 15 - (messageDigit right i).val = 15 - (messageDigit left i).val at heq
  omega

/-- A different WOTS message necessarily needs an earlier value on some chain. -/
theorem exists_decreased_digit {signed forged : Digest} (hne : signed ≠ forged) :
    ∃ i, encode forged i < encode signed i := by
  classical
  by_contra h
  simp only [not_exists, not_lt] at h
  exact hne (eq_of_encode_le h)

end SlhDsaSecurity.Checksum
