/-
Copyright (c) 2026 Vitalik Buterin, Nicolas Consigny. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vitalik Buterin, Nicolas Consigny, Alexander Hicks
-/

module
public import VCVio.Algorithms.ComplementaryChecksum.Basic
public import VCVio.Algorithms.RadixEncoding

/-!
# WOTS+ checksum incomparability

The FIPS 205 checksum word appends fixed-width big-endian checksum digits to its message
digits. The shared decoder-parametric checksum law establishes that distinct bounded payloads
produce incomparable words. `HashSig.SLHDSA.WotsInjectivity` combines this law with the
injectivity of the FIPS message-digit map.
-/

@[expose] public section

namespace SLHDSA.WotsChecksum

open List (Forall₂)
open VCVio.Algorithms
open VCVio.Algorithms.RadixEncoding

/-- The WOTS+ complementary checksum over message digits. -/
def wotsChecksumValue (w : ℕ) (digits : List ℕ) : ℕ :=
  ComplementaryChecksum.value w digits

/-- Bounded message digits give a checksum no larger than `l1 * (w - 1)`. -/
theorem wotsChecksumValue_le {digits : List ℕ} {w l1 : ℕ}
    (hLen : digits.length = l1) (hBound : ∀ d ∈ digits, d < w) :
    wotsChecksumValue w digits ≤ l1 * (w - 1) := by
  calc
    _ ≤ ComplementaryChecksum.value w digits + digits.sum := Nat.le_add_right _ _
    _ = digits.length * (w - 1) := ComplementaryChecksum.value_add_sum_eq w digits hBound
    _ = l1 * (w - 1) := by rw [hLen]

/-- Message digits followed by the fixed-width big-endian checksum digits. The message length
is carried for the FIPS parameter interface. -/
def wotsFullDigits (dig : List ℕ) (w _l1 l2 : ℕ) : List ℕ :=
  dig ++ digitsOfBaseW (wotsChecksumValue w dig) w l2

/-- The full word has the prescribed payload and checksum lengths. -/
theorem wotsFullDigits_length (dig : List ℕ) (w l1 l2 : ℕ)
    (hLen : dig.length = l1) : (wotsFullDigits dig w l1 l2).length = l1 + l2 := by
  simp [wotsFullDigits, hLen, digitsOfBaseW_length]

/-- Comparing two FIPS checksum words forces equality of their bounded payloads. -/
theorem wots_fullDigits_pointwiseLE_imp_dig_eq
    {dig1 dig2 : List ℕ} {w l1 l2 : ℕ}
    (hLen1 : dig1.length = l1) (hLen2 : dig2.length = l1)
    (hBound1 : ∀ d ∈ dig1, d < w) (hBound2 : ∀ d ∈ dig2, d < w)
    (hL2suff : l1 * (w - 1) < w ^ l2)
    (hLE : Forall₂ (· ≤ ·)
      (wotsFullDigits dig1 w l1 l2) (wotsFullDigits dig2 w l1 l2)) : dig1 = dig2 := by
  apply ComplementaryChecksum.eq_of_append_le
    (fun n => digitsOfBaseW n w l2) (fromBaseW w)
    (hLen1.trans hLen2.symm) hBound1 hBound2
    (fun h => fromBaseW_pointwiseLE h) _ _ hLE
  · apply fromBaseW_digitsOfBaseW_of_lt
    have hb : ComplementaryChecksum.value w dig1 ≤ l1 * (w - 1) := by
      simpa only [hLen1] using ComplementaryChecksum.value_le w dig1
    exact hb.trans_lt hL2suff
  · apply fromBaseW_digitsOfBaseW_of_lt
    have hb : ComplementaryChecksum.value w dig2 ≤ l1 * (w - 1) := by
      simpa only [hLen2] using ComplementaryChecksum.value_le w dig2
    exact hb.trans_lt hL2suff

/-- For distinct message-digit vectors, neither full WOTS+ digit vector is pointwise `≤` the
other: the WOTS+ encoding is incomparable, which is the combinatorial obstruction to
chain-advancing forgeries. -/
theorem wots_fullDigits_incomparable
    {dig1 dig2 : List ℕ} {w l1 l2 : ℕ}
    (hLen1 : dig1.length = l1) (hLen2 : dig2.length = l1)
    (hBound1 : ∀ d ∈ dig1, d < w) (hBound2 : ∀ d ∈ dig2, d < w)
    (hL2suff : l1 * (w - 1) < w ^ l2)
    (hNeq : dig1 ≠ dig2) :
    ¬ Forall₂ (· ≤ ·) (wotsFullDigits dig1 w l1 l2) (wotsFullDigits dig2 w l1 l2) ∧
    ¬ Forall₂ (· ≤ ·) (wotsFullDigits dig2 w l1 l2) (wotsFullDigits dig1 w l1 l2) := by
  refine ⟨fun h => hNeq ?_, fun h => hNeq ?_⟩
  · exact wots_fullDigits_pointwiseLE_imp_dig_eq hLen1 hLen2 hBound1 hBound2 hL2suff h
  · exact (wots_fullDigits_pointwiseLE_imp_dig_eq hLen2 hLen1 hBound2 hBound1 hL2suff h).symm

end SLHDSA.WotsChecksum
