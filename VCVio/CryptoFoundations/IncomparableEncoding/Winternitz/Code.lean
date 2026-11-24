/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import VCVio.CryptoFoundations.IncomparableEncoding.Basic
public import VCVio.Algorithms.ComplementaryChecksum.Basic
public import ToMathlib.Data.Nat.Digits
public import Mathlib.Data.Nat.Log

/-!
# Winternitz checksum words

A Winternitz word is a payload of `n₀` base-`2^w` digits followed by the low-first digits of its
complementary checksum. The checksum has `checksumWidth n₀ w` digits, as in Construction 5 of
DKKW25. `checksumWordCode_incomparable` shows that all such words form one incomparable code,
using the checksum rigidity law of `VCVio.Algorithms.ComplementaryChecksum`.

## References

- Drake, Khovratovich, Kudinov and Wagner, *Hash-Based Multi-Signatures for Post-Quantum Ethereum*,
  [ePrint 2025/055](https://eprint.iacr.org/2025/055), Construction 5.
-/

public section

namespace IncomparableEncoding.Winternitz

open IncomparableEncoding VCVio.Algorithms

/-- The greatest possible sum of `n₀` base-`2^w` payload digits. -/
@[expose] def maximum (n₀ w : ℕ) : ℕ := n₀ * (2 ^ w - 1)

/-- The number of base-`2^w` digits needed to write `maximum n₀ w`. -/
@[expose] def checksumWidth (n₀ w : ℕ) : ℕ :=
  Nat.log (2 ^ w) (maximum n₀ w) + 1

/-- A positive bit width makes the digit radix at least two. -/
theorem one_lt_radix {w : ℕ} (hw : 0 < w) : 1 < 2 ^ w :=
  Nat.one_lt_pow (Nat.ne_of_gt hw) (by decide)

/-- Every complementary checksum fits in the selected digit width. -/
theorem maximum_lt_pow_width (n₀ w : ℕ) (hw : 0 < w) :
    maximum n₀ w < (2 ^ w) ^ checksumWidth n₀ w :=
  Nat.lt_pow_succ_log_self (one_lt_radix hw) (maximum n₀ w)

/-- The sum of the payload digits. -/
@[expose] def payloadSum {n₀ w : ℕ} (payload : Codeword n₀ (2 ^ w)) : ℕ :=
  ∑ i : Fin n₀, (payload i).val

/-- The complementary checksum `maximum n₀ w - payloadSum payload`. -/
@[expose] def complement {n₀ w : ℕ} (payload : Codeword n₀ (2 ^ w)) : ℕ :=
  maximum n₀ w - payloadSum payload

/-- The complement is the shared complementary checksum `ComplementaryChecksum.value` of the
payload digits. -/
theorem complement_eq_value {n₀ w : ℕ} (payload : Codeword n₀ (2 ^ w)) :
    complement payload =
      ComplementaryChecksum.value (2 ^ w) (List.ofFn fun i => (payload i).val) := by
  have h := ComplementaryChecksum.value_add_sum_eq (2 ^ w)
    (List.ofFn fun i => (payload i).val) (by
      intro d hd
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hd
      exact (payload i).isLt)
  rw [List.sum_ofFn, List.length_ofFn] at h
  simp only [complement, maximum, payloadSum]
  omega

/-- The checksum is in the representable range for the selected width. -/
theorem complement_lt_pow_width {n₀ w : ℕ} (hw : 0 < w)
    (payload : Codeword n₀ (2 ^ w)) :
    complement payload < (2 ^ w) ^ checksumWidth n₀ w :=
  (Nat.sub_le _ _).trans_lt (maximum_lt_pow_width n₀ w hw)

/-- The checksum digit at coordinate `i` is digit `i` of the complement, counted from the low end.
-/
@[expose] def checksum {n₀ w : ℕ} (payload : Codeword n₀ (2 ^ w)) :
    Codeword (checksumWidth n₀ w) (2 ^ w) :=
  fun i => ⟨complement payload / (2 ^ w) ^ i.val % (2 ^ w),
    Nat.mod_lt _ (by positivity : 0 < 2 ^ w)⟩

/-- The checksum digits are the padded low-first base-`2^w` digits of the complement. -/
theorem checksum_eq_padded_digits {n₀ w : ℕ} (hw : 0 < w)
    (payload : Codeword n₀ (2 ^ w)) :
    (List.ofFn fun i => (checksum payload i).val) =
      Nat.digitsAppend (2 ^ w) (checksumWidth n₀ w) (complement payload) :=
  (Nat.digitsAppend_eq_ofFn _ _ _ (one_lt_radix hw) (complement_lt_pow_width hw payload)).symm

/-- The checksum digits decode to the complement. -/
theorem checksum_reconstruct {n₀ w : ℕ} (hw : 0 < w)
    (payload : Codeword n₀ (2 ^ w)) :
    Nat.ofDigits (2 ^ w) (List.ofFn fun i => (checksum payload i).val) =
      complement payload := by
  rw [checksum_eq_padded_digits hw]
  exact (Nat.setInvOn_digitsAppend_ofDigits (one_lt_radix hw) _).2
    (complement_lt_pow_width hw payload)

/-- The payload followed by its checksum digits. -/
@[expose] def word {n₀ w : ℕ} (payload : Codeword n₀ (2 ^ w)) :
    Codeword (n₀ + checksumWidth n₀ w) (2 ^ w) :=
  Fin.append payload (checksum payload)

/-- The code of all checksum words, one for each payload. -/
@[expose] def checksumWordCode (n₀ w : ℕ) : Set (Codeword (n₀ + checksumWidth n₀ w) (2 ^ w)) :=
  Set.range (word (n₀ := n₀) (w := w))

/-- If one checksum word is coordinatewise at most another, the two words are equal. -/
theorem word_eq_of_le {n₀ w : ℕ} (hw : 0 < w)
    (xs ys : Codeword n₀ (2 ^ w))
    (hle : ∀ i, word xs i ≤ word ys i) : word xs = word ys := by
  have hp : ∀ i, xs i ≤ ys i := by
    intro i
    simpa [word] using hle (Fin.castAdd (checksumWidth n₀ w) i)
  have hc : ∀ i, checksum xs i ≤ checksum ys i := by
    intro i
    simpa [word] using hle (Fin.natAdd n₀ i)
  have hcomp : complement xs ≤ complement ys := by
    rw [← checksum_reconstruct hw xs, ← checksum_reconstruct hw ys]
    apply Nat.ofDigits_le_of_forall₂
    apply List.forall₂_of_length_eq_of_get
    · simp
    · intro i h₁ _
      simpa using hc ⟨i, by simpa using h₁⟩
  rw [complement_eq_value, complement_eq_value, ComplementaryChecksum.value_ofFn,
    ComplementaryChecksum.value_ofFn] at hcomp
  exact congrArg word (ComplementaryChecksum.fin_eq_of_le_of_value_le xs ys hp hcomp)

/-- Distinct checksum words are incomparable. -/
theorem checksumWordCode_incomparable (n₀ w : ℕ) (hw : 0 < w) :
    IncomparableCode (checksumWordCode n₀ w) := by
  have strict : ∀ {a b : Codeword (n₀ + checksumWidth n₀ w) (2 ^ w)},
      a ∈ checksumWordCode n₀ w → b ∈ checksumWordCode n₀ w → a ≠ b → ∃ i, a i < b i := by
    rintro _ _ ⟨pa, rfl⟩ ⟨pb, rfl⟩ hab
    by_contra h
    push Not at h
    exact hab (word_eq_of_le hw pb pa h).symm
  intro x hx y hy hne
  exact ⟨strict hx hy hne, strict hy hx hne.symm⟩

end IncomparableEncoding.Winternitz
