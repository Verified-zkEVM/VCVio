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
import Mathlib.Data.List.GetD

/-!
# Winternitz checksum words

Payloads are extended by low-first digits of their complementary checksum. The shared
checksum rigidity law proves global incomparability, with the Construction 5 width.
-/

public section

namespace IncomparableEncoding.Winternitz

open IncomparableEncoding

/-- The fixed width needed for the largest complementary checksum. -/
@[expose] def checksumWidth (n₀ w : ℕ) : ℕ :=
  Nat.log (2 ^ w) (n₀ * (2 ^ w - 1)) + 1

/-- The greatest possible sum of `n₀` base-`2^w` payload digits. -/
@[expose] def maximum (n₀ w : ℕ) : ℕ := n₀ * (2 ^ w - 1)

/-- A positive bit width makes the digit radix at least two. -/
theorem one_lt_radix {w : ℕ} (hw : 0 < w) : 1 < 2 ^ w :=
  Nat.one_lt_pow (Nat.ne_of_gt hw) (by decide)

/-- Every complementary checksum fits in the selected digit width. -/
theorem maximum_lt_pow_width (n₀ w : ℕ) (hw : 0 < w) :
    maximum n₀ w < (2 ^ w) ^ checksumWidth n₀ w := by
  exact Nat.lt_pow_succ_log_self (one_lt_radix hw) (maximum n₀ w)

/-- The natural-valued sum of the bounded payload digits. -/
@[expose] def payloadSum {n₀ w : ℕ} (payload : Codeword n₀ (2 ^ w)) : ℕ :=
  ∑ i : Fin n₀, (payload i).val

/-- A payload sum never exceeds the maximum complement minuend. -/
theorem payloadSum_le_maximum {n₀ w : ℕ} (payload : Codeword n₀ (2 ^ w)) :
    payloadSum payload ≤ maximum n₀ w := by
  unfold payloadSum maximum
  calc
    (∑ i : Fin n₀, (payload i).val) ≤ ∑ _i : Fin n₀, (2 ^ w - 1) := by
      apply Finset.sum_le_sum
      intro i _
      exact Nat.le_sub_one_of_lt (payload i).isLt
    _ = n₀ * (2 ^ w - 1) := by simp

/-- The complementary checksum as an ordinary natural number. -/
@[expose] def complement {n₀ w : ℕ} (payload : Codeword n₀ (2 ^ w)) : ℕ :=
  maximum n₀ w - payloadSum payload

/-- The checksum is in the representable range for the selected width. -/
theorem complement_lt_pow_width {n₀ w : ℕ} (hw : 0 < w)
    (payload : Codeword n₀ (2 ^ w)) :
    complement payload < (2 ^ w) ^ checksumWidth n₀ w :=
  (Nat.sub_le _ _).trans_lt (maximum_lt_pow_width n₀ w hw)

/-- The low-first checksum digit at coordinate `i` is the corresponding quotient remainder. -/
@[expose] def checksum {n₀ w : ℕ} (_hw : 0 < w)
    (payload : Codeword n₀ (2 ^ w)) :
    Codeword (checksumWidth n₀ w) (2 ^ w) :=
  fun i => ⟨complement payload / (2 ^ w) ^ i.val % (2 ^ w),
    Nat.mod_lt _ (by positivity : 0 < 2 ^ w)⟩

/-- The explicit checksum coordinates agree with the canonical padded base digits. -/
theorem checksum_eq_padded_digits {n₀ w : ℕ} (hw : 0 < w)
    (payload : Codeword n₀ (2 ^ w)) (i : Fin (checksumWidth n₀ w)) :
    (checksum hw payload i).val =
      (Nat.digitsAppend (2 ^ w) (checksumWidth n₀ w) (complement payload)).getD i.val 0 := by
  exact (Nat.digitsAppend_getD _ _ _ _ (one_lt_radix hw)
    (complement_lt_pow_width hw payload)).symm

/-- The appended checksum digits decode to the exact complementary value. -/
theorem checksum_reconstruct {n₀ w : ℕ} (hw : 0 < w)
    (payload : Codeword n₀ (2 ^ w)) :
    Nat.ofDigits (2 ^ w)
        (List.ofFn fun i : Fin (checksumWidth n₀ w) => (checksum hw payload i).val) =
      complement payload := by
  let digits := Nat.digitsAppend (2 ^ w) (checksumWidth n₀ w) (complement payload)
  have hlen : digits.length = checksumWidth n₀ w :=
    Nat.length_digitsAppend (one_lt_radix hw) _ (complement_lt_pow_width hw payload)
  have hlist : (List.ofFn fun i : Fin (checksumWidth n₀ w) =>
      (checksum hw payload i).val) = digits := by
    apply List.ext_get
    · simp [hlen]
    · intro i h₁ h₂
      have hc := checksum_eq_padded_digits hw payload ⟨i, by simpa using h₁⟩
      rw [List.getD_eq_getElem digits 0 h₂] at hc
      simpa [digits] using hc
  rw [hlist]
  exact (Nat.setInvOn_digitsAppend_ofDigits (one_lt_radix hw)
    (checksumWidth n₀ w)).2 (complement_lt_pow_width hw payload)

/-- Appending the payload and its canonical complementary checksum. -/
@[expose] def word {n₀ w : ℕ} (hw : 0 < w)
    (payload : Codeword n₀ (2 ^ w)) :
    Codeword (n₀ + checksumWidth n₀ w) (2 ^ w) :=
  Fin.append payload (checksum hw payload)

/-- The checksum-word code over all bounded payloads. -/
@[expose] def checksumWordCode (n₀ w : ℕ) (hw : 0 < w) :
    Set (Codeword (n₀ + checksumWidth n₀ w) (2 ^ w)) :=
  Set.range (word (n₀ := n₀) hw)

/-- Comparability of two output words forces equality of their payloads. -/
theorem word_eq_of_le {n₀ w : ℕ} (hw : 0 < w)
    (xs ys : Codeword n₀ (2 ^ w))
    (hle : ∀ i, word hw xs i ≤ word hw ys i) : word hw xs = word hw ys := by
  have hp : ∀ i, xs i ≤ ys i := by
    intro i
    simpa [word] using hle (Fin.castAdd (checksumWidth n₀ w) i)
  have hc : ∀ i, checksum hw xs i ≤ checksum hw ys i := by
    intro i
    simpa [word] using hle (Fin.natAdd n₀ i)
  have hcomp : complement xs ≤ complement ys := by
    have hdigits : Nat.ofDigits (2 ^ w) (List.ofFn fun i => (checksum hw xs i).val) ≤
        Nat.ofDigits (2 ^ w) (List.ofFn fun i => (checksum hw ys i).val) := by
      apply Nat.ofDigits_le_of_forall₂
      apply List.forall₂_of_length_eq_of_get
      · simp
      · intro i h₁ _
        simpa using hc ⟨i, by simpa using h₁⟩
    simpa [checksum_reconstruct hw] using hdigits
  have hvalue (payload : Codeword n₀ (2 ^ w)) :
      (∑ i, (2 ^ w - 1 - (payload i).val)) = complement payload := by
    have ht := VCVio.Algorithms.ComplementaryChecksum.value_add_sum_eq (2 ^ w)
      (List.ofFn fun i => (payload i).val) (by
        intro d hd
        obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hd
        exact (payload i).isLt)
    rw [VCVio.Algorithms.ComplementaryChecksum.value_ofFn, List.sum_ofFn,
      List.length_ofFn] at ht
    dsimp [complement, maximum, payloadSum]
    omega
  have hcoords : xs = ys :=
    VCVio.Algorithms.ComplementaryChecksum.fin_eq_of_le_of_value_le xs ys hp
      (by simpa only [hvalue] using hcomp)
  exact congrArg (word hw) hcoords

/-- All distinct checksum words from bounded payloads are incomparable. -/
theorem checksumWordCode_incomparable (n₀ w : ℕ) (hw : 0 < w) :
    IncomparableCode (checksumWordCode n₀ w hw) := by
  intro x hx y hy hne
  have strict : ∀ {a b : Codeword (n₀ + checksumWidth n₀ w) (2 ^ w)},
      a ∈ checksumWordCode n₀ w hw → b ∈ checksumWordCode n₀ w hw → a ≠ b →
        ∃ i, a i < b i := by
    intro a b ha hb hab
    by_contra h
    have hle : ∀ i, b i ≤ a i := by
      intro i
      exact le_of_not_gt (fun hi => h ⟨i, hi⟩)
    rcases ha with ⟨pa, rfl⟩
    rcases hb with ⟨pb, rfl⟩
    exact hab (word_eq_of_le hw pb pa hle).symm
  exact ⟨strict hx hy hne, strict hy hx hne.symm⟩

end IncomparableEncoding.Winternitz
