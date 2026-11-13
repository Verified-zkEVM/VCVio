/-
Copyright (c) 2026 Vitalik Buterin, Nicolas Consigny, Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vitalik Buterin, Nicolas Consigny, Alexander Hicks, Matthias Meijers
-/

module
public import ToMathlib.Data.List.Forall2
public import Mathlib.Data.List.OfFn
public import Mathlib.Algebra.BigOperators.Fin

/-!
# Complementary-checksum incomparability

Advancing every payload coordinate decreases its complementary checksum. Appending checksum
digits prevents comparable distinct payloads whenever their decoder reconstructs that checksum
and is monotone for the chosen digit order. The decoder can use either endian convention.
-/

public section

namespace VCVio.Algorithms.ComplementaryChecksum

/-- Sum the complements of the payload digits in radix `base`. -/
@[expose] def value (base : ℕ) (digits : List ℕ) : ℕ :=
  (digits.map (fun d => base - 1 - d)).sum

/-- Append a chosen representation of the complementary checksum to its payload. -/
@[expose] def append (encode : ℕ → List ℕ) (base : ℕ) (digits : List ℕ) : List ℕ :=
  digits ++ encode (value base digits)

/-- A finite tuple's checksum is the sum of its coordinate complements. -/
theorem value_ofFn (base : ℕ) {n : ℕ} (digits : Fin n → ℕ) :
    value base (List.ofFn digits) = ∑ i, (base - 1 - digits i) := by
  simp [value, List.sum_ofFn]

/-- The complementary checksum is bounded by the number of coordinates times the top digit. -/
theorem value_le (base : ℕ) (digits : List ℕ) : value base digits ≤ digits.length * (base - 1) := by
  unfold value
  simpa [nsmul_eq_mul] using
    List.sum_le_length_nsmul (digits.map (fun d => base - 1 - d)) (base - 1)
      (fun d hd => by
        obtain ⟨x, _, rfl⟩ := List.mem_map.mp hd
        exact Nat.sub_le _ _)

/-- For bounded payload digits, the checksum and payload sum have a fixed total. -/
theorem value_add_sum_eq (base : ℕ) (digits : List ℕ)
    (hbound : ∀ d ∈ digits, d < base) :
    value base digits + digits.sum = digits.length * (base - 1) := by
  induction digits with
  | nil => simp [value]
  | cons d ds ih =>
    have hd := hbound d (by simp)
    have ht := ih (fun x hx => hbound x (by simp [hx]))
    simp only [value, List.map_cons, List.sum_cons, List.length_cons, Nat.succ_mul] at *
    omega

/-- Pointwise payload advancement and a nondecreasing checksum force payload equality. -/
theorem eq_of_le_of_value_le {xs ys : List ℕ} {base : ℕ}
    (hle : List.Forall₂ (· ≤ ·) xs ys)
    (hxs : ∀ d ∈ xs, d < base) (hys : ∀ d ∈ ys, d < base)
    (hvalue : value base xs ≤ value base ys) : xs = ys := by
  apply List.Forall₂.eq_of_sum_eq hle
  have hx := value_add_sum_eq base xs hxs
  have hy := value_add_sum_eq base ys hys
  have hlen := hle.length_eq
  rw [hlen] at hx
  have hsum := hle.sum_le_sum
  omega

/-- Decoder-parametric checksum words are incomparable: a comparison of two words already
forces equality of their payloads. Reconstruction is needed only for these two checksums. -/
theorem eq_of_append_le (encode : ℕ → List ℕ) (decode : List ℕ → ℕ)
    {xs ys : List ℕ} {base : ℕ} (hlen : xs.length = ys.length)
    (hxs : ∀ d ∈ xs, d < base) (hys : ∀ d ∈ ys, d < base)
    (hdecode : ∀ {as bs}, List.Forall₂ (· ≤ ·) as bs → decode as ≤ decode bs)
    (hroundx : decode (encode (value base xs)) = value base xs)
    (hroundy : decode (encode (value base ys)) = value base ys)
    (hle : List.Forall₂ (· ≤ ·) (append encode base xs) (append encode base ys)) : xs = ys := by
  have hprefix : List.Forall₂ (· ≤ ·) xs ys := by
    simpa [append, hlen] using List.forall₂_take_append _ _ _ hle
  have hsuffix : List.Forall₂ (· ≤ ·) (encode (value base xs)) (encode (value base ys)) := by
    simpa [append, hlen] using List.forall₂_drop_append _ _ _ hle
  apply eq_of_le_of_value_le hprefix hxs hys
  rw [← hroundx, ← hroundy]
  exact hdecode hsuffix

/-- Finite bounded payloads satisfy the same checksum rigidity law. -/
theorem fin_eq_of_le_of_value_le {n base : ℕ} (xs ys : Fin n → Fin base)
    (hle : ∀ i, xs i ≤ ys i)
    (hvalue : (∑ i, (base - 1 - (xs i).val)) ≤ ∑ i, (base - 1 - (ys i).val)) : xs = ys := by
  have hlist : (List.ofFn fun i => (xs i).val) = List.ofFn fun i => (ys i).val := by
    apply eq_of_le_of_value_le (base := base)
    · apply List.forall₂_of_length_eq_of_get
      · simp
      · intro i hi _
        simpa using hle ⟨i, by simpa using hi⟩
    · intro d hd
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hd
      exact (xs i).isLt
    · intro d hd
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hd
      exact (ys i).isLt
    · simpa only [value_ofFn] using hvalue
  funext i
  exact Fin.ext (congrFun (List.ofFn_injective hlist) i)

end VCVio.Algorithms.ComplementaryChecksum
