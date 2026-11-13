/-
Copyright (c) 2026 Vitalik Buterin, Nicolas Consigny, Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vitalik Buterin, Nicolas Consigny, Alexander Hicks, Matthias Meijers
-/

module
public import ToMathlib.Data.Nat.Digits

/-!
# Fixed-width big-endian radix encodings

Quotient-remainder digits have the prescribed width, including leading zeroes. Their numerical
value is the input modulo the available radix power. Reversal connects their decoder to the
shared little-endian reconstruction and its coordinatewise monotonicity law.
-/

public section

namespace VCVio.Algorithms.RadixEncoding

/-- Reconstruct a natural number from its big-endian base-`w` digit list. -/
@[expose] def fromBaseW (w : ℕ) (digits : List ℕ) : ℕ :=
  digits.foldl (fun acc d => acc * w + d) 0

/-- The empty digit list reconstructs zero. -/
@[simp]
theorem fromBaseW_nil (w : ℕ) : fromBaseW w [] = 0 := rfl

/-- Big-endian reconstruction is little-endian reconstruction of the reversed digits. -/
theorem fromBaseW_eq_ofDigits_reverse (w : ℕ) (ds : List ℕ) :
    fromBaseW w ds = Nat.ofDigits w ds.reverse :=
  (Nat.ofDigits_reverse_eq_foldl w ds).symm

/-- The leading digit has the place value determined by the remaining width. -/
@[simp]
theorem fromBaseW_cons (w d : ℕ) (ds : List ℕ) :
    fromBaseW w (d :: ds) = d * w ^ ds.length + fromBaseW w ds := by
  rw [fromBaseW_eq_ofDigits_reverse, Nat.ofDigits_reverse_cons]
  simp [fromBaseW_eq_ofDigits_reverse, Nat.add_comm, Nat.mul_comm]

/-- Concatenating digit lists shifts the first value by the width of the second list. -/
theorem fromBaseW_append (w : ℕ) (xs ys : List ℕ) :
    fromBaseW w (xs ++ ys) = fromBaseW w xs * w ^ ys.length + fromBaseW w ys := by
  rw [fromBaseW_eq_ofDigits_reverse, List.reverse_append, Nat.ofDigits_append]
  simp [fromBaseW_eq_ofDigits_reverse, Nat.add_comm, Nat.mul_comm]

/-- Coordinatewise comparison preserves big-endian numerical order. -/
theorem fromBaseW_pointwiseLE {ds1 ds2 : List ℕ} {w : ℕ}
    (hLE : List.Forall₂ (· ≤ ·) ds1 ds2) : fromBaseW w ds1 ≤ fromBaseW w ds2 := by
  rw [fromBaseW_eq_ofDigits_reverse, fromBaseW_eq_ofDigits_reverse]
  exact Nat.ofDigits_le_of_forall₂ w (List.rel_reverse hLE)

/-- The big-endian base-`w` digit list of `n` with `len` digits (most significant first). -/
@[expose] def digitsOfBaseW (n w len : ℕ) : List ℕ :=
  match len with
  | 0 => []
  | len + 1 => ((n / w ^ len) % w) :: digitsOfBaseW n w len

/-- A zero-width encoding has no digits. -/
theorem digitsOfBaseW_nil (n w : ℕ) : digitsOfBaseW n w 0 = [] := rfl

/-- Quotient-remainder encoding has exactly the requested width. -/
theorem digitsOfBaseW_length (n w len : ℕ) : (digitsOfBaseW n w len).length = len := by
  induction len with
  | zero => simp [digitsOfBaseW]
  | succ len ih => simp [digitsOfBaseW, ih]

/-- Every digit produced by `digitsOfBaseW` is a genuine base-`w` digit (`< w`). -/
theorem digitsOfBaseW_lt (n w len : ℕ) (hw : 0 < w) :
    ∀ d ∈ digitsOfBaseW n w len, d < w := by
  induction len with
  | zero => intro d hd; simp [digitsOfBaseW] at hd
  | succ len ih =>
    intro d hd
    simp only [digitsOfBaseW, List.mem_cons] at hd
    rcases hd with h | h
    · subst h; exact Nat.mod_lt _ hw
    · exact ih d h

/-- A fixed-width encoding keeps the input modulo the available radix power. -/
theorem fromBaseW_digitsOfBaseW_eq_mod (n w len : ℕ) :
    fromBaseW w (digitsOfBaseW n w len) = n % (w ^ len) := by
  induction len generalizing n with
  | zero => simp [digitsOfBaseW, fromBaseW, Nat.mod_one]
  | succ len ih =>
    simp only [digitsOfBaseW, fromBaseW_cons, digitsOfBaseW_length n w len, ih n]
    rw [Nat.mod_pow_succ, Nat.mul_comm, Nat.add_comm]

/-- Values fitting the selected width reconstruct exactly. -/
theorem fromBaseW_digitsOfBaseW_of_lt (n w len : ℕ)
    (h : n < w ^ len) : fromBaseW w (digitsOfBaseW n w len) = n := by
  rw [fromBaseW_digitsOfBaseW_eq_mod n w len]
  exact Nat.mod_eq_of_lt h

/-- Comparison of fitting big-endian digit lists reflects numerical order. -/
theorem digitsOfBaseW_pointwiseLE_imp_le {a b w len : ℕ}
    (ha : a < w ^ len) (hb : b < w ^ len)
    (hLE : List.Forall₂ (· ≤ ·) (digitsOfBaseW a w len) (digitsOfBaseW b w len)) :
    a ≤ b := by
  have ha' : fromBaseW w (digitsOfBaseW a w len) = a :=
    fromBaseW_digitsOfBaseW_of_lt a w len ha
  have hb' : fromBaseW w (digitsOfBaseW b w len) = b :=
    fromBaseW_digitsOfBaseW_of_lt b w len hb
  have hValLE : fromBaseW w (digitsOfBaseW a w len) ≤ fromBaseW w (digitsOfBaseW b w len) :=
    fromBaseW_pointwiseLE hLE
  simpa [ha', hb'] using hValLE

/-- The fixed-width digits enumerate quotient remainders from most significant to least. -/
theorem digitsOfBaseW_eq_range (n w len : ℕ) :
    digitsOfBaseW n w len =
      (List.range len).map (fun i => n / w ^ (len - 1 - i) % w) := by
  induction len with
  | zero => simp [digitsOfBaseW]
  | succ len ih =>
      rw [digitsOfBaseW, List.range_succ_eq_map]
      simp only [List.map_cons, List.map_map, ih, List.cons.injEq]
      constructor
      · congr 2
      · apply List.map_congr_left
        intro i hi
        congr 3
        omega

/-- Lookup at a bounded big-endian digit position. -/
theorem digitsOfBaseW_getElem? (n w len j : ℕ) (hj : j < len) :
    (digitsOfBaseW n w len)[j]? = some (n / w ^ (len - 1 - j) % w) := by
  rw [digitsOfBaseW_eq_range]
  simp [hj]

end VCVio.Algorithms.RadixEncoding
