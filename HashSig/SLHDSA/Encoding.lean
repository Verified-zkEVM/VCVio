/-
Copyright (c) 2026 Nicolas Consigny. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicolas Consigny
-/

module
public import HashSig.SLHDSA.Params

/-!
# SLH-DSA Integer / Byte / Base Helpers

The pure conversion helpers of FIPS 205 §4.4: `toInt` (Algorithm 2, big-endian byte string →
integer), `toByte` (Algorithm 3, integer → big-endian byte string), and `base2b`
(Algorithm 4, split a byte string into `outLen` big-endian `b`-bit digits, most significant
first). These are used by WOTS+ (`b = lg_w`) and FORS (`b = a`) to derive digit/index vectors,
and by the message-digest split (`Scheme.splitDigest`).

## References

- NIST FIPS 205, §4.4 (Algorithms 2, 3, 4)
-/

@[expose] public section


namespace SLHDSA

/-- `toInt(X, |X|)`: interpret a byte list as a big-endian natural number (FIPS 205 Alg 2). -/
def toInt (x : List Byte) : ℕ :=
  x.foldl (fun acc b => acc * 256 + b.toNat) 0

/-- `toByte(x, len)`: big-endian `len`-byte serialization of `x` (FIPS 205 Alg 3). -/
def toByte (x len : ℕ) : List Byte :=
  (List.range len).map (fun i => UInt8.ofNat (x / 256 ^ (len - 1 - i) % 256))

/-- Consume bytes from the front of `inp` into the `(total, bits)` accumulator until at least
`b` bits are buffered (the inner `while` of `base2b`). Returns the leftover input and the
updated accumulator. -/
def base2bFill (b : ℕ) : List Byte → ℕ → ℕ → (List Byte × ℕ × ℕ)
  | [], total, bits => ([], total, bits)
  | x :: xs, total, bits =>
      if b ≤ bits then (x :: xs, total, bits)
      else base2bFill b xs (total * 256 + x.toNat) (bits + 8)

/-- Emit `out` big-endian `b`-bit digits, threading the `(total, bits)` bit buffer. -/
def base2bGo (b : ℕ) : ℕ → List Byte → ℕ → ℕ → List ℕ
  | 0, _, _, _ => []
  | out + 1, inp, total, bits =>
      let r := base2bFill b inp total bits
      let bits' := r.2.2 - b
      ((r.2.1 >>> bits') % 2 ^ b) :: base2bGo b out r.1 r.2.1 bits'

/-- `base2b(X, b, outLen)`: the first `outLen` big-endian `b`-bit digits of the byte string `X`
(FIPS 205 Algorithm 4). Requires `X` to have at least `⌈outLen·b / 8⌉` bytes; missing bits read
as zero. -/
def base2b (x : List Byte) (b outLen : ℕ) : List ℕ :=
  base2bGo b outLen x 0 0

@[simp] theorem base2b_length (x : List Byte) (b outLen : ℕ) :
    (base2b x b outLen).length = outLen := by
  unfold base2b
  suffices h : ∀ (out : ℕ) (inp : List Byte) (total bits : ℕ),
      (base2bGo b out inp total bits).length = out by
    exact h outLen x 0 0
  intro out
  induction out with
  | zero => intro inp total bits; rfl
  | succ out ih => intro inp total bits; simp [base2bGo, ih]

/-- Every digit produced by `base2b` is bounded by `2^b` (it is reduced mod `2^b`). -/
theorem base2b_lt (x : List Byte) (b outLen : ℕ) :
    ∀ d ∈ base2b x b outLen, d < 2 ^ b := by
  unfold base2b
  suffices h : ∀ (out : ℕ) (inp : List Byte) (total bits : ℕ),
      ∀ d ∈ base2bGo b out inp total bits, d < 2 ^ b by
    exact h outLen x 0 0
  intro out
  induction out with
  | zero => intro inp total bits d hd; simp [base2bGo] at hd
  | succ out ih =>
    intro inp total bits d hd
    simp only [base2bGo, List.mem_cons] at hd
    rcases hd with h | h
    · subst h; exact Nat.mod_lt _ (by positivity)
    · exact ih _ _ _ d h

/-! ### Injectivity of the full-width two-bit encoding

The supported SHA2-128-24 WOTS instance uses `b = 2` and emits four digits for every input byte.
The next lemmas prove that this exact full-width specialization loses no information. -/

private theorem base2bFill_of_le_bits (b bits total : ℕ) (xs : List Byte) (h : b ≤ bits) :
    base2bFill b xs total bits = (xs, total, bits) := by
  cases xs <;> simp [base2bFill, h]

/-- The four most-significant-first two-bit digits of one byte. -/
def byteTwoBitDigits (x : Byte) : List ℕ :=
  [x.toNat >>> 6 % 4, x.toNat >>> 4 % 4, x.toNat >>> 2 % 4, x.toNat % 4]

/-- Four two-bit digits determine the original byte. -/
theorem byteTwoBitDigits_injective : Function.Injective byteTwoBitDigits := by
  intro x y h
  simp only [byteTwoBitDigits, List.cons.injEq] at h
  rcases h with ⟨h6, h4, h2, h0⟩
  apply UInt8.toNat_inj.mp
  rw [Nat.shiftRight_eq_div_pow] at h6 h4 h2
  norm_num at h6 h4 h2
  have hx := x.toNat_lt
  have hy := y.toNat_lt
  omega

private theorem base2bGo_two_chunk (n total : ℕ) (x : Byte) (xs : List Byte) :
    base2bGo 2 (4 * (n + 1)) (x :: xs) total 0 =
      byteTwoBitDigits x ++ base2bGo 2 (4 * n) xs (total * 256 + x.toNat) 0 := by
  simp only [Nat.mul_add, Nat.mul_one]
  simp only [base2bGo, base2bFill, nonpos_iff_eq_zero, OfNat.ofNat_ne_zero, ↓reduceIte,
    zero_add, Nat.reduceLeDiff, base2bFill_of_le_bits, Nat.reduceSub, Nat.reducePow,
    Std.le_refl, tsub_self, Nat.shiftRight_zero, byteTwoBitDigits, List.cons_append,
    List.nil_append, List.cons.injEq, and_true]
  repeat' rw [Nat.shiftRight_eq_div_pow]
  norm_num
  have hx := x.toNat_lt
  constructor
  · omega
  constructor
  · omega
  constructor
  · omega
  · omega

private theorem base2bGo_two_injective_of_length (n total : ℕ) :
    ∀ xs ys : List Byte, xs.length = n → ys.length = n →
      base2bGo 2 (4 * n) xs total 0 = base2bGo 2 (4 * n) ys total 0 → xs = ys := by
  induction n generalizing total with
  | zero =>
      intro xs ys hxs hys _
      rw [List.length_eq_zero_iff] at hxs hys
      subst xs
      subst ys
      rfl
  | succ n ih =>
      intro xs ys hxs hys hout
      cases xs with
      | nil => simp at hxs
      | cons x xs =>
      cases ys with
      | nil => simp at hys
      | cons y ys =>
      rw [base2bGo_two_chunk, base2bGo_two_chunk] at hout
      have hdigits : byteTwoBitDigits x = byteTwoBitDigits y := by
        have htake := congrArg (List.take 4) hout
        simpa [byteTwoBitDigits] using htake
      have hxy : x = y := byteTwoBitDigits_injective hdigits
      subst y
      have hrest :
          base2bGo 2 (4 * n) xs (total * 256 + x.toNat) 0 =
            base2bGo 2 (4 * n) ys (total * 256 + x.toNat) 0 := by
        exact List.append_cancel_left hout
      have hxs' : xs.length = n := by simpa using hxs
      have hys' : ys.length = n := by simpa using hys
      rw [ih (total := total * 256 + x.toNat) xs ys hxs' hys' hrest]

/-- `base2b xs 2 (4 * n)` is injective on byte lists of length `n`: it emits the complete
two-bit representation of every byte and therefore performs no truncation. -/
theorem base2b_two_injective_of_length (n : ℕ) :
    Set.InjOn (fun xs : List Byte => base2b xs 2 (4 * n)) {xs | xs.length = n} := by
  intro xs hxs ys hys hout
  exact base2bGo_two_injective_of_length n 0 xs ys hxs hys hout

end SLHDSA
