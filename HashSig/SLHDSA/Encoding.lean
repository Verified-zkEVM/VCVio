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

/-- Failures exposed by checked fixed-width, digit, and ADRS wire decoders. -/
inductive CodecError where
  | invalidLength (expected actual : ℕ)
  | zeroDigitWidth
  | insufficientInput (requiredBits availableBits : ℕ)
  | outOfRange (widthBytes value : ℕ)
  | invalidAddressType (code : ℕ)
  | noncanonicalAddress
deriving Repr, DecidableEq

/-- `toInt(X, |X|)`: interpret a byte list as a big-endian natural number (FIPS 205 Alg 2). -/
def toInt (x : List Byte) : ℕ :=
  x.foldl (fun acc b => acc * 256 + b.toNat) 0

/-- Appending one byte performs one big-endian radix-256 step. -/
theorem toInt_append_byte (x : List Byte) (b : Byte) :
    toInt (x ++ [b]) = toInt x * 256 + b.toNat := by
  simp [toInt, List.foldl_append]

/-- A byte string of length `n` denotes an integer strictly below `256^n`. -/
theorem toInt_lt_pow (x : List Byte) : toInt x < 256 ^ x.length := by
  induction x using List.reverseRecOn with
  | nil => simp [toInt]
  | append_singleton xs b ih =>
    rw [toInt_append_byte]
    simp only [List.length_append, List.length_singleton, Nat.pow_succ]
    have hb : b.toNat < 256 := UInt8.toNat_lt b
    omega

/-- `toByte(x, len)`: big-endian `len`-byte serialization of `x` (FIPS 205 Alg 3). -/
def toByte (x len : ℕ) : List Byte :=
  (List.range len).map (fun i => UInt8.ofNat (x / 256 ^ (len - 1 - i) % 256))

@[simp] theorem toByte_length (x len : ℕ) : (toByte x len).length = len := by
  simp [toByte]

/-- Pointwise MSB-first characterization of Algorithm 3. -/
theorem toByte_bigEndian (x len : ℕ) :
    toByte x len =
      (List.range len).map (fun i => UInt8.ofNat (x / 256 ^ (len - 1 - i) % 256)) := rfl

/-- Checked Algorithm 3: reject values that do not fit instead of silently truncating them. -/
def toByteChecked (x len : ℕ) : Except CodecError (Bytes len) :=
  if x < 256 ^ len then
    .ok ⟨(toByte x len).toArray, by simp⟩
  else
    .error (.outOfRange len x)

/-- Decode a list only when its length is exactly the requested wire width. -/
def decodeExact (n : ℕ) (raw : List Byte) : Except CodecError (Bytes n) :=
  if h : raw.length = n then
    .ok ⟨raw.toArray, by simpa using h⟩
  else
    .error (.invalidLength n raw.length)

/-- Fixed-width vectors encode without adding or dropping bytes. -/
def encodeExact {n : ℕ} (bytes : Bytes n) : List Byte := bytes.toList

@[simp] theorem decodeExact_encode {n : ℕ} (bytes : Bytes n) :
    decodeExact n (encodeExact bytes) = .ok bytes := by
  simp only [decodeExact, encodeExact, Vector.length_toList, ↓reduceDIte]
  congr 1

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

/-- `base2b(X, b, outLen)`: the first `outLen` MSB-first `b`-bit digits (FIPS 205 Algorithm 4).
Normative callers satisfy `outLen*b ≤ 8*|X|`; `base2bChecked` enforces that precondition at a wire
boundary. The direct arithmetic form makes the big-endian extraction rule explicit. -/
def base2b (x : List Byte) (b outLen : ℕ) : List ℕ :=
  (List.range outLen).map (fun i =>
    toInt x / 2 ^ (8 * x.length - b * (i + 1)) % 2 ^ b)

/-- Pointwise MSB-first characterization of Algorithm 4. -/
theorem base2b_bigEndian (x : List Byte) (b outLen : ℕ) :
    base2b x b outLen = (List.range outLen).map (fun i =>
      toInt x / 2 ^ (8 * x.length - b * (i + 1)) % 2 ^ b) := rfl

@[simp] theorem base2b_length (x : List Byte) (b outLen : ℕ) :
    (base2b x b outLen).length = outLen := by
  simp [base2b]

/-- Every digit produced by `base2b` is bounded by `2^b` (it is reduced mod `2^b`). -/
theorem base2b_lt (x : List Byte) (b outLen : ℕ) :
    ∀ d ∈ base2b x b outLen, d < 2 ^ b := by
  intro d hd
  rcases List.mem_map.mp hd with ⟨i, _, rfl⟩
  exact Nat.mod_lt _ (by positivity)

/-- Reject zero-width digits and insufficient input before invoking Algorithm 4. -/
def base2bChecked (x : List Byte) (b outLen : ℕ) : Except CodecError (List ℕ) :=
  if b = 0 then
    .error .zeroDigitWidth
  else if 8 * x.length < outLen * b then
    .error (.insufficientInput (outLen * b) (8 * x.length))
  else
    .ok (base2b x b outLen)

theorem base2bChecked_eq (x : List Byte) (b outLen : ℕ)
    (hb : b ≠ 0) (hlen : outLen * b ≤ 8 * x.length) :
    base2bChecked x b outLen = .ok (base2b x b outLen) := by
  simp [base2bChecked, hb, Nat.not_lt.mpr hlen]

theorem base2bChecked_zero (x : List Byte) (outLen : ℕ) :
    base2bChecked x 0 outLen = .error .zeroDigitWidth := by
  simp [base2bChecked]

end SLHDSA
