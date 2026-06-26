/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import Batteries.Data.ByteArray
import Batteries.Data.Array.Lemmas
import LatticeCrypto.Falcon.Arithmetic

/-!
# Concrete Falcon Encoding

Executable compress/decompress for Falcon signature polynomials (Golomb-Rice style),
plus 14-bit public key encoding/decoding for `q = 12289`.

## Signature Compression (comp_encode / comp_decode)

Each coefficient `x` with `|x| ≤ 2047` is encoded as:
- 1 sign bit (0 = positive, 1 = negative)
- 7 low bits of `|x|`
- unary-coded high bits: `(|x| >> 7)` zero bits followed by a `1` bit

This is a variable-length code: small coefficients use ~9 bits, larger ones up to ~24 bits.

## Public Key Encoding

Each coefficient of `h ∈ R_q` takes exactly 14 bits (since `q = 12289 < 2^14`),
packed 4 coefficients into 7 bytes.

## References

- c-fn-dsa: `codec.c` (comp_encode, comp_decode, mqpoly_encode, mqpoly_decode)
- Falcon specification v1.2, Section 3.12 (Algorithms 17–18)
-/


namespace Falcon.Concrete

open Falcon

/-! ## Signature compression -/

/-- Compress a Falcon signature polynomial into at most `dlen` bytes. -/
def compress (n : ℕ) (s : IntPoly n) (dlen : ℕ) : Option (List UInt8) := Id.run do
  let mut acc : UInt32 := 0
  let mut accLen : UInt32 := 0
  let mut out : Array UInt8 := #[]
  for i in [0:n] do
    let x : Int := s[i]!
    if x < -2047 || x > 2047 then
      return none
    let sw : UInt32 := if x < 0 then 0xFFFFFFFF else 0
    let w : UInt32 := x.natAbs.toUInt32
    acc := (acc <<< 8) ||| ((sw &&& 0x80) ||| (w &&& 0x7F))
    accLen := accLen + 8
    let wh := (w >>> 7).toNat + 1
    acc := (acc <<< wh.toUInt32) ||| 1
    accLen := accLen + wh.toUInt32
    while accLen ≥ 8 do
      accLen := accLen - 8
      if out.size ≥ dlen then
        return none
      out := out.push (acc >>> accLen).toUInt8
  if accLen > 0 then
    if out.size ≥ dlen then
      return none
    out := out.push (acc <<< (8 - accLen)).toUInt8
  while out.size < dlen do
    out := out.push 0
  return some out.toList

/-- Decompress a Falcon signature polynomial from its compressed byte representation.

Falcon signatures are fixed-length: `compress` pads its output to exactly `dlen` bytes, so a
canonical compressed `s` has length exactly `dlen`. We reject any input whose length differs from
`dlen` (not merely shorter ones): accepting trailing bytes would make signatures **malleable** —
a verifier reads only the first `dlen` bytes, so appended garbage would verify identically
(B9 / ENC-3). This enforces the spec's fixed-bitlength requirement (Falcon §3.11.2–3 / FN-DSA). -/
def decompress (n : ℕ) (d : List UInt8) (dlen : ℕ) : Option (IntPoly n) := Id.run do
  if d.length ≠ dlen then return none
  let bytes := d.toArray
  let mut acc : UInt32 := 0
  let mut accLen : UInt32 := 0
  let mut j := 0
  let mut result : Array ℤ := Array.replicate n 0
  for i in [0:n] do
    if j ≥ dlen then return none
    acc := (acc <<< 8) ||| bytes[j]!.toUInt32
    j := j + 1
    let full := acc >>> accLen
    let t := (full >>> 7) &&& 1
    let mut m : UInt32 := full &&& 0x7F
    let mut done := false
    while !done do
      if accLen == 0 then
        if j ≥ dlen then return none
        acc := (acc <<< 8) ||| bytes[j]!.toUInt32
        j := j + 1
        accLen := 8
      accLen := accLen - 1
      if ((acc >>> accLen) &&& 1) != 0 then
        done := true
      else
        m := m + 0x80
        if m > 2047 then return none
    if m == 0 && t != 0 then return none
    let val : UInt32 := (m ^^^ (0 - t)) + t
    let signedVal : ℤ :=
      if val &&& 0x80000000 != 0 then -(((~~~val) + 1).toNat : ℤ)
      else (val.toNat : ℤ)
    result := result.set! i signedVal
  if accLen > 0 then
    if (acc &&& ((1 <<< accLen) - 1)) != 0 then
      return none
  while j < dlen do
    if bytes[j]! != 0 then return none
    j := j + 1
  return some (Vector.ofFn fun ⟨i, _⟩ => result.getD i 0)

/-! ## Public key encoding (14 bits per coefficient) -/

/-- The FN-DSA public-key header byte for a given `logn`. -/
@[inline] def publicKeyHeader (logn : Nat) : UInt8 :=
  (0x00 + logn).toUInt8

/-- Encode a Falcon public key polynomial using the packed 14-bit coefficient format. -/
def pkEncode (n : ℕ) (h : Rq n) : ByteArray := Id.run do
  if n % 4 != 0 then
    panic! s!"Falcon public-key encoding requires n divisible by 4, got {n}"
  let mut out := ByteArray.empty
  for b in [0:n / 4] do
    let i := 4 * b
    let h0 := (h[i]!).val
    let h1 := (h[i+1]!).val
    let h2 := (h[i+2]!).val
    let h3 := (h[i+3]!).val
    out := out.push (h0 >>> 6).toUInt8
    out := out.push ((h0 <<< 2) ||| (h1 >>> 12)).toUInt8
    out := out.push (h1 >>> 4).toUInt8
    out := out.push ((h1 <<< 4) ||| (h2 >>> 10)).toUInt8
    out := out.push (h2 >>> 2).toUInt8
    out := out.push ((h2 <<< 6) ||| (h3 >>> 8)).toUInt8
    out := out.push h3.toUInt8
  return out

/-- Decode a Falcon public key polynomial from the packed 14-bit coefficient format. -/
def pkDecode (n : ℕ) (d : ByteArray) : Option (Rq n) := Id.run do
  if n % 4 != 0 then return none
  let needed := 7 * n / 4
  if d.size < needed then return none
  let mut result : Array Coeff := Array.replicate n 0
  for b in [0:n / 4] do
    let i := 4 * b
    let j := 7 * b
    let d0 := d[j]!.toNat
    let d1 := d[j+1]!.toNat
    let d2 := d[j+2]!.toNat
    let d3 := d[j+3]!.toNat
    let d4 := d[j+4]!.toNat
    let d5 := d[j+5]!.toNat
    let d6 := d[j+6]!.toNat
    let h0 := (d0 <<< 6) ||| (d1 >>> 2)
    let h1 := ((d1 <<< 12) ||| (d2 <<< 4) ||| (d3 >>> 4)) &&& 0x3FFF
    let h2 := ((d3 <<< 10) ||| (d4 <<< 2) ||| (d5 >>> 6)) &&& 0x3FFF
    let h3 := ((d5 <<< 8) ||| d6) &&& 0x3FFF
    if h0 ≥ modulus || h1 ≥ modulus || h2 ≥ modulus || h3 ≥ modulus then
      return none
    result := result.set! i (h0 : Coeff)
    result := result.set! (i+1) (h1 : Coeff)
    result := result.set! (i+2) (h2 : Coeff)
    result := result.set! (i+3) (h3 : Coeff)
  return some (Vector.ofFn fun ⟨i, _⟩ => result.getD i 0)

/-- External public-key bytes used by FN-DSA verification and raw-message hashing:
one header byte followed by the packed 14-bit coefficient encoding. -/
def publicKeyBytes (logn : Nat) {n : ℕ} (h : Rq n) : ByteArray :=
  ByteArray.mk #[publicKeyHeader logn] ++ pkEncode n h

/-! ## Full signature encoding/decoding -/

/-- Encode a Falcon signature as header, salt, and compressed `s₂` bytes. -/
def sigEncode (salt : Bytes 40) (compSig : List UInt8) (logn : ℕ) : ByteArray :=
  let header : UInt8 := (0x30 + logn).toUInt8
  let saltBA := ByteArray.mk salt.toArray
  let compBA := ByteArray.mk compSig.toArray
  ByteArray.mk #[header] ++ saltBA ++ compBA

/-- Decode a Falcon signature into its salt and compressed `s₂` bytes. -/
def sigDecode (d : ByteArray) (logn : ℕ) : Option (Bytes 40 × List UInt8) := Id.run do
  if d.size < 42 then return none
  let header := d[0]!
  if header != (0x30 + logn).toUInt8 then return none
  let salt : Bytes 40 := Vector.ofFn fun ⟨i, _⟩ => d[i + 1]!
  let comp := (d.extract 41 d.size).toList
  return some (salt, comp)

@[simp] theorem sigDecode_sigEncode_nil (salt : Bytes 40) (logn : ℕ) :
    sigDecode (sigEncode salt [] logn) logn = none := by
  cases salt with
  | mk xs hxs =>
      have hsalt : ({ data := xs } : ByteArray).size = 40 := by
        simpa using hxs
      have hone : ({ data := #[48 + UInt8.ofNat logn] } : ByteArray).size = 1 := rfl
      have hempty : ({ data := #[] } : ByteArray).size = 0 := rfl
      simp [sigDecode, sigEncode, hsalt, hone, hempty]

/-- The accumulator loop underlying `ByteArray.toList` reverses its accumulator onto the
remaining bytes, so the full traversal recovers the underlying array as a list. -/
private theorem toList_loop_eq (a : ByteArray) :
    ∀ i (acc : List UInt8), ByteArray.toList.loop a i acc
      = acc.reverse ++ (a.data.toList.drop i) := by
  intro i acc
  fun_induction ByteArray.toList.loop a i acc with
  | case1 i acc h ih =>
      rw [ih]
      have hi : i < a.data.toList.length := by rw [Array.length_toList]; exact h
      rw [List.drop_eq_getElem_cons hi]
      simp only [List.reverse_cons, List.append_assoc, List.singleton_append]
      congr 2
      cases a with
      | mk bs =>
        change bs[i]! = _
        rw [getElem!_pos bs i (show i < bs.size from h), Array.getElem_toList]
  | case2 i acc h =>
      have : a.data.toList.length ≤ i := by
        rw [Array.length_toList]; exact Nat.le_of_not_lt h
      rw [List.drop_eq_nil_of_le this]; simp

/-- `ByteArray.toList` agrees with the list of the underlying data array. -/
private theorem byteArray_toList_eq (a : ByteArray) : a.toList = a.data.toList := by
  rw [ByteArray.toList, toList_loop_eq]; simp

/-- Round-trip: decoding an encoded signature recovers the original salt and compressed bytes.
A nonempty compressed payload guarantees the encoded length passes the `42`-byte minimum check,
so the header, salt, and payload segments all decode back to their inputs. -/
theorem sigDecode_sigEncode (salt : Bytes 40) (compSig : List UInt8) (logn : ℕ)
    (hne : compSig ≠ []) :
    sigDecode (sigEncode salt compSig logn) logn = some (salt, compSig) := by
  have hlen : 1 ≤ compSig.length := by
    rw [Nat.one_le_iff_ne_zero, ne_eq, List.length_eq_zero_iff]; exact hne
  set hdr : UInt8 := (0x30 + logn).toUInt8 with hhdr
  have hb1 : (ByteArray.mk #[hdr]).size = 1 := rfl
  have hss : (ByteArray.mk salt.toArray).size = 40 := by change salt.toArray.size = 40; simp
  have hcs : (ByteArray.mk compSig.toArray).size = compSig.length := by
    change compSig.toArray.size = compSig.length; simp
  have hesize : (sigEncode salt compSig logn).size = 41 + compSig.length := by
    change (ByteArray.mk #[hdr] ++ ByteArray.mk salt.toArray ++ ByteArray.mk compSig.toArray).size
        = 41 + compSig.length
    rw [ByteArray.size_append, ByteArray.size_append, hb1, hss, hcs]
  have hguard : ¬ (sigEncode salt compSig logn).size < 42 := by rw [hesize]; omega
  have hhead : (sigEncode salt compSig logn)[0]! = hdr := by
    have h0 : (0:Nat) < (sigEncode salt compSig logn).size := by rw [hesize]; omega
    rw [getElem!_pos _ 0 h0]
    change (ByteArray.mk #[hdr] ++ ByteArray.mk salt.toArray ++ ByteArray.mk compSig.toArray)[0]'_
        = hdr
    rw [ByteArray.getElem_eq_getElem_data]
    simp only [ByteArray.data_append]
    simp [Array.getElem_append_left]
  have hsalt : (Vector.ofFn fun (i : Fin 40) => (sigEncode salt compSig logn)[i.val + 1]!)
      = salt := by
    apply Vector.ext
    intro i hi
    rw [Vector.getElem_ofFn]
    have hfull : i + 1 < (sigEncode salt compSig logn).size := by rw [hesize]; omega
    rw [getElem!_pos _ (i+1) hfull]
    change (ByteArray.mk #[hdr] ++ ByteArray.mk salt.toArray
        ++ ByteArray.mk compSig.toArray)[i+1]'_ = salt[i]
    rw [ByteArray.getElem_eq_getElem_data]
    simp only [ByteArray.data_append]
    rw [Array.getElem_append_left (by simp; omega)]
    rw [Array.getElem_append_right (by simp)]
    simp only [Array.size_singleton]
    rw [Vector.getElem_toArray]
    congr 1
  have hcomp : ((sigEncode salt compSig logn).extract 41
      (sigEncode salt compSig logn).size).toList = compSig := by
    rw [hesize]
    change ((ByteArray.mk #[hdr] ++ ByteArray.mk salt.toArray
        ++ ByteArray.mk compSig.toArray).extract 41 (41 + compSig.length)).toList = compSig
    rw [ByteArray.extract_append_eq_right
      (a := ByteArray.mk #[hdr] ++ ByteArray.mk salt.toArray) (b := ByteArray.mk compSig.toArray)
      (by rw [ByteArray.size_append, hb1, hss]) (by rw [ByteArray.size_append, hb1, hss, hcs])]
    rw [byteArray_toList_eq]
  unfold sigDecode
  simp only [Id.run, hguard, hhead, hhdr, if_false, bne_self_eq_false, Bool.false_eq_true,
    pure_bind, hsalt, hcomp]
  rfl

end Falcon.Concrete
