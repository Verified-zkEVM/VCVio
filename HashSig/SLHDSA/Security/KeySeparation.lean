/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module

public import HashSig.SLHDSA.AddressDiscipline
public import HashSig.SLHDSA.Concrete.FIPS
public import HashSig.SLHDSA.Concrete.Instance
import HashSig.SLHDSA.Security.AddressKeys

/-!
# Key separation of the concrete SLH-DSA bundles

`CorePrimitives.KeySeparated` says that no address of type at most `4` shares its oracle key with
a secret-key address. Each shipped bundle satisfies it at every address, because its oracle key
keeps enough of the address type apart:

* `Concrete.keySeparated_shakePrimitives`: the SHAKE bundles, whose oracle key is the full
  32-byte address with its four-byte type block;
* `Concrete.keySeparated_shaPrimitives`: the SLH-DSA-SHA2-128-24 compatibility bundle, whose
  oracle key is the compressed address `ADRSc` with its one-byte type block;
* `Concrete.keySeparated_sha2Primitives`: the FIPS SHA-2 bundles, whose oracle key
  `Concrete.sha2AdrsKey` is `ADRSc` on the checked domain and the type-tagged
  `Concrete.sha2FallbackKey` outside it. Byte `9` of the key is the type byte: the low byte of the
  type on the checked domain (`Concrete.toNat_getElem_sha2AdrsKey_nine_of_ok`), and `7` or `8`
  outside it (`Concrete.toNat_getElem_sha2AdrsKey_nine_of_error`), according as the type is at
  most `4` or not. The same byte shows that the fallback is the key of no checked-domain address
  (`Concrete.sha2AdrsKey_ne_sha2FallbackKey`).
-/

public section

namespace SLHDSA

/-- Equal big-endian encodings of one width encode equal values below the width's bound. -/
private theorem eq_of_toBytesBE_eq {x y w : ℕ} (hx : x < 256 ^ w) (hy : y < 256 ^ w)
    (h : Adrs.toBytesBE x w = Adrs.toBytesBE y w) : x = y := by
  have h' := congrArg toInt h
  simp only [Adrs.toBytesBE] at h'
  rwa [toInt_toByte _ _ hx, toInt_toByte _ _ hy] at h'

/-- A secret-key address has type `5` or `6`. -/
private theorem Adrs.IsSecretKey.type_eq {a : Adrs} (ha : a.IsSecretKey) :
    a.type = 5 ∨ a.type = 6 := ha

namespace Concrete

/-- The SHAKE bundles are key-separated: their oracle key is the full 32-byte address, whose type
block separates the secret-key types from the types at most `4`. -/
theorem keySeparated_shakePrimitives (p : Params) : (shakePrimitives p).core.KeySeparated := by
  intro a b ha hb h
  have hbytes : a.toBytes = b.toBytes := by
    have h' := congrArg Vector.toList h
    simpa only [Primitives.core, shakePrimitives, Adrs.toVector, Vector.toList_mk,
      List.toList_toArray] using h'
  have := eq_of_toBytesBE_eq (w := 4) (by rcases ha.type_eq with h | h <;> rw [h] <;> norm_num)
    (by omega) (Security.toBytes_blocks hbytes).2.2.1
  rcases ha.type_eq with h | h <;> omega

/-- The SLH-DSA-SHA2-128-24 compatibility bundle is key-separated: its oracle key is the
compressed address `ADRSc`, whose one-byte type block separates the secret-key types from the
types at most `4`. -/
theorem keySeparated_shaPrimitives : shaPrimitives.core.KeySeparated := by
  intro a b ha hb h
  have hbytes : a.compressSha2 = b.compressSha2 := by
    rw [← shaAdrsKey_toList, ← shaAdrsKey_toList]
    exact congrArg Vector.toList h
  have := eq_of_toBytesBE_eq (w := 1) (by rcases ha.type_eq with h | h <;> rw [h] <;> norm_num)
    (by omega) (Security.compressSha2_blocks hbytes).2.2.1
  rcases ha.type_eq with h | h <;> omega

/-- Offset `9` of the compressed address `ADRSc` is the low byte of the address type. -/
theorem _root_.SLHDSA.Adrs.getElem_compressSha2_nine (a : Adrs) :
    a.compressSha2[9]'(by simp) = UInt8.ofNat (a.type % 256) := by
  simp [Adrs.compressSha2, List.getElem_append_right, Adrs.toBytesBE, toByte]

/-- Offset `9` of the fallback key is its type tag. -/
theorem getElem_sha2FallbackKey_nine (type : ℕ) :
    (sha2FallbackKey type)[9] = if type ≤ 4 then 7 else 8 := by
  simp [sha2FallbackKey]

/-- On the checked domain, byte `9` of the SHA-2 key is the low byte of the address type. -/
theorem toNat_getElem_sha2AdrsKey_nine_of_ok {a : Adrs} {value : Bytes 22}
    (h : a.compressSha2Checked = .ok value) : (sha2AdrsKey a)[9].toNat = a.type % 256 := by
  rw [sha2AdrsKey_eq_of_compressSha2Checked_eq_ok h]
  unfold Adrs.compressSha2Checked at h
  split_ifs at h
  cases h
  simp [Adrs.getElem_compressSha2_nine]

/-- Outside the checked domain, byte `9` of the SHA-2 key is `7` for a type at most `4` and `8`
otherwise. -/
theorem toNat_getElem_sha2AdrsKey_nine_of_error {a : Adrs} {error : CodecError}
    (h : a.compressSha2Checked = .error error) :
    (sha2AdrsKey a)[9].toNat = if a.type ≤ 4 then 7 else 8 := by
  rw [sha2AdrsKey_eq_sha2FallbackKey_of_compressSha2Checked_eq_error h,
    getElem_sha2FallbackKey_nine]
  split_ifs <;> rfl

/-- The SHA-2 fallback key is the key of no checked-domain address: the type byte of a
checked-domain key is a FIPS 205 type code, at most `6`, while the fallback's is `7` or `8`. -/
theorem sha2AdrsKey_ne_sha2FallbackKey {a : Adrs} {value : Bytes 22}
    (h : a.compressSha2Checked = .ok value) (type : ℕ) :
    sha2AdrsKey a ≠ sha2FallbackKey type := by
  intro hkey
  have h9 := toNat_getElem_sha2AdrsKey_nine_of_ok h
  rw [hkey, getElem_sha2FallbackKey_nine] at h9
  have hcanonical : a.isCanonical = true := by
    unfold Adrs.compressSha2Checked at h
    by_contra hc
    simp [Bool.eq_false_iff.2 hc] at h
  have := Adrs.type_le_six_of_isCanonical hcanonical
  split_ifs at h9 <;> simp at h9 <;> omega

/-- The FIPS SHA-2 bundles are key-separated: byte `9` of their oracle key is the type byte on the
checked domain and a type tag outside it, and the two type classes never share it. -/
theorem keySeparated_sha2Primitives (p : Params) : (sha2Primitives p).core.KeySeparated := by
  intro a b ha hb hkey
  replace hkey : sha2AdrsKey a = sha2AdrsKey b := hkey
  have h9 := congrArg (fun k : Bytes 22 => k[9].toNat) hkey
  have := ha.type_eq
  rcases hA : a.compressSha2Checked with _ | _ <;> rcases hB : b.compressSha2Checked with _ | _
  all_goals first
    | rw [toNat_getElem_sha2AdrsKey_nine_of_ok hA] at h9
    | rw [toNat_getElem_sha2AdrsKey_nine_of_error hA] at h9
  all_goals first
    | rw [toNat_getElem_sha2AdrsKey_nine_of_ok hB] at h9
    | rw [toNat_getElem_sha2AdrsKey_nine_of_error hB] at h9
  all_goals (try split_ifs at h9) <;> omega

end Concrete

end SLHDSA
