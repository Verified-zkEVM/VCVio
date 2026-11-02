/-
Copyright (c) 2026 Tom Wambsgans, Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Wambsgans, Alexander Hicks
-/

module
public import HashSig.SLHDSA.SHAKE128s.Statement.Types
public import HashSig.SLHDSA.SHAKE128s.FIPS205.Params
public import HashSig.SLHDSA.Encoding
public import VCVio.OracleComp.Constructions.SampleableType.Measure

/-!
# Complete SHAKE-128s byte representations

Big-endian bit vectors and fixed-width byte vectors are in bijection. The complete30-byte
answer map preserves its uniform law without importing signature algorithms or a compiler rule.
-/

public section

open OracleComp OracleSpec

namespace SLHDSA.SHAKE128s.Bridge

open SLHDSA

/-! ## Big-endian bytes -/

/-- The paper's big-endian encoding is FIPS 205's `toByte` of the value. -/
theorem bytesBE_eq_toByte (k : ℕ) (v : BitVec (8 * k)) : bytesBE k v = toByte v.toNat k := by
  apply List.ext_getElem
  · simp [bytesBE]
  · intro i h₁ h₂
    have hk : i < k := by simpa [bytesBE] using h₁
    simp only [bytesBE, List.getElem_reverse, List.getElem_ofFn, List.length_ofFn, toByte,
      VCVio.Algorithms.Encoding.natToBytesBE, List.getElem_map, List.getElem_range]
    apply UInt8.toNat_inj.mp
    simp only [UInt8.toNat_ofBitVec, BitVec.extractLsb'_toNat, UInt8.toNat_ofNat',
      Nat.shiftRight_eq_div_pow, pow_mul]
    norm_num

/-- `toByte x k` reads only `x` modulo `256 ^ k`. -/
theorem toByte_mod (x k : ℕ) : toByte (x % 256 ^ k) k = toByte x k :=
  eq_of_length_eq_of_toInt_eq (by simp) (by simp [toInt_toByte_mod])

/-- The first `a` bytes of `toByte x (a + b)` are `toByte (x / 256 ^ b) a`. -/
theorem take_toByte (x a b : ℕ) : (toByte x (a + b)).take a = toByte (x / 256 ^ b) a := by
  apply List.ext_getElem
  · simp
  · intro i h₁ h₂
    have hi : i < a := by simpa using h₂
    simp only [List.getElem_take, toByte, VCVio.Algorithms.Encoding.natToBytesBE,
      List.getElem_map, List.getElem_range, Nat.div_div_eq_div_mul, ← pow_add]
    congr 4
    omega

/-- The bytes of `toByte x (a + b)` after the first `a` are `toByte x b`. -/
theorem drop_toByte (x a b : ℕ) : (toByte x (a + b)).drop a = toByte x b := by
  apply List.ext_getElem
  · simp
  · intro i h₁ h₂
    simp only [List.getElem_drop, toByte, VCVio.Algorithms.Encoding.natToBytesBE,
      List.getElem_map, List.getElem_range]
    congr 4
    simp at h₂
    omega

/-- The big-endian encoding of a `k`-byte value has `k` bytes. -/
theorem length_bytesBE (k : ℕ) (v : BitVec (8 * k)) : (bytesBE k v).length = k := by
  simp [bytesBE]

/-- The paper's big-endian bytes read back as the value. -/
@[simp] theorem toInt_bytesBE (k : ℕ) (v : BitVec (8 * k)) : toInt (bytesBE k v) = v.toNat := by
  rw [bytesBE_eq_toByte, toInt_toByte]
  have := v.isLt
  rwa [pow_mul] at this

/-- **`k`-byte big-endian values and `k`-byte vectors**: the paper's `bytesBE` packaged as a
vector, with inverse FIPS 205's `toInt`. -/
@[expose] def bytesEquiv (k : ℕ) : BitVec (8 * k) ≃ SLHDSA.Bytes k where
  toFun v := ⟨(bytesBE k v).toArray, by simp [bytesBE]⟩
  invFun b := BitVec.ofNat (8 * k) (toInt b.toList)
  left_inv v := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ofNat]
    change toInt (bytesBE k v) % 2 ^ (8 * k) = v.toNat
    rw [toInt_bytesBE, Nat.mod_eq_of_lt v.isLt]
  right_inv b := by
    apply Vector.toList_inj.mp
    change bytesBE k (BitVec.ofNat (8 * k) (toInt b.toList)) = b.toList
    rw [bytesBE_eq_toByte, BitVec.toNat_ofNat, pow_mul, show (2 : ℕ) ^ 8 = 256 by norm_num,
      toByte_mod]
    simpa using toByte_toInt b.toList

/-- The bytes of `bytesEquiv k v` are the paper's `bytesBE k v`. -/
@[simp] theorem toList_bytesEquiv (k : ℕ) (v : BitVec (8 * k)) :
    (bytesEquiv k v).toList = bytesBE k v := by
  simp [bytesEquiv, Vector.toList]

/-- The value of a byte vector is its big-endian integer. -/
@[simp] theorem toNat_bytesEquiv_symm (k : ℕ) (b : SLHDSA.Bytes k) :
    ((bytesEquiv k).symm b).toNat = toInt b.toList := by
  change (BitVec.ofNat (8 * k) (toInt b.toList)).toNat = _
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
  have := toInt_lt_pow b.toList
  rw [Vector.length_toList] at this
  rwa [pow_mul]

/-- The paper's big-endian bytes of a vector's value are the vector's bytes. -/
@[simp] theorem bytesBE_bytesEquiv_symm (k : ℕ) (b : SLHDSA.Bytes k) :
    bytesBE k ((bytesEquiv k).symm b) = b.toList := by
  rw [← toList_bytesEquiv, Equiv.apply_symm_apply]

/-- The `n = 16`-byte vectors of SLH-DSA-SHAKE-128s. Every carrier of `FIPS205.core` (`PkSeed`,
`SkSeed`, `SkPrf`, `Y`) is definitionally this type. -/
abbrev Node : Type := SLHDSA.Bytes FIPS205.params.params.n

/-- **Digests are nodes**: a `128`-bit digest is the node of its `16` big-endian bytes. The
codomain is the node carrier `FIPS205.core.Y`, definitionally `Node`. -/
@[expose] def digestEquiv : Digest ≃ FIPS205.core.Y := bytesEquiv n

/-- **Oracle answers are `30`-byte vectors** (`m = 30` for SLH-DSA-SHAKE-128s), big-endian. -/
@[expose] def answerEquiv : HashOutput ≃ FIPS205.Answer := bytesEquiv messageDigestBytes

/-- The bytes of a digest's node are its big-endian bytes. -/
@[simp] theorem toList_digestEquiv (d : Digest) :
    Vector.toList (digestEquiv d : Node) = bytesBE n d :=
  toList_bytesEquiv n d

/-- The bytes of an answer are its big-endian bytes. -/
@[simp] theorem toList_answerEquiv (h : HashOutput) :
    (answerEquiv h).toList = bytesBE messageDigestBytes h :=
  toList_bytesEquiv messageDigestBytes h

/-- The big-endian bytes of a node's digest are the node's bytes. -/
@[simp] theorem bytesBE_digestEquiv_symm (b : FIPS205.core.Y) :
    bytesBE n (digestEquiv.symm b) = Vector.toList (b : Node) :=
  bytesBE_bytesEquiv_symm n b

/-- The big-endian bytes of an answer's paper value are the answer's bytes. -/
@[simp] theorem bytesBE_answerEquiv_symm (b : FIPS205.Answer) :
    bytesBE messageDigestBytes (answerEquiv.symm b) = b.toList :=
  bytesBE_bytesEquiv_symm messageDigestBytes b

/-- The value of a node's digest is the big-endian integer of its bytes. -/
@[simp] theorem toNat_digestEquiv_symm (b : FIPS205.core.Y) :
    (digestEquiv.symm b).toNat = toInt (Vector.toList (b : Node)) :=
  toNat_bytesEquiv_symm n b

/-- The value of an answer's paper value is the big-endian integer of its bytes. -/
@[simp] theorem toNat_answerEquiv_symm (b : FIPS205.Answer) :
    (answerEquiv.symm b).toNat = toInt b.toList :=
  toNat_bytesEquiv_symm messageDigestBytes b

open SampleableType in
/-- **A uniform paper answer is a uniform FIPS 205 answer.** -/
theorem map_answerEquiv_uniformSample :
    answerEquiv <$> ($ᵗ HashOutput : ProbComp HashOutput) =ᵈ
      ($ᵗ FIPS205.Answer : ProbComp _) :=
  map_uniformSample_evalDistEq_of_bijective answerEquiv.bijective


end SLHDSA.SHAKE128s.Bridge
