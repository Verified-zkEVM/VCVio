/-
Copyright (c) 2026 Tom Wambsgans. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Wambsgans
-/

module

public import HashSig.SLHDSA.SHAKE128s.Statement.Scheme
public import HashSig.SLHDSA.SHAKE128s.Statement.FIPS205

/-!
# Data correspondences between the paper model and FIPS 205 at SLH-DSA-SHAKE-128s

Test file.
-/

@[expose] public section

open OracleComp OracleSpec

namespace SlhDsaSecurity.Bridge

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

/-- The paper's big-endian bytes read back as the value. -/
@[simp] theorem toInt_bytesBE (k : ℕ) (v : BitVec (8 * k)) : toInt (bytesBE k v) = v.toNat := by
  rw [bytesBE_eq_toByte, toInt_toByte]
  have := v.isLt
  rwa [pow_mul] at this

/-- **`k`-byte big-endian values and `k`-byte vectors**: the paper's `bytesBE` packaged as a
vector, with inverse FIPS 205's `toInt`. -/
def bytesEquiv (k : ℕ) : BitVec (8 * k) ≃ SLHDSA.Bytes k where
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

/-- The FIPS 205 node carrier at SLH-DSA-SHAKE-128s: `n = 16` bytes. Every carrier of
`FIPS205.core` (`PkSeed`, `SkSeed`, `SkPrf`, `Y`) is this type. -/
abbrev Node : Type := SLHDSA.Bytes FIPS205.params.params.n

/-- **Digests are `16`-byte vectors**, big-endian. -/
def digestEquiv : Digest ≃ Node := bytesEquiv n

/-- **Oracle answers are `30`-byte vectors** (`m = 30` for SLH-DSA-SHAKE-128s), big-endian. -/
def answerEquiv : HashOutput ≃ FIPS205.Answer := bytesEquiv messageDigestBytes

@[simp] theorem toList_digestEquiv (d : Digest) : (digestEquiv d).toList = bytesBE n d :=
  toList_bytesEquiv n d

@[simp] theorem toList_answerEquiv (h : HashOutput) :
    (answerEquiv h).toList = bytesBE messageDigestBytes h :=
  toList_bytesEquiv messageDigestBytes h

@[simp] theorem bytesBE_digestEquiv_symm (b : Node) :
    bytesBE n (digestEquiv.symm b) = b.toList :=
  bytesBE_bytesEquiv_symm n b

@[simp] theorem bytesBE_answerEquiv_symm (b : FIPS205.Answer) :
    bytesBE messageDigestBytes (answerEquiv.symm b) = b.toList :=
  bytesBE_bytesEquiv_symm messageDigestBytes b

@[simp] theorem toNat_digestEquiv_symm (b : Node) :
    (digestEquiv.symm b).toNat = toInt b.toList :=
  toNat_bytesEquiv_symm n b

@[simp] theorem toNat_answerEquiv_symm (b : FIPS205.Answer) :
    (answerEquiv.symm b).toNat = toInt b.toList :=
  toNat_bytesEquiv_symm messageDigestBytes b

/-- The bytes of an answer, as `toByte` of its value. -/
theorem toList_answerEquiv_eq_toByte (h : HashOutput) :
    (answerEquiv h).toList = toByte h.toNat 30 := by
  rw [toList_answerEquiv, bytesBE_eq_toByte]
  rfl

/-! ## Truncation -/

/-- **The `n`-byte role read of an answer is the paper's truncation**: the first `16` bytes of the
`30`-byte answer are the big-endian bytes of its top `128` bits. -/
theorem prefixBytes_answerEquiv (h : HashOutput) :
    SLHDSA.Security.prefixBytes FIPS205.params.params.n (answerEquiv h) =
      digestEquiv (Hashing.truncate h) := by
  apply Vector.toList_inj.mp
  rw [SLHDSA.Security.toList_prefixBytes_of_le (by decide), toList_answerEquiv_eq_toByte,
    toList_digestEquiv, bytesBE_eq_toByte]
  change (toByte h.toNat (16 + 14)).take 16 = _
  rw [take_toByte, ← toByte_mod]
  congr 1
  simp only [Hashing.truncate, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]
  norm_num [messageDigestBytes, n]

/-- The same statement at the literal width `16`. -/
theorem prefixBytes_sixteen_answerEquiv (h : HashOutput) :
    SLHDSA.Security.prefixBytes 16 (answerEquiv h) = digestEquiv (Hashing.truncate h) :=
  prefixBytes_answerEquiv h

/-! ## Message-digest parsing -/

/-- The parsed digest of an answer, at the SLH-DSA-SHAKE-128s parameters. -/
abbrev parts (h : HashOutput) : DigestParts FIPS205.params.params :=
  splitDigest FIPS205.params.params (answerEquiv h)

/-- **`idx_tree`**: the tree index FIPS 205 parses is the paper's `MessageDigest.treeIndex`. -/
theorem idxTree_val_parts (h : HashOutput) :
    (parts h).idxTree.val = (MessageDigest.treeIndex h).toNat := by
  rw [splitDigest_idxTree_val, toList_answerEquiv_eq_toByte]
  change toInt (((toByte h.toNat (21 + 9)).drop 21).take 7) % 2 ^ 54 = _
  rw [drop_toByte, show (9 : ℕ) = 7 + 2 from rfl, take_toByte, toInt_toByte_mod]
  simp only [MessageDigest.treeIndex, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]
  norm_num [totalHeight, subtreeHeight]

/-- **`idx_leaf`**: the leaf index FIPS 205 parses is the paper's `MessageDigest.leafIndex`. -/
theorem idxLeaf_val_parts (h : HashOutput) :
    (parts h).idxLeaf.val = (MessageDigest.leafIndex h).toNat := by
  rw [splitDigest_idxLeaf_val, toList_answerEquiv_eq_toByte]
  change toInt (((toByte h.toNat (28 + 2)).drop 28).take 2) % 2 ^ 9 = _
  rw [drop_toByte, List.take_of_length_le (by simp), toInt_toByte_mod]
  simp only [MessageDigest.leafIndex, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]
  norm_num [subtreeHeight]

/-- Reading bits `[a + c, a + c + d)` of `x` through an intermediate window of `b` bits from
bit `a`. -/
theorem div_pow_mod_pow_div_pow_mod (x a b c d : ℕ) (h : c + d ≤ b) :
    x / 2 ^ a % 2 ^ b / 2 ^ c % 2 ^ d = x / 2 ^ (a + c) % 2 ^ d := by
  rw [show (2 : ℕ) ^ b = 2 ^ c * 2 ^ (b - c) by rw [← pow_add]; congr 1; omega,
    Nat.mod_mul_right_div_self, Nat.mod_mod_of_dvd _ (pow_dvd_pow 2 (by omega)),
    Nat.div_div_eq_div_mul, ← pow_add]

/-- The FORS message bytes `md` are the first `21` bytes of the answer. -/
theorem toList_md_parts (h : HashOutput) :
    (parts h).md.toList = toByte (h.toNat / 256 ^ 9) 21 := by
  rw [splitDigest_md_toList, toList_answerEquiv_eq_toByte]
  exact take_toByte _ 21 9

/-- **FORS indices**: the leaf FIPS 205 selects in FORS tree `i` is the paper's
`MessageDigest.forsIndices`. -/
theorem forsIdx_parts (h : HashOutput) (i : Fin forsTrees) :
    forsIdx FIPS205.params.params (parts h).md.toList i.val =
      (MessageDigest.forsIndices h i).val := by
  have hi := i.isLt
  simp only [forsTrees] at hi
  rw [forsIdx, toList_md_parts, base2b_bigEndian _ _ _ (by simp only [toByte_length]; decide)]
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range (by exact hi)]
  simp only [Option.map_some, Option.getD_some, toByte_length, toInt_toByte_mod]
  simp only [MessageDigest.forsIndices, BitVec.val_toFin, BitVec.extractLsb'_toNat,
    Nat.shiftRight_eq_div_pow]
  rw [show (256 : ℕ) ^ 9 = 2 ^ 72 by norm_num, show (256 : ℕ) ^ 21 = 2 ^ 168 by norm_num]
  change h.toNat / 2 ^ 72 % 2 ^ 168 / 2 ^ (8 * 21 - 12 * (i.val + 1)) % 2 ^ 12 =
    h.toNat / 2 ^ (72 + 12 * (14 - 1 - i.val)) % 2 ^ 12
  rw [div_pow_mod_pow_div_pow_mod _ _ _ _ _ (by omega)]
  congr 3
  omega

/-! ## Pure-mode framing -/

/-- **Framing**: the paper's `Message.frame` is FIPS 205's pure-mode encoder
`0 ‖ |ctx| ‖ ctx ‖ M`, rejecting the same contexts. -/
theorem frame_eq_encodePureMessage (request : Message) :
    request.frame =
      (External.encodePureMessage request.context request.message).toOption := by
  by_cases h : request.context.length ≤ 255
  · rw [External.encodePureMessage_eq_ok _ _ h]
    simp only [Message.frame, h, ↓reduceIte]
    rfl
  · simp only [Message.frame, h, ↓reduceIte]
    simp only [External.encodePureMessage, External.encodeMessage,
      External.requireContext_eq_error _ (Nat.lt_of_not_le h)]
    rfl

/-! ## WOTS+ digits -/

/-- The big-endian base-`w` digit `j` of `digitsOfBaseW`. -/
theorem getElem?_digitsOfBaseW (x w : ℕ) :
    ∀ (len j : ℕ), j < len →
      (WotsChecksum.digitsOfBaseW x w len)[j]? = some (x / w ^ (len - 1 - j) % w)
  | 0, j, h => absurd h (Nat.not_lt_zero j)
  | len + 1, 0, _ => by simp [WotsChecksum.digitsOfBaseW]
  | len + 1, j + 1, h => by
    rw [WotsChecksum.digitsOfBaseW, List.getElem?_cons_succ,
      getElem?_digitsOfBaseW x w len j (by omega), show len + 1 - 1 - (j + 1) = len - 1 - j by omega]

/-- The message digits FIPS 205 extracts from a node are the paper's `messageDigit`s. -/
theorem wotsMsgDigitsCore_digestEquiv (d : Digest) :
    wotsMsgDigitsCore FIPS205.core (digestEquiv d) =
      List.ofFn fun j : Fin messageDigits => (Checksum.messageDigit d j).val := by
  change base2b (digestEquiv d).toList 4 32 = _
  rw [base2b_bigEndian _ _ _ (by rw [Vector.length_toList]; decide)]
  simp only [Vector.length_toList]
  apply List.ext_getElem
  · simp [messageDigits, n, winternitzBits]
  · intro j h₁ h₂
    have hj : j < 32 := by simpa using h₁
    simp only [List.getElem_map, List.getElem_range, List.getElem_ofFn, toList_digestEquiv,
      toInt_bytesBE, Checksum.messageDigit, BitVec.val_toFin,
      BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]
    change d.toNat / 2 ^ (8 * 16 - 4 * (j + 1)) % 2 ^ 4 =
      d.toNat / 2 ^ (4 * (32 - 1 - j)) % 2 ^ 4
    rw [show 8 * 16 - 4 * (j + 1) = 4 * (32 - 1 - j) by omega]

/-- **WOTS+ chain lengths**: the number of `F` steps FIPS 205 takes on chain `i` when signing a
node is the paper's digit `Checksum.encode`, message digits and checksum digits alike. -/
theorem chainStepsCore_digestEquiv (d : Digest) (i : Fin chains) :
    chainStepsCore FIPS205.core (digestEquiv d) i.val = (Checksum.encode d i).val := by
  have hi := i.isLt
  simp only [chains, messageDigits, checksumDigits, n, winternitzBits] at hi
  unfold chainStepsCore
  have hfull := chainLengthsCore_eq_wotsFullDigits FIPS205.params.valid FIPS205.core
    (digestEquiv d)
  rw [hfull, wotsMsgDigitsCore_digestEquiv, WotsChecksum.wotsFullDigits,
    List.getD_eq_getElem?_getD, Checksum.encode]
  by_cases hm : i.val < messageDigits
  · simp only [hm, ↓reduceDIte]
    rw [List.getElem?_append_left (by simpa using hm), List.getElem?_ofFn]
    simp [hm]
  · simp only [hm, ↓reduceDIte]
    rw [List.getElem?_append_right (by simp; omega)]
    simp only [List.length_ofFn]
    have hlt : i.val - messageDigits < 3 := by simp only [messageDigits, n, winternitzBits]; omega
    change (WotsChecksum.digitsOfBaseW _ 16 3)[i.val - messageDigits]?.getD 0 = _
    rw [getElem?_digitsOfBaseW _ _ _ _ hlt]
    simp only [Option.getD_some, Checksum.checksumDigit, Checksum.checksum,
      WotsChecksum.wotsChecksumValue, List.map_ofFn, List.sum_ofFn, Function.comp_def]
    rfl

end SlhDsaSecurity.Bridge
