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

The paper model (`HashSig.SLHDSA.SHAKE128s.Statement.Scheme`) works with big-endian bit vectors and
32-byte paper addresses; FIPS 205's library (`HashSig.SLHDSA`), at `FIPS205.params` and the SHAKE
context `FIPS205.core`, works with byte vectors and structured addresses with natural-number
fields. This module identifies the data of the two.

## Main definitions

* `digestEquiv : Digest ≃ FIPS205.core.Y` and `answerEquiv : HashOutput ≃ FIPS205.Answer`:
  big-endian bytes (`toList_digestEquiv`, `toList_answerEquiv`), instances of `bytesEquiv`.
* `toAdrs : Address → Adrs`: the same six fields.
* `sigOfCore`, `sigToCore`, `signatureEquiv`: structured signatures.

## Main statements

* `prefixBytes_answerEquiv`: the `n`-byte read of an answer is the paper's `Hashing.truncate`.
* `idxTree_val_parts`, `idxLeaf_val_parts`, `forsIdx_parts`: FIPS 205's digest split is the paper's
  `MessageDigest.treeIndex`, `leafIndex` and `forsIndices`.
* `frame_eq_encodePureMessage`: the paper's framing is FIPS 205's pure-mode encoder.
* `chainStepsCore_digestEquiv`: FIPS 205's WOTS+ chain lengths are the paper's `Checksum.encode`.
* `toList_adrsToKey_toAdrs` and the `toAdrs_*` lemmas: every address construction of the paper is
  the corresponding FIPS 205 construction, so both schemes hash at the same address bytes.
* `encode_thash`, `encode_hmsg`, `encode_prfMsg`: the single-oracle layouts of
  `SLHDSA.Security.encode` are the paper's oracle inputs.
* `toBytes_sigOfCore`, `fromBytes?_eq`: signature encoding and parsing agree.
* `map_digestEquiv_uniformSample`, `map_answerEquiv_uniformSample`: uniform samples correspond.

## Implementation notes

Every carrier of `FIPS205.core` is definitionally `Node = Bytes 16`, but `rw` and `simp` do not
see through the carriers, so lemmas are stated at the carrier the FIPS 205 programs use: nodes at
`FIPS205.core.Y`, the codomain of `digestEquiv`. At another carrier, ascribe the type
(`(x : Node)`) or `change` the goal.

FIPS 205's address setters store natural numbers, the paper's `BitVec.ofNat` values; the address
lemmas carry the hypotheses that the stored indices fit their fields, which hold at every address
either scheme builds.
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
      getElem?_digitsOfBaseW x w len j (by omega),
      show len + 1 - 1 - (j + 1) = len - 1 - j by omega]

/-- The message digits FIPS 205 extracts from a node are the paper's `messageDigit`s. -/
theorem wotsMsgDigitsCore_digestEquiv (d : Digest) :
    wotsMsgDigitsCore FIPS205.core (digestEquiv d) =
      List.ofFn fun j : Fin messageDigits => (Checksum.messageDigit d j).val := by
  change base2b (bytesBE n d) 4 32 = _
  rw [base2b_bigEndian _ _ _ (by rw [length_bytesBE]; decide), length_bytesBE]
  apply List.ext_getElem
  · simp [messageDigits, n, winternitzBits]
  · intro j h₁ h₂
    have hj : j < 32 := by simpa using h₁
    simp only [List.getElem_map, List.getElem_range, List.getElem_ofFn, toInt_bytesBE,
      Checksum.messageDigit, BitVec.val_toFin, BitVec.extractLsb'_toNat,
      Nat.shiftRight_eq_div_pow]
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

/-- The WOTS+ chain lengths of any node, through its digest. -/
theorem chainStepsCore_eq_encode (msg : FIPS205.core.Y) (i : Fin chains) :
    chainStepsCore FIPS205.core msg i.val = (Checksum.encode (digestEquiv.symm msg) i).val := by
  rw [← chainStepsCore_digestEquiv, Equiv.apply_symm_apply]

/-! ## Addresses -/

/-- The FIPS 205 address type of a paper address type. -/
@[expose] def _root_.SLHDSA.SHAKE128s.AddressType.toAddrType : AddressType → AddrType
  | .wotsHash => .wotsHash
  | .wotsPk => .wotsPk
  | .tree => .tree
  | .forsTree => .forsTree
  | .forsRoots => .forsRoots
  | .wotsPrf => .wotsPrf
  | .forsPrf => .forsPrf

/-- The paper's type code is FIPS 205's. -/
@[simp] theorem _root_.SLHDSA.SHAKE128s.AddressType.toNat_code (k : AddressType) :
    k.code.toNat = k.toAddrType.toCode := by
  cases k <;> rfl

/-- **The FIPS 205 structured address of a paper address**: the same six fields, as naturals. -/
@[expose] def toAdrs (a : Address) : Adrs where
  layer := a.layer.toNat
  tree := a.tree.toNat
  type := a.kind.code.toNat
  word1 := a.keyPair.toNat
  word2 := a.chainOrHeight.toNat
  word3 := a.hashOrIndex.toNat

/-- **Address bytes**: FIPS 205's 32-byte serialization of `toAdrs a` is the paper's
`a.toBytes`. -/
theorem toBytes_toAdrs (a : Address) : (toAdrs a).toBytes = a.toBytes := by
  simp only [Adrs.toBytes, Adrs.toBytesBE, Address.toBytes, bytesBE_eq_toByte, toAdrs]

/-- The address key the SHAKE context hashes is the 32-byte serialization of the address. -/
@[simp] theorem toList_adrsToKey (A : Adrs) :
    Vector.toList (FIPS205.core.adrsToKey A : SLHDSA.Bytes 32) = A.toBytes := rfl

/-- **Address keys**: the 32 bytes the SHAKE context hashes as the address of `toAdrs a` are the
paper's `a.toBytes`. -/
theorem toList_adrsToKey_toAdrs (a : Address) :
    Vector.toList (FIPS205.core.adrsToKey (toAdrs a) : SLHDSA.Bytes 32) = a.toBytes :=
  toBytes_toAdrs a

/-! ### Setters

Paper addresses set a field to `BitVec.ofNat w i`; FIPS 205's setters store `i` itself. The two
agree whenever `i` fits the field. -/

section Setters

variable (a : Address)

/-- `setTypeAndClear` commutes with `toAdrs`. -/
theorem toAdrs_setTypeAndClear (k : AddressType) :
    toAdrs (a.setTypeAndClear k) = (toAdrs a).setTypeAndClear k.toAddrType := by
  apply Adrs.ext <;> simp [toAdrs, Address.setTypeAndClear, Adrs.setTypeAndClear]

/-- The paper's layer update is `setLayerAddress`. -/
theorem toAdrs_setLayer {i : ℕ} (hi : i < 2 ^ 32) :
    toAdrs { a with layer := BitVec.ofNat 32 i } = (toAdrs a).setLayerAddress i := by
  apply Adrs.ext <;>
    simp [toAdrs, Adrs.setLayerAddress, Nat.mod_eq_of_lt (show i < 4294967296 by omega)]

/-- The paper's tree update is `setTreeAddress`. -/
theorem toAdrs_setTree {i : ℕ} (hi : i < 2 ^ 96) :
    toAdrs { a with tree := BitVec.ofNat 96 i } = (toAdrs a).setTreeAddress i := by
  apply Adrs.ext <;>
    simp [toAdrs, Adrs.setTreeAddress,
      Nat.mod_eq_of_lt (show i < 79228162514264337593543950336 by omega)]

/-- The paper's key-pair update is `setKeyPairAddress`. -/
theorem toAdrs_setKeyPair {i : ℕ} (hi : i < 2 ^ 32) :
    toAdrs { a with keyPair := BitVec.ofNat 32 i } = (toAdrs a).setKeyPairAddress i := by
  apply Adrs.ext <;>
    simp [toAdrs, Adrs.setKeyPairAddress, Nat.mod_eq_of_lt (show i < 4294967296 by omega)]

/-- The paper's chain update is `setChainAddress`. -/
theorem toAdrs_setChain {i : ℕ} (hi : i < 2 ^ 32) :
    toAdrs { a with chainOrHeight := BitVec.ofNat 32 i } = (toAdrs a).setChainAddress i := by
  apply Adrs.ext <;>
    simp [toAdrs, Adrs.setChainAddress, Nat.mod_eq_of_lt (show i < 4294967296 by omega)]

/-- The paper's height update is `setTreeHeight`. -/
theorem toAdrs_setHeight {i : ℕ} (hi : i < 2 ^ 32) :
    toAdrs { a with chainOrHeight := BitVec.ofNat 32 i } = (toAdrs a).setTreeHeight i := by
  apply Adrs.ext <;>
    simp [toAdrs, Adrs.setTreeHeight, Nat.mod_eq_of_lt (show i < 4294967296 by omega)]

/-- The paper's hash-index update is `setHashAddress`. -/
theorem toAdrs_setHash {i : ℕ} (hi : i < 2 ^ 32) :
    toAdrs { a with hashOrIndex := BitVec.ofNat 32 i } = (toAdrs a).setHashAddress i := by
  apply Adrs.ext <;>
    simp [toAdrs, Adrs.setHashAddress, Nat.mod_eq_of_lt (show i < 4294967296 by omega)]

/-- The paper's tree-index update is `setTreeIndex`. -/
theorem toAdrs_setIndex {i : ℕ} (hi : i < 2 ^ 32) :
    toAdrs { a with hashOrIndex := BitVec.ofNat 32 i } = (toAdrs a).setTreeIndex i := by
  apply Adrs.ext <;>
    simp [toAdrs, Adrs.setTreeIndex, Nat.mod_eq_of_lt (show i < 4294967296 by omega)]

end Setters

/-! ### The addresses of the two schemes

Each paper address construction, applied to a paper base address `a`, is FIPS 205's construction
applied to `toAdrs a`. With `toList_adrsToKey_toAdrs`, the two schemes hash at the same address
bytes. -/

/-- **Hypertree base addresses**: the paper's `Hypertree.address` is FIPS 205's `layerAdrs`. -/
theorem toAdrs_address {layer tree : ℕ} (hl : layer < 2 ^ 32) (ht : tree < 2 ^ 96) :
    toAdrs (Hypertree.address layer tree) = GeneralHypertree.layerAdrs layer tree := by
  apply Adrs.ext <;>
    simp [toAdrs, Hypertree.address, GeneralHypertree.layerAdrs, Adrs.setLayerAddress,
      Adrs.setTreeAddress, Adrs.zero, AddressType.code] <;> omega

/-- The base address of a hypertree position is the paper's address at its layer and tree. -/
theorem LayerPosition.toAdrs_eq (pos : LayerPosition FIPS205.params) :
    pos.toAdrs = toAdrs (Hypertree.address pos.layer.val pos.tree.val) := by
  have hl : pos.layer.val < 7 := pos.layer.isLt
  have ht := pos.tree.isLt
  have hheight : layerTreeHeight FIPS205.params pos.layer.val ≤ 96 := by
    change (7 - (pos.layer.val + 1)) * 9 ≤ 96
    omega
  rw [toAdrs_address (by omega)
    (lt_of_lt_of_le ht (Nat.pow_le_pow_right (by norm_num) hheight))]
  rfl

/-- The layer-zero hypertree position of an answer is at the paper's tree index. -/
theorem initial_tree_val_parts (h : HashOutput) :
    (LayerPosition.initial FIPS205.params (parts h)).tree.val =
      (MessageDigest.treeIndex h).toNat :=
  idxTree_val_parts h

/-- The layer-zero hypertree position of an answer is at the paper's leaf index. -/
theorem initial_leaf_val_parts (h : HashOutput) :
    (LayerPosition.initial FIPS205.params (parts h)).leaf.val =
      (MessageDigest.leafIndex h).toNat :=
  idxLeaf_val_parts h

/-- The root address of key generation: layer `d - 1`, tree `0`. -/
theorem toAdrs_address_top :
    toAdrs (Hypertree.address (layers - 1) 0) =
      GeneralHypertree.layerAdrs (FIPS205.params.params.d - 1) 0 :=
  toAdrs_address (by decide) (by decide)

/-- **XMSS leaves**: the paper's `Merkle.wotsAddress` is FIPS 205's `wotsLeafAdrs`. -/
theorem toAdrs_wotsAddress (a : Address) {index : ℕ} (hi : index < 2 ^ 32) :
    toAdrs (Merkle.wotsAddress a index) = wotsLeafAdrs (toAdrs a) index := by
  apply Adrs.ext <;>
    simp [toAdrs, Merkle.wotsAddress, wotsLeafAdrs, Address.setTypeAndClear,
      Adrs.setTypeAndClear, Adrs.setKeyPairAddress, AddressType.code, AddrType.toCode,
      Nat.mod_eq_of_lt (show index < 4294967296 by omega)]

/-- **XMSS nodes**: the paper's `Merkle.nodeAddress` is FIPS 205's `xmssNodeAdrs`. -/
theorem toAdrs_merkleNodeAddress (a : Address) {height index : ℕ} (hz : height < 2 ^ 32)
    (hi : index < 2 ^ 32) :
    toAdrs (Merkle.nodeAddress a height index) = xmssNodeAdrs (toAdrs a) height index := by
  apply Adrs.ext <;>
    simp [toAdrs, Merkle.nodeAddress, xmssNodeAdrs, Address.setTypeAndClear,
      Adrs.setTypeAndClear, Adrs.setTreeHeight, Adrs.setTreeIndex, AddressType.code,
      AddrType.toCode] <;>
    omega

/-- **WOTS+ secret values**: the paper's `Wots.secretAddress` is FIPS 205's `wotsSkAdrs`. -/
theorem toAdrs_wotsSecretAddress (a : Address) (i : Fin chains) :
    toAdrs (Wots.secretAddress a i) = wotsSkAdrs (toAdrs a) i.val := by
  have hi : i.val < 35 := i.isLt
  apply Adrs.ext <;>
    simp [toAdrs, Wots.secretAddress, wotsSkAdrs, Address.setTypeAndClear,
      Adrs.setTypeAndClear, Adrs.setKeyPairAddress, Adrs.setChainAddress,
      Adrs.getKeyPairAddress, AddressType.code, AddrType.toCode,
      Nat.mod_eq_of_lt (show i.val < 4294967296 by omega)]

/-- **WOTS+ chains**: at a WOTS+ hash address with a clear hash word, the paper's chain address
`{a with chainOrHeight := i}` is FIPS 205's `wotsChainAdrs`. -/
theorem toAdrs_wotsChainAddress (a : Address) (hk : a.kind = .wotsHash)
    (hh : a.hashOrIndex = 0) (i : Fin chains) :
    toAdrs { a with chainOrHeight := BitVec.ofNat 32 i.val } =
      wotsChainAdrs (toAdrs a) i.val := by
  have hi : i.val < 35 := i.isLt
  apply Adrs.ext <;>
    simp [toAdrs, wotsChainAdrs, Adrs.setTypeAndClear, Adrs.setKeyPairAddress,
      Adrs.setChainAddress, Adrs.getKeyPairAddress, hk, hh, AddressType.code,
      AddrType.toCode, Nat.mod_eq_of_lt (show i.val < 4294967296 by omega)]

/-- **WOTS+ chain steps**: the paper's step address `{a with hashOrIndex := j}` is FIPS 205's
`setHashAddress j`. -/
theorem toAdrs_chainStepAddress (a : Address) {j : ℕ} (hj : j < 2 ^ 32) :
    toAdrs { a with hashOrIndex := BitVec.ofNat 32 j } = (toAdrs a).setHashAddress j :=
  toAdrs_setHash a hj

/-- **WOTS+ public keys**: the paper's `Wots.publicKeyAddress` is FIPS 205's `wotsPkAdrs`. -/
theorem toAdrs_wotsPublicKeyAddress (a : Address) :
    toAdrs (Wots.publicKeyAddress a) = wotsPkAdrs (toAdrs a) := by
  apply Adrs.ext <;>
    simp [toAdrs, Wots.publicKeyAddress, wotsPkAdrs, Address.setTypeAndClear,
      Adrs.setTypeAndClear, Adrs.setKeyPairAddress, Adrs.getKeyPairAddress, AddressType.code,
      AddrType.toCode]

/-- **FORS secret values**: the paper's `Fors.secretAddress` is FIPS 205's `forsSkAdrs`. -/
theorem toAdrs_forsSecretAddress (a : Address) {index : ℕ} (hi : index < 2 ^ 32) :
    toAdrs (Fors.secretAddress a index) = forsSkAdrs (toAdrs a) index := by
  apply Adrs.ext <;>
    simp [toAdrs, Fors.secretAddress, forsSkAdrs, Address.setTypeAndClear,
      Adrs.setTypeAndClear, Adrs.setKeyPairAddress, Adrs.setTreeIndex, Adrs.getKeyPairAddress,
      AddressType.code, AddrType.toCode, Nat.mod_eq_of_lt (show index < 4294967296 by omega)]

/-- **FORS nodes**: at a FORS-tree address, the paper's `Fors.nodeAddress` is FIPS 205's
`forsNodeAdrs`. -/
theorem toAdrs_forsNodeAddress (a : Address) (hk : a.kind = .forsTree) {height index : ℕ}
    (hz : height < 2 ^ 32) (hi : index < 2 ^ 32) :
    toAdrs (Fors.nodeAddress a height index) = forsNodeAdrs (toAdrs a) height index := by
  apply Adrs.ext <;>
    simp [toAdrs, Fors.nodeAddress, forsNodeAdrs, Adrs.setTypeAndClear,
      Adrs.setKeyPairAddress, Adrs.setTreeHeight, Adrs.setTreeIndex, Adrs.getKeyPairAddress,
      hk, AddressType.code, AddrType.toCode] <;>
    omega

/-- **FORS public keys**: the paper's FORS-roots address is FIPS 205's `forsPkAdrs`. -/
theorem toAdrs_forsRootsAddress (a : Address) :
    toAdrs { a.setTypeAndClear .forsRoots with keyPair := a.keyPair } =
      forsPkAdrs (toAdrs a) := by
  apply Adrs.ext <;>
    simp [toAdrs, forsPkAdrs, Address.setTypeAndClear, Adrs.setTypeAndClear,
      Adrs.setKeyPairAddress, Adrs.getKeyPairAddress, AddressType.code, AddrType.toCode]

/-- **The FORS address of a digest**: the paper's `Scheme.forsAddress` is FIPS 205's
`DigestParts.forsAdrs` of the parsed answer. -/
theorem toAdrs_forsAddress (h : HashOutput) :
    toAdrs (Scheme.forsAddress h) = (parts h).forsAdrs := by
  have ht : (MessageDigest.treeIndex h).toNat < 2 ^ 54 := (MessageDigest.treeIndex h).isLt
  have hl : (MessageDigest.leafIndex h).toNat < 2 ^ 9 := (MessageDigest.leafIndex h).isLt
  apply Adrs.ext
  · rfl
  · change (BitVec.ofNat 96 (MessageDigest.treeIndex h).toNat).toNat = (parts h).idxTree.val
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), idxTree_val_parts]
  · rfl
  · change (BitVec.ofNat 32 (MessageDigest.leafIndex h).toNat).toNat = (parts h).idxLeaf.val
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), idxLeaf_val_parts]
  · rfl
  · rfl

/-! ## Signatures -/

/-- The FIPS 205 structured signature at SLH-DSA-SHAKE-128s. -/
abbrev CoreSignature : Type := SignatureCore FIPS205.params.params FIPS205.core

/-- The atomic wire codec of the SHAKE context. -/
abbrev wireCodec : CoreWireCodec FIPS205.params.params FIPS205.core :=
  Concrete.shakeWireCodec FIPS205.params.params

/-- FORS tree signatures are equal when their fields are. -/
theorem forsTreeSigCore_ext {x y : ForsTreeSigCore FIPS205.params.params FIPS205.core}
    (hsk : x.sk = y.sk) (hauth : x.auth = y.auth) : x = y := by
  cases x
  cases y
  simp_all

/-- XMSS signatures are equal when their fields are. -/
theorem xmssSigCore_ext {x y : XmssSigCore FIPS205.params.params FIPS205.core}
    (hwots : x.wots = y.wots) (hauth : x.auth = y.auth) : x = y := by
  cases x
  cases y
  simp_all

/-- The paper's FORS tree signature of a FIPS 205 one. -/
@[expose] def forsTreeOfCore (t : ForsTreeSigCore FIPS205.params.params FIPS205.core) :
    ForsTreeSignature where
  secret := digestEquiv.symm t.sk
  authentication j := digestEquiv.symm (t.auth[j.val]'j.isLt)

/-- FIPS 205's FORS tree signature of a paper one. -/
@[expose] def forsTreeToCore (t : ForsTreeSignature) :
    ForsTreeSigCore FIPS205.params.params FIPS205.core where
  sk := digestEquiv t.secret
  auth := Vector.ofFn fun j => digestEquiv (t.authentication j)

/-- The paper's XMSS signature of a FIPS 205 one. -/
@[expose] def xmssOfCore (t : XmssSigCore FIPS205.params.params FIPS205.core) : XmssSignature where
  wots j := digestEquiv.symm (t.wots[j.val]'j.isLt)
  authentication j := digestEquiv.symm (t.auth[j.val]'j.isLt)

/-- FIPS 205's XMSS signature of a paper one. -/
@[expose] def xmssToCore (t : XmssSignature) : XmssSigCore FIPS205.params.params FIPS205.core where
  wots := Vector.ofFn fun j => digestEquiv (t.wots j)
  auth := Vector.ofFn fun j => digestEquiv (t.authentication j)

/-- **The paper's signature of a FIPS 205 structured signature**: every node read as a digest,
FORS trees and hypertree layers in the same order. -/
@[expose] def sigOfCore (σ : CoreSignature) : Signature where
  randomizer := digestEquiv.symm σ.randomness
  fors i := forsTreeOfCore (σ.fors[i.val]'i.isLt)
  hypertree i := xmssOfCore (σ.hypertree[i.val]'i.isLt)

/-- FIPS 205's structured signature of a paper signature. -/
@[expose] def sigToCore (s : Signature) : CoreSignature where
  randomness := digestEquiv s.randomizer
  fors := Vector.ofFn fun i => forsTreeToCore (s.fors i)
  hypertree := Vector.ofFn fun i => xmssToCore (s.hypertree i)

/-- **Signatures of the two schemes are in bijection** (`sigOfCore`, `sigToCore`). -/
@[expose] def signatureEquiv : CoreSignature ≃ Signature where
  toFun := sigOfCore
  invFun := sigToCore
  left_inv σ := by
    rcases σ with ⟨r, f, ht⟩
    simp only [sigToCore, sigOfCore, Equiv.apply_symm_apply]
    congr 1
    · apply Vector.ext
      intro i hi
      simp only [Vector.getElem_ofFn]
      apply forsTreeSigCore_ext
      · simp [forsTreeToCore, forsTreeOfCore]
        rfl
      · apply Vector.ext
        intro j hj
        simp [forsTreeToCore, forsTreeOfCore]
        rfl
    · apply Vector.ext
      intro i hi
      simp only [Vector.getElem_ofFn]
      apply xmssSigCore_ext
      · apply Vector.ext
        intro j hj
        simp [xmssToCore, xmssOfCore]
        rfl
      · apply Vector.ext
        intro j hj
        simp [xmssToCore, xmssOfCore]
        rfl
  right_inv s := by
    rcases s with ⟨r, f, ht⟩
    simp only [sigToCore, sigOfCore, Equiv.symm_apply_apply]
    congr 1
    · funext i
      simp only [forsTreeToCore, forsTreeOfCore, Equiv.symm_apply_apply, Vector.getElem_ofFn]
      rfl
    · funext i
      simp only [xmssToCore, xmssOfCore, Equiv.symm_apply_apply, Vector.getElem_ofFn]
      rfl

/-- `signatureEquiv` is `sigOfCore`. -/
@[simp] theorem signatureEquiv_apply (σ : CoreSignature) : signatureEquiv σ = sigOfCore σ := rfl

/-- The inverse of `signatureEquiv` is `sigToCore`. -/
@[simp] theorem signatureEquiv_symm_apply (s : Signature) :
    signatureEquiv.symm s = sigToCore s := rfl

/-- The atomic SHAKE codec writes a node as its own bytes. -/
theorem wireCodec_y_encode (v : FIPS205.core.Y) :
    wireCodec.y.encode v = Vector.toList (v : Node) := rfl

/-- **Signature bytes**: the paper's `Signature.toBytes` of `sigOfCore σ` is FIPS 205's
canonical encoding of `σ`. -/
theorem toBytes_sigOfCore (σ : CoreSignature) :
    (sigOfCore σ).toBytes = encodeSignature FIPS205.params wireCodec σ := by
  rw [encodeSignature_eq]
  simp only [Signature.toBytes, ForsTreeSignature.toBytes, XmssSignature.toBytes,
    digestArrayBytes, sigOfCore, forsTreeOfCore, xmssOfCore, bytesBE_digestEquiv_symm,
    wireCodec_y_encode, List.append_assoc]
  rfl

/-! ### Parsing -/

/-- One step of the paper's big-endian fold: shift in a byte. -/
theorem shiftLeft_or_ofNat (acc : BitVec 128) (b : UInt8) :
    (acc <<< 8) ||| BitVec.ofNat 128 b.toNat = BitVec.ofNat 128 (acc.toNat * 256 + b.toNat) := by
  have hb : b.toNat < 2 ^ 8 := b.toNat_lt
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_or, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (show b.toNat < 2 ^ 128 by omega), Nat.shiftLeft_eq]
  have h : acc.toNat * 2 ^ 8 % 2 ^ 128 = (acc.toNat % 2 ^ 120) <<< 8 := by
    rw [Nat.shiftLeft_eq]
    omega
  rw [h, ← Nat.shiftLeft_add_eq_or_of_lt hb, Nat.shiftLeft_eq]
  omega

/-- The paper's big-endian fold computes `acc · 256 ^ |l| + toInt l`, modulo `2 ^ 128`. -/
theorem foldl_shiftLeft_or (l : List UInt8) (acc : BitVec 128) :
    l.foldl (fun (value : BitVec 128) (byte : UInt8) => (value <<< 8) |||
      BitVec.ofNat 128 byte.toNat) acc =
      BitVec.ofNat 128 (acc.toNat * 256 ^ l.length + toInt l) := by
  induction l generalizing acc with
  | nil => simp
  | cons b l ih =>
    rw [List.foldl_cons, shiftLeft_or_ofNat, ih]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ofNat, List.length_cons]
    rw [show b :: l = [b] ++ l from rfl, toInt_append]
    have hcongr : ∀ x y : ℕ, x % 2 ^ 128 = y % 2 ^ 128 →
        (x * 256 ^ l.length + toInt l) % 2 ^ 128 = (y * 256 ^ l.length + toInt l) % 2 ^ 128 := by
      intro x y hxy
      rw [Nat.add_mod, Nat.mul_mod, hxy, ← Nat.mul_mod, ← Nat.add_mod]
    rw [hcongr _ ((acc.toNat * 256 + b.toNat)) (Nat.mod_mod _ _)]
    congr 1
    simp [toInt, pow_succ]
    ring

/-- The paper's `readDigest` is the big-endian value of the `16` bytes at the offset. -/
theorem readDigest_eq (input : Bytes) (offset : ℕ) :
    Signature.readDigest input offset =
      BitVec.ofNat 128 (toInt ((input.drop offset).take 16)) := by
  unfold Signature.readDigest
  exact (foldl_shiftLeft_or ((input.drop offset).take 16) 0).trans (by simp)

/-- Reading `16` bytes that are a node's bytes gives that node's digest. -/
theorem readDigest_of_slice {input : Bytes} {offset : ℕ} {v : FIPS205.core.Y}
    (h : (input.drop offset).take FIPS205.params.params.n = Vector.toList (v : Node)) :
    Signature.readDigest input offset = digestEquiv.symm v := by
  rw [readDigest_eq]
  exact congrArg (BitVec.ofNat 128 ∘ toInt) h

/-- `len = 35` WOTS+ chains at SLH-DSA-SHAKE-128s. -/
theorem params_len : FIPS205.params.params.len = 35 := by decide

/-- The paper's and FIPS 205's signature lengths agree: `7856` bytes. -/
theorem params_signatureBytes : FIPS205.params.params.signatureBytes = signatureBytes := by
  decide

/-- **Parsing FIPS 205's encoding**: the paper's `Signature.fromBytes?` reads FIPS 205's canonical
encoding of `σ` as `sigOfCore σ`. -/
theorem fromBytes?_encodeSignature (σ : CoreSignature) :
    Signature.fromBytes? (encodeSignature FIPS205.params wireCodec σ) = some (sigOfCore σ) := by
  have hlen : (encodeSignature FIPS205.params wireCodec σ).length = signatureBytes :=
    (encodeSignature_length _ _ _).trans params_signatureBytes
  unfold Signature.fromBytes?
  rw [ite_eq_left_of_eq_true _ _ (eq_true hlen)]
  refine congrArg some ?_
  unfold sigOfCore
  rw [Signature.mk.injEq]
  refine ⟨?_, ?_, ?_⟩
  · exact readDigest_of_slice (encodeSignature_randomness_slice FIPS205.params wireCodec σ)
  · funext i
    have hi : i.val < 14 := i.isLt
    simp only [forsTreeOfCore, ForsTreeSignature.mk.injEq]
    constructor
    · rw [show n * (1 + i.val * (1 + forsHeight)) =
          WireLayout.forsSecretOffset FIPS205.params.params i.val by
        simp only [WireLayout.forsSecretOffset, WireLayout.forsTreeOffset, WireLayout.forsOffset,
          WireLayout.forsTreeBytes]
        change 16 * (1 + i.val * (1 + 12)) = 16 + i.val * ((1 + 12) * 16)
        ring]
      exact readDigest_of_slice
        (encodeSignature_forsSecret_slice FIPS205.params wireCodec σ ⟨i.val, hi⟩)
    · funext j
      have hj : j.val < 12 := j.isLt
      rw [show n * (2 + i.val * (1 + forsHeight) + j.val) =
          WireLayout.forsAuthOffset FIPS205.params.params i.val j.val by
        simp only [WireLayout.forsAuthOffset, WireLayout.forsTreeOffset, WireLayout.forsOffset,
          WireLayout.forsTreeBytes]
        change 16 * (2 + i.val * (1 + 12) + j.val) = 16 + i.val * ((1 + 12) * 16) +
          (1 + j.val) * 16
        ring]
      exact readDigest_of_slice
        (encodeSignature_forsAuth_slice FIPS205.params wireCodec σ ⟨i.val, hi⟩ ⟨j.val, hj⟩)
  · funext i
    have hi : i.val < 7 := i.isLt
    simp only [xmssOfCore, XmssSignature.mk.injEq]
    constructor
    · funext j
      have hj : j.val < 35 := j.isLt
      rw [show n * (1 + forsTrees * (1 + forsHeight) + i.val * (chains + subtreeHeight) +
            j.val) = WireLayout.wotsOffset FIPS205.params.params i.val j.val by
        simp only [WireLayout.wotsOffset, WireLayout.xmssOffset, WireLayout.hypertreeOffset,
          WireLayout.forsOffset, WireLayout.forsBytes, WireLayout.forsTreeBytes,
          WireLayout.xmssBytes, params_len]
        change 16 * (1 + 14 * (1 + 12) + i.val * (35 + 9) + j.val) =
          16 + 14 * ((1 + 12) * 16) + i.val * ((35 + 9) * 16) + j.val * 16
        ring]
      exact readDigest_of_slice
        (encodeSignature_wots_slice FIPS205.params wireCodec σ ⟨i.val, hi⟩
          ⟨j.val, params_len ▸ hj⟩)
    · funext j
      have hj : j.val < 9 := j.isLt
      rw [show n * (1 + forsTrees * (1 + forsHeight) + i.val * (chains + subtreeHeight) +
            chains + j.val) = WireLayout.xmssAuthOffset FIPS205.params.params i.val j.val by
        simp only [WireLayout.xmssAuthOffset, WireLayout.xmssOffset, WireLayout.hypertreeOffset,
          WireLayout.forsOffset, WireLayout.forsBytes, WireLayout.forsTreeBytes,
          WireLayout.xmssBytes, params_len]
        change 16 * (1 + 14 * (1 + 12) + i.val * (35 + 9) + 35 + j.val) =
          16 + 14 * ((1 + 12) * 16) + i.val * ((35 + 9) * 16) + (35 + j.val) * 16
        ring]
      exact readDigest_of_slice
        (encodeSignature_xmssAuth_slice FIPS205.params wireCodec σ ⟨i.val, hi⟩ ⟨j.val, hj⟩)

/-- **Signature parsing**: the paper's `Signature.fromBytes?` accepts exactly the strings FIPS 205's
`decodeSignature` accepts, with the corresponding signature. -/
theorem fromBytes?_eq (bs : Bytes) :
    Signature.fromBytes? bs =
      sigOfCore <$> (decodeSignature FIPS205.params wireCodec bs).toOption := by
  cases hdec : decodeSignature FIPS205.params wireCodec bs with
  | error e =>
    have hlen : bs.length ≠ signatureBytes := by
      intro hlen
      rw [decodeSignature, WireCodec.decode, decodeExact,
        dite_eq_left_of_eq_true (eq_true (hlen.trans params_signatureBytes.symm))] at hdec
      cases hdec
    simp [Signature.fromBytes?, hlen, Except.toOption]
  | ok σ =>
    rw [(decodeSignature_eq_ok_iff _ _ _ _).mp hdec, fromBytes?_encodeSignature]
    rfl

/-! ## Oracle inputs

FIPS 205's single-oracle layouts (`SLHDSA.Security.encode`) at paper values are the paper's
oracle inputs. -/

/-- **Tweakable hash and `PRF` inputs**: at a FIPS 205 address `A` with the paper bytes of `a`,
the layout `PK.seed ‖ ADRS ‖ M_1 ‖ … ‖ M_ℓ` is the paper's `Hashing.tweakableInput`. -/
theorem encode_thash (seed : Digest) {A : Adrs} {a : Address} (hA : A.toBytes = a.toBytes)
    (xs : List Digest) :
    SLHDSA.Security.encode FIPS205.params
        (.inl (.thash (digestEquiv seed) (FIPS205.core.adrsToKey A) (xs.map digestEquiv))) =
      Hashing.tweakableInput seed a (xs.map (bytesBE n)).flatten := by
  change Vector.toList (digestEquiv seed : Node) ++
      Vector.toList (FIPS205.core.adrsToKey A : SLHDSA.Bytes 32) ++
      ((xs.map digestEquiv).map fun x : FIPS205.core.Y => Vector.toList (x : Node)).flatten = _
  rw [List.map_map, toList_digestEquiv, toList_adrsToKey, hA]
  rfl

/-- The tweakable-hash input at the FIPS 205 address `toAdrs a`. -/
theorem encode_thash_toAdrs (seed : Digest) (a : Address) (xs : List Digest) :
    SLHDSA.Security.encode FIPS205.params
        (.inl (.thash (digestEquiv seed) (FIPS205.core.adrsToKey (toAdrs a))
          (xs.map digestEquiv))) =
      Hashing.tweakableInput seed a (xs.map (bytesBE n)).flatten :=
  encode_thash seed (toBytes_toAdrs a) xs

/-- **`H_msg` inputs**: the layout `R ‖ PK.seed ‖ PK.root ‖ M` is the paper's
`Hashing.messageInput`. -/
theorem encode_hmsg (r : Digest) (pk : PublicKey) (msg : Bytes) :
    SLHDSA.Security.encode FIPS205.params
        (.inl (.hmsg (digestEquiv r) (digestEquiv pk.seed) (digestEquiv pk.root) msg)) =
      Hashing.messageInput r pk msg := by
  rfl

/-- **`PRF_msg` inputs**: the layout `SK.prf ‖ opt_rand ‖ M` is the paper's
`Hashing.randomizerInput`. -/
theorem encode_prfMsg (prf seed : Digest) (msg : Bytes) :
    SLHDSA.Security.encode FIPS205.params
        (.inr ⟨digestEquiv prf, digestEquiv seed, msg⟩) =
      Hashing.randomizerInput prf seed msg := by
  rfl

/-! ## Uniform sampling -/

open SampleableType in
/-- A uniform digest is a uniform node. -/
theorem map_digestEquiv_uniformSample :
    digestEquiv <$> ($ᵗ Digest : ProbComp Digest) =ᵈ ($ᵗ FIPS205.core.Y : ProbComp _) :=
  map_uniformSample_evalDistEq_of_bijective digestEquiv.bijective

open SampleableType in
/-- A uniform digest is a uniform public seed. -/
theorem map_digestEquiv_uniformSample_pkSeed :
    (digestEquiv : Digest → FIPS205.core.PkSeed) <$> ($ᵗ Digest : ProbComp Digest) =ᵈ
      ($ᵗ FIPS205.core.PkSeed : ProbComp _) :=
  map_uniformSample_evalDistEq_of_bijective digestEquiv.bijective

open SampleableType in
/-- A uniform digest is a uniform secret seed. -/
theorem map_digestEquiv_uniformSample_skSeed :
    (digestEquiv : Digest → FIPS205.core.SkSeed) <$> ($ᵗ Digest : ProbComp Digest) =ᵈ
      ($ᵗ FIPS205.core.SkSeed : ProbComp _) :=
  map_uniformSample_evalDistEq_of_bijective digestEquiv.bijective

open SampleableType in
/-- A uniform digest is a uniform message-PRF key. -/
theorem map_digestEquiv_uniformSample_skPrf :
    (digestEquiv : Digest → FIPS205.core.SkPrf) <$> ($ᵗ Digest : ProbComp Digest) =ᵈ
      ($ᵗ FIPS205.core.SkPrf : ProbComp _) :=
  map_uniformSample_evalDistEq_of_bijective digestEquiv.bijective

open SampleableType in
/-- A uniform digest is a uniform `16`-byte vector. -/
theorem map_digestEquiv_uniformSample_bytes :
    (digestEquiv : Digest → SLHDSA.Bytes 16) <$> ($ᵗ Digest : ProbComp Digest) =ᵈ
      ($ᵗ (SLHDSA.Bytes 16) : ProbComp _) :=
  map_uniformSample_evalDistEq_of_bijective digestEquiv.bijective

open SampleableType in
/-- **A uniform paper answer is a uniform FIPS 205 answer.** -/
theorem map_answerEquiv_uniformSample :
    answerEquiv <$> ($ᵗ HashOutput : ProbComp HashOutput) =ᵈ
      ($ᵗ FIPS205.Answer : ProbComp _) :=
  map_uniformSample_evalDistEq_of_bijective answerEquiv.bijective

end SLHDSA.SHAKE128s.Bridge
