/-
Copyright (c) 2026 Tom Wambsgans. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Wambsgans
-/

module

public import HashSig.SLHDSA.SHAKE128s.Proof.Experiment
public import HashSig.SLHDSA.SHAKE128s.Proof.Hashing
public import Mathlib.Tactic.IntervalCases

/-!
# Signature
-/

@[expose] public section

namespace SlhDsaSecurity

theorem ForsTreeSignature.ext {left right : ForsTreeSignature}
    (hsecret : left.secret = right.secret)
    (hauthentication : left.authentication = right.authentication) : left = right := by
  cases left
  cases right
  simp_all

theorem XmssSignature.ext {left right : XmssSignature}
    (hwots : left.wots = right.wots)
    (hauthentication : left.authentication = right.authentication) : left = right := by
  cases left
  cases right
  simp_all

@[simp] theorem digestArrayBytes_length {size : Nat} (values : Fin size → Digest) :
    (digestArrayBytes values).length = size * n := by
  induction size with
  | zero => simp [digestArrayBytes]
  | succ size ih =>
    simp only [digestArrayBytes, List.ofFn_succ, List.flatten_cons, List.length_append,
      length_bytesBE]
    change n + (digestArrayBytes (fun i => values i.succ)).length = _
    rw [ih]
    simp [Nat.succ_mul, Nat.add_comm]

@[simp] theorem XmssSignature.toBytes_length (signature : XmssSignature) :
    signature.toBytes.length = (chains + subtreeHeight) * n := by
  simp [XmssSignature.toBytes, Nat.add_mul]

@[simp] theorem ForsTreeSignature.toBytes_length (signature : ForsTreeSignature) :
    signature.toBytes.length = (1 + forsHeight) * n := by
  simp [ForsTreeSignature.toBytes, Nat.add_mul]

@[simp] theorem Signature.toBytes_length (signature : Signature) :
    signature.toBytes.length = signatureBytes := by
  simp only [Signature.toBytes, List.length_append, length_bytesBE, List.length_flatten,
    List.map_ofFn, Function.comp_def, ForsTreeSignature.toBytes_length,
    XmssSignature.toBytes_length, List.sum_ofFn, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, smul_eq_mul]
  simp [signatureBytes, layers, totalHeight, subtreeHeight, forsTrees,
    forsHeight, chains, messageDigits, checksumDigits, winternitzBits, n]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
/-- The big-endian fold of the sixteen bytes of a `128`-bit value rebuilds that value. -/
private theorem foldl_bytes128 (value : BitVec 128) :
    ((List.ofFn fun i : Fin 16 => UInt8.ofBitVec (value.extractLsb' (8 * i.val) 8)).reverse).foldl
      (fun (acc : BitVec 128) (byte : UInt8) => (acc <<< 8) ||| BitVec.ofNat 128 byte.toNat) 0 =
      value := by
  simp only [List.ofFn_succ, List.ofFn_zero, List.reverse_cons, List.reverse_nil, List.nil_append,
    List.cons_append, List.foldl_cons, List.foldl_nil, Fin.val_zero, Fin.val_succ, Nat.reduceAdd,
    Nat.reduceMul]
  have widen (byte : BitVec 8) :
      BitVec.ofNat 128 (UInt8.ofBitVec byte).toNat = byte.setWidth 128 := by
    apply BitVec.eq_of_toNat_eq
    simp
  simp only [widen]
  clear widen
  apply BitVec.eq_of_getLsbD_eq
  intro bit hbit
  interval_cases bit <;>
    simp only [BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth,
      BitVec.getLsbD_extractLsb'] <;> simp

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem Signature.readDigest_bytesBE (value : Digest) :
    readDigest (bytesBE n value) 0 = value := by
  unfold readDigest
  rw [List.drop_zero, List.take_of_length_le (by simp)]
  exact foldl_bytes128 value

theorem Signature.readDigest_append_prefix (front input : Bytes) (offset : Nat) :
    readDigest (front ++ input) (front.length + offset) = readDigest input offset := by
  simp only [readDigest, ← List.drop_drop, List.drop_append_length]

theorem Signature.readDigest_append_suffix (input suffix : Bytes) (offset : Nat)
    (h : offset + n ≤ input.length) :
    readDigest (input ++ suffix) offset = readDigest input offset := by
  simp only [readDigest]
  rw [List.drop_append_of_le_length (by omega),
    List.take_append_of_le_length (by simp only [List.length_drop]; omega)]

theorem Signature.readDigest_field (value : Digest) (suffix : Bytes) :
    readDigest (bytesBE n value ++ suffix) 0 = value := by
  rw [readDigest_append_suffix _ _ _ (by simp), readDigest_bytesBE]

/-- Reading a field inside equally sized serialized blocks selects the intended block. -/
theorem Signature.readDigest_flatten {size : Nat} (blocks : Fin size → Bytes)
    (blockBytes : Nat) (hlen : ∀ i, (blocks i).length = blockBytes) (i : Fin size)
    (offset : Nat) (hoffset : offset + n ≤ blockBytes) (suffix : Bytes) :
    readDigest ((List.ofFn blocks).flatten ++ suffix) (i.val * blockBytes + offset) =
      readDigest (blocks i) offset := by
  induction size with
  | zero => exact Fin.elim0 i
  | succ size ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · simpa only [Fin.val_zero, Nat.zero_mul, Nat.zero_add, List.ofFn_succ,
        List.flatten_cons, List.append_assoc] using
        readDigest_append_suffix (blocks 0)
          ((List.ofFn fun j => blocks j.succ).flatten ++ suffix) offset
          (by rw [hlen]; exact hoffset)
    · simp only [Fin.val_succ, List.ofFn_succ, List.flatten_cons, List.append_assoc]
      rw [show (j.val + 1) * blockBytes + offset =
        (blocks 0).length + (j.val * blockBytes + offset) by
          rw [hlen]; simp [Nat.add_mul, Nat.add_comm, Nat.add_left_comm]]
      rw [readDigest_append_prefix]
      exact ih (fun j => blocks j.succ) (fun j => hlen j.succ) j

theorem Signature.readDigest_digestArray {size : Nat} (values : Fin size → Digest)
    (i : Fin size) (suffix : Bytes) :
    readDigest (digestArrayBytes values ++ suffix) (i.val * n) = values i := by
  have h := readDigest_flatten (fun j => bytesBE n (values j)) n (by simp) i 0
    (by omega) suffix
  simpa only [digestArrayBytes, Nat.add_zero, readDigest_bytesBE] using h

theorem Signature.readDigest_randomizer (signature : Signature) :
    readDigest signature.toBytes 0 = signature.randomizer := by
  simp only [Signature.toBytes, List.append_assoc]
  exact readDigest_field _ _

theorem Signature.readDigest_fors (signature : Signature) (i : Fin forsTrees)
    (offset : Nat) (hoffset : offset + n ≤ (1 + forsHeight) * n) :
    readDigest signature.toBytes (n + i.val * ((1 + forsHeight) * n) + offset) =
      readDigest (signature.fors i).toBytes offset := by
  simp only [Signature.toBytes, List.append_assoc]
  rw [show n + i.val * ((1 + forsHeight) * n) + offset =
    (bytesBE n signature.randomizer).length + (i.val * ((1 + forsHeight) * n) + offset) by
      simp [Nat.add_assoc]]
  rw [readDigest_append_prefix]
  exact readDigest_flatten (fun j => (signature.fors j).toBytes) ((1 + forsHeight) * n)
    (by simp) i offset hoffset _

theorem Signature.readDigest_hypertree (signature : Signature) (i : Fin layers)
    (offset : Nat) (hoffset : offset + n ≤ (chains + subtreeHeight) * n) :
    readDigest signature.toBytes
        (n + forsTrees * ((1 + forsHeight) * n) + i.val * ((chains + subtreeHeight) * n) + offset) =
      readDigest (signature.hypertree i).toBytes offset := by
  let front := bytesBE n signature.randomizer ++
    (List.ofFn fun j => (signature.fors j).toBytes).flatten
  have hfront : front.length = n + forsTrees * ((1 + forsHeight) * n) := by
    simp [front, List.length_flatten, List.map_ofFn, Function.comp_def,
      List.ofFn_const, List.sum_replicate]
  change readDigest (front ++ _) _ = _
  rw [show n + forsTrees * ((1 + forsHeight) * n) +
      i.val * ((chains + subtreeHeight) * n) + offset =
        front.length + (i.val * ((chains + subtreeHeight) * n) + offset) by
          rw [hfront]; omega]
  rw [readDigest_append_prefix]
  simpa only [List.append_nil] using readDigest_flatten
    (fun j => (signature.hypertree j).toBytes) ((chains + subtreeHeight) * n)
    (by simp) i offset hoffset []

theorem Signature.readDigest_fors_secret (signature : Signature) (i : Fin forsTrees) :
    readDigest signature.toBytes (n * (1 + i.val * (1 + forsHeight))) =
      (signature.fors i).secret := by
  rw [show n * (1 + i.val * (1 + forsHeight)) =
    n + i.val * ((1 + forsHeight) * n) + 0 by dsimp [n, forsHeight]; omega]
  rw [readDigest_fors _ _ _ (by decide)]
  exact readDigest_field _ _

theorem Signature.readDigest_fors_auth (signature : Signature) (i : Fin forsTrees)
    (j : Fin forsHeight) :
    readDigest signature.toBytes (n * (2 + i.val * (1 + forsHeight) + j.val)) =
      (signature.fors i).authentication j := by
  rw [show n * (2 + i.val * (1 + forsHeight) + j.val) =
    n + i.val * ((1 + forsHeight) * n) + (n + j.val * n) by dsimp [n, forsHeight]; omega]
  rw [readDigest_fors _ _ _ (by have := j.isLt; dsimp [n, forsHeight] at *; omega)]
  simp only [ForsTreeSignature.toBytes]
  rw [show n + j.val * n = (bytesBE n (signature.fors i).secret).length + j.val * n by simp]
  rw [readDigest_append_prefix]
  simpa only [List.append_nil] using readDigest_digestArray (signature.fors i).authentication j []

theorem Signature.readDigest_wots (signature : Signature) (i : Fin layers) (j : Fin chains) :
    readDigest signature.toBytes
        (n * (1 + forsTrees * (1 + forsHeight) + i.val * (chains + subtreeHeight) + j.val)) =
      (signature.hypertree i).wots j := by
  rw [show n * (1 + forsTrees * (1 + forsHeight) + i.val * (chains + subtreeHeight) + j.val) =
    n + forsTrees * ((1 + forsHeight) * n) + i.val * ((chains + subtreeHeight) * n) +
      j.val * n by
        dsimp [n, forsHeight, forsTrees, chains, subtreeHeight, messageDigits, checksumDigits,
          winternitzBits]
        omega]
  rw [readDigest_hypertree _ _ _ (by
    have := j.isLt
    dsimp [chains, messageDigits, checksumDigits, subtreeHeight, winternitzBits, n] at *
    omega)]
  exact readDigest_digestArray _ j _

theorem Signature.readDigest_xmss_auth (signature : Signature) (i : Fin layers)
    (j : Fin subtreeHeight) :
    readDigest signature.toBytes
        (n * (1 + forsTrees * (1 + forsHeight) + i.val * (chains + subtreeHeight) + chains + j.val)) =
      (signature.hypertree i).authentication j := by
  rw [show n * (1 + forsTrees * (1 + forsHeight) + i.val * (chains + subtreeHeight) + chains + j.val) =
    n + forsTrees * ((1 + forsHeight) * n) + i.val * ((chains + subtreeHeight) * n) +
      (chains * n + j.val * n) by
        dsimp [n, forsHeight, forsTrees, chains, subtreeHeight, messageDigits, checksumDigits,
          winternitzBits]
        omega]
  rw [readDigest_hypertree _ _ _ (by
    have := j.isLt
    dsimp [chains, messageDigits, checksumDigits, subtreeHeight, winternitzBits, n] at *
    omega)]
  simp only [XmssSignature.toBytes]
  rw [show chains * n + j.val * n =
    (digestArrayBytes (signature.hypertree i).wots).length + j.val * n by simp]
  rw [readDigest_append_prefix]
  simpa only [List.append_nil] using
    readDigest_digestArray (signature.hypertree i).authentication j []

@[simp] theorem Signature.fromBytes_toBytes (signature : Signature) :
    fromBytes? signature.toBytes = some signature := by
  simp only [fromBytes?, toBytes_length, ↓reduceIte, Option.some.injEq]
  cases signature with
  | mk randomizer fors hypertree =>
    simp only [Signature.mk.injEq]
    refine ⟨readDigest_randomizer _, ?_, ?_⟩
    · funext i
      apply ForsTreeSignature.ext
      · exact readDigest_fors_secret _ i
      · funext j; exact readDigest_fors_auth _ i j
    · funext i
      apply XmssSignature.ext
      · funext j; exact readDigest_wots _ i j
      · funext j; exact readDigest_xmss_auth _ i j

end SlhDsaSecurity
