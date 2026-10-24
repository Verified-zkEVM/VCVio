/-
Copyright (c) 2026 Tom Wambsgans. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Wambsgans
-/

module

public import HashSig.SLHDSA.SHAKE128s.Proof.Signature
public import Mathlib.Data.Fintype.Vector
public import Mathlib.Data.FinEnum

/-!
# Canonical signature encoding

No signature bytes are ignored: decoding and encoding are inverse in both directions. Counting
signatures (`Signature.card`) shows that `Signature.encodeFixed` is a bijection onto byte strings
of the standard length, so every accepted byte string is the canonical encoding of its parsed
signature (`Signature.toBytes_fromBytes`).
-/

public section

namespace SLHDSA.SHAKE128s

/-- An XMSS signature as its pair of fields. -/
private def xmssFields : XmssSignature ≃ WotsSignature × (Fin subtreeHeight → Digest) where
  toFun signature := (signature.wots, signature.authentication)
  invFun fields := ⟨fields.1, fields.2⟩
  left_inv := by intro signature; rfl
  right_inv := by intro fields; rfl

/-- A FORS tree signature as its pair of fields. -/
private def forsFields : ForsTreeSignature ≃ Digest × (Fin forsHeight → Digest) where
  toFun signature := (signature.secret, signature.authentication)
  invFun fields := ⟨fields.1, fields.2⟩
  left_inv := by intro signature; rfl
  right_inv := by intro fields; rfl

/-- A signature as its triple of fields. -/
private def signatureFields : Signature ≃ Digest × ForsSignature × HypertreeSignature where
  toFun signature := (signature.randomizer, signature.fors, signature.hypertree)
  invFun fields := ⟨fields.1, fields.2.1, fields.2.2⟩
  left_inv := by intro signature; rfl
  right_inv := by intro fields; rfl

/-- An XMSS signature is a finite tuple of digests. -/
instance : Finite XmssSignature := Finite.of_equiv _ xmssFields.symm

/-- A FORS tree signature is a finite tuple of digests. -/
instance : Finite ForsTreeSignature := Finite.of_equiv _ forsFields.symm

/-- A signature is a finite tuple of digests. -/
instance : Finite Signature := Finite.of_equiv _ signatureFields.symm

/-- There are exactly `2 ^ (8 * signatureBytes)` signatures. -/
theorem Signature.card : Nat.card Signature = 2 ^ (8 * signatureBytes) := by
  have hdigest : Nat.card Digest = 2 ^ (8 * n) := by
    rw [Nat.card_eq_fintype_card, Fintype.card_bitVec]
  have hxmss : Nat.card XmssSignature = (2 ^ (8 * n)) ^ (chains + subtreeHeight) := by
    rw [Nat.card_congr xmssFields]
    simp only [WotsSignature, Nat.card_prod, Nat.card_fun, Nat.card_fin, hdigest, pow_add]
  have hfors : Nat.card ForsTreeSignature = (2 ^ (8 * n)) ^ (1 + forsHeight) := by
    rw [Nat.card_congr forsFields]
    simp only [Nat.card_prod, Nat.card_fun, Nat.card_fin, hdigest, pow_add, pow_one]
  rw [Nat.card_congr signatureFields]
  simp only [ForsSignature, HypertreeSignature, Nat.card_prod, Nat.card_fun, Nat.card_fin, hxmss,
    hfors, hdigest, ← pow_mul, ← pow_add]
  apply congrArg (fun exponent : Nat => 2 ^ exponent)
  rfl

/-- The encoder into all byte strings of the standard length. -/
@[expose] def Signature.encodeFixed (signature : Signature) : List.Vector UInt8 signatureBytes :=
  ⟨signature.toBytes, signature.toBytes_length⟩

/-- The fixed-length encoding is injective. -/
theorem Signature.encodeFixed_injective : Function.Injective encodeFixed := by
  intro left right h
  have hbytes := congrArg Subtype.val h
  have hdecoded := congrArg Signature.fromBytes? hbytes
  simpa only [encodeFixed, fromBytes_toBytes, Option.some.injEq] using hdecoded

/-- The fixed-length encoding is a bijection onto byte strings of the standard length. -/
theorem Signature.encodeFixed_bijective : Function.Bijective encodeFixed := by
  refine encodeFixed_injective.bijective_of_nat_card_le (le_of_eq ?_)
  rw [card, Nat.card_congr (Equiv.vectorEquivFin UInt8 signatureBytes), Nat.card_fun,
    Nat.card_fin, Nat.card_eq_fintype_card (α := UInt8), ← FinEnum.card_eq_fintypeCard,
    FinEnum.card_UInt8, pow_mul]

/-- Every accepted byte string is precisely the canonical encoding of its parsed signature. -/
theorem Signature.toBytes_fromBytes {input : Bytes} {signature : Signature}
    (h : fromBytes? input = some signature) : signature.toBytes = input := by
  have hlen : input.length = signatureBytes := by
    unfold fromBytes? at h
    split at h <;> simp_all
  obtain ⟨original, horiginal⟩ := encodeFixed_bijective.surjective ⟨input, hlen⟩
  have hbytes : original.toBytes = input := congrArg Subtype.val horiginal
  have hsignature : original = signature := by
    rw [← hbytes, fromBytes_toBytes] at h
    exact Option.some.inj h
  exact hsignature ▸ hbytes

end SLHDSA.SHAKE128s
