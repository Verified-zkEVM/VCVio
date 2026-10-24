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

namespace SlhDsaSecurity

deriving instance Fintype for XmssSignature
deriving instance Fintype for ForsTreeSignature
deriving instance Fintype for Signature

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

/-- There are exactly `2 ^ (8 * signatureBytes)` signatures. -/
theorem Signature.card : Fintype.card Signature = 2 ^ (8 * signatureBytes) := by
  have hxmss : Fintype.card XmssSignature = (2 ^ (8 * n)) ^ (chains + subtreeHeight) := by
    rw [Fintype.card_congr xmssFields]
    simp only [WotsSignature, Fintype.card_prod, Fintype.card_fun, Fintype.card_fin,
      Digest, Fintype.card_bitVec, pow_add]
  have hfors : Fintype.card ForsTreeSignature = (2 ^ (8 * n)) ^ (1 + forsHeight) := by
    rw [Fintype.card_congr forsFields]
    simp only [Fintype.card_prod, Fintype.card_fun, Fintype.card_fin,
      Digest, Fintype.card_bitVec, pow_add, pow_one]
  rw [Fintype.card_congr signatureFields]
  simp only [ForsSignature, HypertreeSignature, Fintype.card_prod, Fintype.card_fun,
    Fintype.card_fin, hxmss, hfors, Digest, Fintype.card_bitVec, ← pow_mul, ← pow_add]
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
  apply (Fintype.bijective_iff_injective_and_card _).2
  refine ⟨encodeFixed_injective, ?_⟩
  rw [card, Fintype.card_congr (Equiv.vectorEquivFin UInt8 signatureBytes)]
  rw [Fintype.card_fun, Fintype.card_fin,
    ← FinEnum.card_eq_fintypeCard (α := UInt8), FinEnum.card_UInt8, pow_mul]

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

end SlhDsaSecurity
