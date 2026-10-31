/-
Copyright (c) 2026 Tom Wambsgans. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Wambsgans
-/

module

public import HashSig.SLHDSA.SHAKE128s.Proof.Signature

/-!
# Finite signatures and canonical encoding

The structured signature carriers are finite through equivalences with their field tuples.
Successful decoding retains the complete canonical encoding (`Signature.toBytes_fromBytes`);
the codec consumes every byte of an accepted signature.
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

/-- Every accepted byte string is precisely the canonical encoding of its parsed signature. -/
theorem Signature.toBytes_fromBytes {input : Bytes} {signature : Signature}
    (h : fromBytes? input = some signature) : signature.toBytes = input := by
  cases decoded : decodeSignature FIPS205.params Bridge.wireCodec input with
  | error error => simp [Signature.fromBytes?, decoded, Except.toOption] at h
  | ok native =>
    have mapped : Bridge.sigOfCore native = signature := by
      simpa only [Signature.fromBytes?, decoded, Except.toOption, Option.map_eq_map,
        Option.map_some, Option.some.injEq] using h
    rw [← mapped, Bridge.toBytes_sigOfCore]
    exact ((SLHDSA.decodeSignature_eq_ok_iff FIPS205.params Bridge.wireCodec input native).mp
      decoded).symm

end SLHDSA.SHAKE128s
