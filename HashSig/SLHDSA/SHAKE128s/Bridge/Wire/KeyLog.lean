/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module
public import HashSig.SLHDSA.SHAKE128s.Bridge.Wire.Defs

/-!
# Fixed-context wire keys and signing logs

Generated keys share their public seed and root. At those keys the fixed-context signer
returns precisely the wire signature inside `some`, and the signing transcript retains every
returned pair under context attachment. These identities relate returned-pair freshness and
strict verification at their shared oracle interface.
-/

public section

open OracleComp OracleSpec SignatureAlg

namespace SLHDSA.SHAKE128s.Bridge

/-- Attach the fixed context and successful-reply constructor to every wire log entry. -/
@[expose] def fixedContextLog (ctx : SLHDSA.Security.PureContext)
    (signed : QueryLog (Bytes →ₒ Bytes)) : Game.SigningLog :=
  signed.map fun entry => ⟨⟨entry.1, ctx.bytes⟩, some entry.2⟩

/-- Context attachment preserves chronological concatenation, including arbitrary prefixes. -/
theorem fixedContextLog_append (ctx : SLHDSA.Security.PureContext)
    (left right : QueryLog (Bytes →ₒ Bytes)) :
    fixedContextLog ctx (left ++ right) =
      fixedContextLog ctx left ++ fixedContextLog ctx right := by
  simp [fixedContextLog]

/-- Returned-pair freshness is unchanged by attaching one fixed context to the complete log. -/
theorem fresh_fixedContextLog_iff (ctx : SLHDSA.Security.PureContext)
    (signed : QueryLog (Bytes →ₒ Bytes)) (msg signature : Bytes) :
    Game.Fresh (fixedContextLog ctx signed) ⟨⟨msg, ctx.bytes⟩, signature⟩ ↔
      (⟨msg, signature⟩ : (_ : Bytes) × Bytes) ∉ signed := by
  constructor
  · intro fresh member
    apply fresh
    exact ⟨⟨⟨msg, ctx.bytes⟩, some signature⟩, List.mem_map.mpr ⟨_, member, rfl⟩, rfl, rfl⟩
  · intro fresh
    rintro ⟨entry, member, sameMessage, sameSignature⟩
    obtain ⟨⟨message, answer⟩, sourceMember, rfl⟩ := List.mem_map.mp member
    have sameMessage' : message = msg := congrArg Message.message sameMessage
    have sameSignature' : answer = signature := Option.some.inj sameSignature
    subst message
    subst answer
    exact fresh sourceMember

/-- Every possible internal key-generation output stores its public seed and root in both keys. -/
theorem internal_keygen_consistent (keys : PublicKeyCore FIPS205.core × SecretKeyCore FIPS205.core)
    (member : keys ∈ support FIPS205.internal.keygen) :
    keys.1 = FIPS205.SecretKeyCore.publicKey keys.2 := by
  simp only [FIPS205.internal, SLHDSA.Security.shakeRomScheme, SignatureAlg.map_keygen,
    SLHDSA.Security.romScheme, SLHDSA.Security.romKeygenAt, simulateQ_bind, simulateQ_pure,
    mem_support_bind_iff, mem_support_pure_iff] at member
  obtain ⟨_, _, _, _, _, _, _, _, rfl⟩ := member
  rfl

/-- The challenger-generated public key is the public key carried by its secret key. -/
theorem keygen_consistent (keys : SecretKeyCore FIPS205.core × PublicKeyCore FIPS205.core)
    (member : keys ∈ support FIPS205.scheme.keygen) :
    keys.2 = FIPS205.SecretKeyCore.publicKey keys.1 := by
  change keys ∈ support ((fun pair => (pair.2, pair.1)) <$> FIPS205.internal.keygen) at member
  rw [support_map] at member
  obtain ⟨pair, member, rfl⟩ := member
  exact internal_keygen_consistent pair member

/-- At consistent keys, external signing returns exactly the byte-wire signing reply in `some`. -/
theorem fixedContext_sign_eq_wire_sign (ctx : SLHDSA.Security.PureContext)
    (sk : SecretKeyCore FIPS205.core) (pk : PublicKeyCore FIPS205.core)
    (consistent : pk = FIPS205.SecretKeyCore.publicKey sk) (msg : Bytes) :
    FIPS205.scheme.sign sk ⟨msg, ctx.bytes⟩ =
      some <$> (wireAlgorithm ctx).sign
        ((publicKeyCodec (Concrete.shakeWireCodec FIPS205.params.params)).encode pk) sk msg := by
  rw [fixedContext_sign]
  subst pk
  simp [wireAlgorithm, SLHDSA.Security.wireShakeScheme, SignatureAlg.Wire.scheme,
    WireCodec.canonicalEncoding, CanonicalEncoding.read, encodeSignature, Except.toOption]

/-- A valid fixed context cannot cause the FIPS signer to return `none`. -/
theorem none_not_mem_support_fixedContext_sign (ctx : SLHDSA.Security.PureContext)
    (sk : SecretKeyCore FIPS205.core) (msg : Bytes) :
    none ∉ support (FIPS205.scheme.sign sk ⟨msg, ctx.bytes⟩) := by
  rw [fixedContext_sign]
  simp

/-- The target freshness bit equals the canonical wire returned-pair freshness bit. -/
theorem decide_fresh_fixedContextLog (ctx : SLHDSA.Security.PureContext)
    (signed : QueryLog (Bytes →ₒ Bytes)) (msg signature : Bytes) :
    decide (Game.Fresh (fixedContextLog ctx signed) ⟨⟨msg, ctx.bytes⟩, signature⟩) =
      !signingLogContains signed msg signature := by
  simp [fresh_fixedContextLog_iff, signingLogContains]

/-- At an encoded typed key, both strict wire verifiers run exactly the same program. -/
theorem fixedContext_verify_eq_wire_verify (ctx : SLHDSA.Security.PureContext)
    (pk : PublicKeyCore FIPS205.core) (msg signature : Bytes) :
    FIPS205.scheme.verify pk ⟨msg, ctx.bytes⟩ signature =
      (wireAlgorithm ctx).verify
        ((publicKeyCodec (Concrete.shakeWireCodec FIPS205.params.params)).encode pk)
        msg signature := by
  rw [fixedContext_verify]
  simp only [wireAlgorithm, SLHDSA.Security.wireShakeScheme, SignatureAlg.Wire.scheme,
    WireCodec.canonicalEncoding, WireCodec.decode_encode]
  change (match decodeSignature FIPS205.params
      (Concrete.shakeWireCodec FIPS205.params.params) signature with
    | .error _ => pure false
    | .ok decoded => FIPS205.internal.verify pk (ctx.encode msg) decoded) = _
  cases decoded : decodeSignature FIPS205.params
      (Concrete.shakeWireCodec FIPS205.params.params) signature <;>
    simp only [decodeSignature] at decoded <;> rw [decoded] <;> rfl

end SLHDSA.SHAKE128s.Bridge
