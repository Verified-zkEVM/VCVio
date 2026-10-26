/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module
public import HashSig.SLHDSA.SHAKE128s.Statement.FIPS205
public import HashSig.SLHDSA.Security.Wire
public import HashSig.SLHDSA.GeneralSchemeQueryBound

/-!
# Fixed-context wire adversaries over the SHAKE-128s oracle

A wire adversary receives the canonical public-key bytes, forwards its private sampling and
hash queries to the shared oracle world, and attaches one valid fixed context to signing
requests and the final forgery. Signing replies are byte strings; the total translation uses
an empty fallback when the target signing interface returns `none`.
-/

public section

open OracleComp OracleSpec SignatureAlg

namespace SLHDSA.SHAKE128s.Bridge

/-- Deterministic SHAKE-128s with uniform seeds and canonical byte-list keys and signatures. -/
noncomputable abbrev wireAlgorithm (ctx : SLHDSA.Security.PureContext) :=
  SLHDSA.Security.wireShakeScheme FIPS205.params ctx FIPS205.deterministicRand
    ($ᵗ FIPS205.core.PkSeed)

/-- Forward ambient queries and attach the fixed context to each signing request. -/
@[expose] def fixedContextHandler (ctx : SLHDSA.Security.PureContext) :
    QueryImpl ((unifSpec + SLHDSA.Security.shakeSpec FIPS205.params) + (Bytes →ₒ Bytes))
      (OracleComp (Game.World FIPS205.Answer + Game.SigningSpec))
  | .inl t => liftM ((Game.World FIPS205.Answer + Game.SigningSpec).query (.inl t))
  | .inr msg => (fun answer : Option Bytes => answer.getD []) <$>
      liftM ((Game.World FIPS205.Answer + Game.SigningSpec).query
        (.inr { message := msg, context := ctx.bytes }))

/-- Ambient queries keep their indices and responses under the fixed-context translation. -/
theorem fixedContextHandler_world (ctx : SLHDSA.Security.PureContext)
    (input : (Game.World FIPS205.Answer).Domain) :
    fixedContextHandler ctx (.inl input) =
      liftM ((Game.World FIPS205.Answer + Game.SigningSpec).query (.inl input)) := rfl

/-- One wire signing request becomes one target signing request at the fixed context. -/
theorem fixedContextHandler_sign (ctx : SLHDSA.Security.PureContext) (msg : Bytes) :
    fixedContextHandler ctx (.inr msg) =
      (fun answer : Option Bytes => answer.getD []) <$>
        liftM ((Game.World FIPS205.Answer + Game.SigningSpec).query
          (.inr { message := msg, context := ctx.bytes })) := rfl

/-- The executable body of a fixed-context wire adversary at a typed public key. -/
@[expose] def fixedContextMain (ctx : SLHDSA.Security.PureContext)
    (main : Bytes → OracleComp
      ((unifSpec + SLHDSA.Security.shakeSpec FIPS205.params) + (Bytes →ₒ Bytes)) (Bytes × Bytes))
    (pk : PublicKeyCore FIPS205.core) :
    OracleComp (Game.World FIPS205.Answer + Game.SigningSpec) Game.Forgery :=
  (fun result : Bytes × Bytes =>
      Game.Forgery.mk (Message.mk result.1 ctx.bytes) result.2) <$>
    simulateQ (fixedContextHandler ctx)
      (main ((publicKeyCodec (Concrete.shakeWireCodec FIPS205.params.params)).encode pk))

/-- Adapt a byte-wire adversary to the external pure-mode SHAKE-128s game. -/
@[expose] def fixedContextAdversary (ctx : SLHDSA.Security.PureContext)
    (adv : StrongUnforgeableAdversary (wireAlgorithm ctx)) :
    Game.Adversary FIPS205.Answer (PublicKeyCore FIPS205.core) where
  main := fixedContextMain ctx adv.main

/-- The executable body is the actual transformed adversary's public-key-indexed program. -/
theorem fixedContextAdversary_main (ctx : SLHDSA.Security.PureContext)
    (adv : StrongUnforgeableAdversary (wireAlgorithm ctx)) (pk : PublicKeyCore FIPS205.core) :
    (fixedContextAdversary ctx adv).main pk = fixedContextMain ctx adv.main pk := rfl

/-- The fixed valid context frames every message exactly as FIPS 205 pure mode. -/
theorem fixedContext_frame (ctx : SLHDSA.Security.PureContext) (msg : Bytes) :
    External.encodePureMessage ctx.bytes msg = .ok (ctx.encode msg) :=
  ctx.encode_eq_external msg

/-- Signing at the fixed context canonically encodes the internal signer's result. The public
key used by this signer is the one carried by its secret key. -/
theorem fixedContext_sign (ctx : SLHDSA.Security.PureContext)
    (sk : SecretKeyCore FIPS205.core) (msg : Bytes) :
    FIPS205.scheme.sign sk { message := msg, context := ctx.bytes } =
      (fun signature => some (encodeSignature FIPS205.params
        (Concrete.shakeWireCodec FIPS205.params.params) signature)) <$>
        FIPS205.internal.sign (FIPS205.SecretKeyCore.publicKey sk) sk (ctx.encode msg) := by
  simp only [FIPS205.scheme, SLHDSA.Security.PureContext.encode_eq_external]

/-- Verification at the fixed context parses the canonical signature before internal
verification, rejecting a string that does not parse. -/
theorem fixedContext_verify (ctx : SLHDSA.Security.PureContext)
    (pk : PublicKeyCore FIPS205.core) (msg signature : Bytes) :
    FIPS205.scheme.verify pk { message := msg, context := ctx.bytes } signature =
      match decodeSignature FIPS205.params (Concrete.shakeWireCodec FIPS205.params.params)
          signature with
      | .error _ => pure false
      | .ok decoded => FIPS205.internal.verify pk (ctx.encode msg) decoded := by
  simp only [FIPS205.scheme, SLHDSA.Security.PureContext.encode_eq_external]
  rfl

/-- Conservative intrinsic verifier cap for SHAKE-128s. -/
@[expose] def verifierCap : Nat := GeneralScheme.verifyInternalQueryBound FIPS205.params.params

/-- The conservative SHAKE-128s verifier cap is 3929 oracle calls. -/
theorem verifierCap_eq : verifierCap = 3929 := by decide

end SLHDSA.SHAKE128s.Bridge
