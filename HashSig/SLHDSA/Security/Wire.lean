/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module

public import HashSig.SLHDSA.Security.ByteBound
public import HashSig.SLHDSA.Concrete.Codec
public import HashSig.SLHDSA.External
public import VCVio.CryptoFoundations.SignatureAlg.Wire

/-!
# Strong unforgeability of the pure SLH-DSA wire interface

The public key and signature are arbitrary byte lists, parsed with the strict FIPS codecs.
The context is fixed by the scheme and checked before its one-byte length is encoded.
The named reduction preserves both ROM budgets and strong returned-pair freshness.
Prehashing requires a separate collision term and is not part of this pure-mode interface.
-/

public section

open OracleComp OracleSpec SignatureAlg
open scoped ENNReal

namespace SLHDSA

/-- An exact-width SLH-DSA codec as a canonical parser for the generic wire-game adapter. -/
@[expose] def WireCodec.canonicalEncoding {α : Type} {width : ℕ} (codec : WireCodec α width) :
    CanonicalEncoding α (List Byte) where
  encode := codec.encode
  decode raw := (codec.decode raw).toOption
  decode_eq_some_iff raw value := by
    rw [← codec.decode_eq_ok_iff raw value]
    cases codec.decode raw <;> simp [Except.toOption]
  fallback := codec.equiv.symm (Vector.replicate width 0)

namespace Security

/-- A FIPS pure-mode context, fixed for all signing queries and the final forgery. -/
structure PureContext where
  /-- The context bytes fixed for the whole signing game. -/
  bytes : List Byte
  /-- The external context length fits in its one-byte encoding. -/
  length_le : bytes.length ≤ 255

/-- Algorithm 22's pure-mode input to the internal scheme. -/
@[expose] def PureContext.encode (ctx : PureContext) (msg : List Byte) : List Byte :=
  [0, UInt8.ofNat ctx.bytes.length] ++ ctx.bytes ++ msg

/-- Pure-mode message encoding is injective at a fixed context. -/
theorem PureContext.encode_injective (ctx : PureContext) : Function.Injective ctx.encode := by
  intro a b h
  simpa only [PureContext.encode, List.append_assoc, List.append_cancel_left_eq] using h

/-- The security interface uses exactly the external pure-mode message encoding. -/
theorem PureContext.encode_eq_external (ctx : PureContext) (msg : List Byte) :
    External.encodePureMessage ctx.bytes msg = .ok (ctx.encode msg) :=
  External.encodePureMessage_eq_ok ctx.bytes msg ctx.length_le

variable (vp : ValidatedParams)

/-- Pure SLH-DSA over the single SHAKE oracle, exposing byte-list keys and signatures.
Malformed signatures and public keys are rejected before internal verification. -/
@[expose] noncomputable def wireShakeScheme (ctx : PureContext)
    (optRand : PublicKeyCore (shakeCore vp) → ProbComp (shakeCore vp).Y)
    (pkSeedDist : ProbComp (shakeCore vp).PkSeed) :=
  SignatureAlg.Wire.scheme (shakeRomScheme vp optRand pkSeedDist) ctx.encode
    (publicKeyCodec (Concrete.shakeWireCodec vp.params)).canonicalEncoding
    (signatureCodec vp (Concrete.shakeWireCodec vp.params)).canonicalEncoding

/-- The named adversary transformation from pure wire forgeries to structured forgeries. -/
@[expose] noncomputable def wireReduce (ctx : PureContext)
    {optRand : PublicKeyCore (shakeCore vp) → ProbComp (shakeCore vp).Y}
    {pkSeedDist : ProbComp (shakeCore vp).PkSeed}
    (adv : StrongUnforgeableAdversary (wireShakeScheme vp ctx optRand pkSeedDist)) :=
  SignatureAlg.Wire.reduce (shakeRomScheme vp optRand pkSeedDist) ctx.encode
    (publicKeyCodec (Concrete.shakeWireCodec vp.params)).canonicalEncoding
    (signatureCodec vp (Concrete.shakeWireCodec vp.params)).canonicalEncoding adv

/-- Answering the wire scheme's hash oracle by concrete SHAKE gives the strict wire wrapper
of FIPS internal algorithms at exactly the external pure-mode message encoding. -/
theorem wireShakeScheme_map_shakeAnswer (hnm : vp.params.n ≤ vp.params.m) (ctx : PureContext)
    (optRand : PublicKeyCore (shakeCore vp) → ProbComp (shakeCore vp).Y)
    (pkSeedDist : ProbComp (shakeCore vp).PkSeed) :
    (wireShakeScheme vp ctx optRand pkSeedDist).map
        (simulateQ' (unifFwdAnswerImpl (shakeAnswer vp))) =
      SignatureAlg.Wire.scheme
        (internalAlg vp (Concrete.shakePrimitives vp.params) optRand pkSeedDist) ctx.encode
        (publicKeyCodec (Concrete.shakeWireCodec vp.params)).canonicalEncoding
        (signatureCodec vp (Concrete.shakeWireCodec vp.params)).canonicalEncoding := by
  unfold wireShakeScheme
  rw [SignatureAlg.Wire.map_scheme, shakeRomScheme_map_shakeAnswer_of_le hnm]

/-- The pure wire reduction preserves the adversary's own hash and signing budgets. -/
theorem romQueryBound_wireReduce (ctx : PureContext)
    {optRand : PublicKeyCore (shakeCore vp) → ProbComp (shakeCore vp).Y}
    {pkSeedDist : ProbComp (shakeCore vp).PkSeed}
    (adv : StrongUnforgeableAdversary (wireShakeScheme vp ctx optRand pkSeedDist))
    {qh qs : ℕ} (hadv : adv.RomQueryBound qh qs) :
    (wireReduce vp ctx adv).RomQueryBound qh qs :=
  SignatureAlg.Wire.romQueryBound_reduce _ _ _ _ _ hadv

/-- An accepted fresh pure wire pair is bounded by the structured strong forgery game. -/
theorem wireStrongAdvantage_le (ctx : PureContext)
    {optRand : PublicKeyCore (shakeCore vp) → ProbComp (shakeCore vp).Y}
    {pkSeedDist : ProbComp (shakeCore vp).PkSeed}
    (adv : StrongUnforgeableAdversary (wireShakeScheme vp ctx optRand pkSeedDist)) :
    strongUnforgeableAdvantage (shakeRuntime vp) adv ≤
      shakeStrongAdvantage vp (wireReduce vp ctx adv) := by
  rw [shakeStrongAdvantage_def]
  exact SignatureAlg.Wire.strongUnforgeableAdvantage_le _ _ ctx.encode_injective _ _ _

/-- The single-SHAKE bound holds at the public pure wire interface with uniform public seed.
The only adversarial hypothesis is its unchanged query budget. -/
theorem wireStrongAdvantage_le_securityBound_validatedParams (set : FipsParameterSet)
    (ctx : PureContext)
    {optRand : PublicKeyCore (shakeCore set.validatedParams) →
      ProbComp (shakeCore set.validatedParams).Y}
    (adv : StrongUnforgeableAdversary (wireShakeScheme set.validatedParams ctx optRand
      ($ᵗ (shakeCore set.validatedParams).PkSeed)))
    {qh qs : ℕ} (hadv : adv.RomQueryBound qh qs) :
    strongUnforgeableAdvantage (shakeRuntime set.validatedParams) adv ≤
      byteBound set.validatedParams qh qs + honestAdrsCount set.validatedParams / 2 ^ 256 *
        weakSeedFactor set.validatedParams (everySeedBound set.validatedParams qh qs) :=
  (wireStrongAdvantage_le _ ctx adv).trans
    (shakeStrongAdvantage_le_securityBound_validatedParams set _
      (romQueryBound_wireReduce _ ctx adv hadv))

/-- Hedged signing retains its sharper bound at the pure wire interface. -/
theorem wireStrongAdvantage_le_securityBound_hedged_validatedParams (set : FipsParameterSet)
    (ctx : PureContext)
    (adv : StrongUnforgeableAdversary (wireShakeScheme set.validatedParams ctx
      (fun _ => $ᵗ (shakeCore set.validatedParams).Y)
      ($ᵗ (shakeCore set.validatedParams).PkSeed)))
    {qh qs : ℕ} (hadv : adv.RomQueryBound qh qs) :
    strongUnforgeableAdvantage (shakeRuntime set.validatedParams) adv ≤
      byteBoundHedged set.validatedParams qh qs + honestAdrsCount set.validatedParams / 2 ^ 256 *
        weakSeedFactor set.validatedParams (everySeedBoundHedged set.validatedParams qh qs) :=
  (wireStrongAdvantage_le _ ctx adv).trans
    (shakeStrongAdvantage_le_securityBound_hedged_validatedParams set _
      (romQueryBound_wireReduce _ ctx adv hadv))

end Security
end SLHDSA
