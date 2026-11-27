/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module
public import HashSig.SLHDSA.Security.Wire

/-!
# Variable valid contexts through the canonical wire reduction

A request carries a valid context and a message. Framing uses the existing FIPS pure-mode
encoding, and the existing generic wire scheme supplies all signing, parsing, verification and
freshness logic. The complete original SHAKE security bound therefore applies to adversaries
that vary the valid context from one signing query to the next.

Rejected contexts and optional signing responses are outside this interface.
-/

public section

open OracleComp OracleSpec SignatureAlg
open scoped ENNReal

namespace SLHDSA.RefactorResearch

/-- A valid context may change on every request. -/
abbrev Request := Security.PureContext × List Byte

/-- The existing pure-mode frame, applied to the context carried by the request. -/
@[expose] def frame (request : Request) : List Byte :=
  request.1.encode request.2

/-- This interface uses the existing external FIPS framing operation. -/
theorem frame_eq_external (request : Request) :
    External.encodePureMessage request.1.bytes request.2 = .ok (frame request) :=
  request.1.encode_eq_external request.2

/-- The one-byte context length makes the complete request encoding injective. -/
theorem frame_injective : Function.Injective frame := by
  rintro ⟨⟨leftContext, hleft⟩, leftMessage⟩ ⟨⟨rightContext, hright⟩, rightMessage⟩ h
  change (0 : Byte) :: UInt8.ofNat leftContext.length :: (leftContext ++ leftMessage) =
    0 :: UInt8.ofNat rightContext.length :: (rightContext ++ rightMessage) at h
  have header := List.cons.inj ((List.cons.inj h).2)
  have hlength := congrArg UInt8.toNat header.1
  have hleftLt : leftContext.length < 256 := by omega
  have hrightLt : rightContext.length < 256 := by omega
  have hlengthEq : leftContext.length = rightContext.length := by
    simpa only [UInt8.toNat_ofNat', Nat.mod_eq_of_lt hleftLt,
      Nat.mod_eq_of_lt hrightLt] using hlength
  have hcontext : leftContext = rightContext := by
    have ht := congrArg (List.take leftContext.length) header.2
    simpa [List.take_append, hlengthEq] using ht
  have hmessage : leftMessage = rightMessage := by
    simpa only [hcontext, List.append_cancel_left_eq] using header.2
  cases hcontext
  cases hmessage
  rfl

/-- The canonical scheme and canonical wire parsers with a per-request valid context. -/
@[expose] noncomputable def scheme (vp : ValidatedParams)
    (optRand : PublicKeyCore (Security.shakeCore vp) → ProbComp (Security.shakeCore vp).Y)
    (pkSeedDist : ProbComp (Security.shakeCore vp).PkSeed) :=
  SignatureAlg.Wire.scheme (Security.shakeRomScheme vp optRand pkSeedDist) frame
    (publicKeyCodec (Concrete.shakeWireCodec vp.params)).canonicalEncoding
    (signatureCodec vp (Concrete.shakeWireCodec vp.params)).canonicalEncoding

/-- Variable valid contexts retain the complete existing bound and both structural budgets. -/
theorem strongAdvantage_le (set : FipsParameterSet)
    {optRand : PublicKeyCore (Security.shakeCore set.validatedParams) →
      ProbComp (Security.shakeCore set.validatedParams).Y}
    (adv : StrongUnforgeableAdversary (scheme set.validatedParams optRand
      ($ᵗ (Security.shakeCore set.validatedParams).PkSeed)))
    {qh qs : Nat} (hadv : adv.RomQueryBound qh qs) :
    strongUnforgeableAdvantage (Security.shakeRuntime set.validatedParams) adv ≤
      Security.byteBound set.validatedParams qh qs +
        Security.honestAdrsCount set.validatedParams / 2 ^ 256 *
          Security.weakSeedFactor set.validatedParams
            (Security.everySeedBound set.validatedParams qh qs) := by
  have hwire := SignatureAlg.Wire.strongUnforgeableAdvantage_le
    (Security.shakeRomScheme set.validatedParams optRand
      ($ᵗ (Security.shakeCore set.validatedParams).PkSeed)) frame frame_injective
    (publicKeyCodec (Concrete.shakeWireCodec set.validatedParams.params)).canonicalEncoding
    (signatureCodec set.validatedParams
      (Concrete.shakeWireCodec set.validatedParams.params)).canonicalEncoding adv
  have hbound := Security.shakeStrongAdvantage_le_securityBound_validatedParams set _
    (SignatureAlg.Wire.romQueryBound_reduce _ frame _ _ adv hadv)
  rw [Security.shakeStrongAdvantage_def] at hbound
  exact hwire.trans hbound

/-- Hedged signing keeps its sharper existing byte bound under variable valid contexts. -/
theorem strongAdvantage_hedged_le (set : FipsParameterSet)
    (adv : StrongUnforgeableAdversary (scheme set.validatedParams
      (fun _ => $ᵗ (Security.shakeCore set.validatedParams).Y)
      ($ᵗ (Security.shakeCore set.validatedParams).PkSeed)))
    {qh qs : Nat} (hadv : adv.RomQueryBound qh qs) :
    strongUnforgeableAdvantage (Security.shakeRuntime set.validatedParams) adv ≤
      Security.byteBoundHedged set.validatedParams qh qs +
        Security.honestAdrsCount set.validatedParams / 2 ^ 256 *
          Security.weakSeedFactor set.validatedParams
            (Security.everySeedBoundHedged set.validatedParams qh qs) := by
  have hwire := SignatureAlg.Wire.strongUnforgeableAdvantage_le
    (Security.shakeRomScheme set.validatedParams
      (fun _ => $ᵗ (Security.shakeCore set.validatedParams).Y)
      ($ᵗ (Security.shakeCore set.validatedParams).PkSeed)) frame frame_injective
    (publicKeyCodec (Concrete.shakeWireCodec set.validatedParams.params)).canonicalEncoding
    (signatureCodec set.validatedParams
      (Concrete.shakeWireCodec set.validatedParams.params)).canonicalEncoding adv
  have hbound := Security.shakeStrongAdvantage_le_securityBound_hedged_validatedParams set _
    (SignatureAlg.Wire.romQueryBound_reduce _ frame _ _ adv hadv)
  rw [Security.shakeStrongAdvantage_def] at hbound
  exact hwire.trans hbound

/-- A SHAKE-128s consumer with a context in each adversarial signing request. -/
theorem shake128s_consumer
    {optRand : PublicKeyCore (Security.shakeCore FipsParameterSet.SLHDSA_SHAKE_128s.validatedParams) →
      ProbComp (Security.shakeCore FipsParameterSet.SLHDSA_SHAKE_128s.validatedParams).Y}
    (adv : StrongUnforgeableAdversary
      (scheme FipsParameterSet.SLHDSA_SHAKE_128s.validatedParams optRand
        ($ᵗ (Security.shakeCore FipsParameterSet.SLHDSA_SHAKE_128s.validatedParams).PkSeed)))
    {qh qs : Nat} (hadv : adv.RomQueryBound qh qs) :
    strongUnforgeableAdvantage
      (Security.shakeRuntime FipsParameterSet.SLHDSA_SHAKE_128s.validatedParams) adv ≤
      Security.byteBound FipsParameterSet.SLHDSA_SHAKE_128s.validatedParams qh qs +
        Security.honestAdrsCount FipsParameterSet.SLHDSA_SHAKE_128s.validatedParams / 2 ^ 256 *
          Security.weakSeedFactor FipsParameterSet.SLHDSA_SHAKE_128s.validatedParams
            (Security.everySeedBound FipsParameterSet.SLHDSA_SHAKE_128s.validatedParams qh qs) :=
  strongAdvantage_le .SLHDSA_SHAKE_128s adv hadv

/-- The same API and proof also serve SHAKE-192f. -/
theorem shake192f_consumer
    {optRand : PublicKeyCore (Security.shakeCore FipsParameterSet.SLHDSA_SHAKE_192f.validatedParams) →
      ProbComp (Security.shakeCore FipsParameterSet.SLHDSA_SHAKE_192f.validatedParams).Y}
    (adv : StrongUnforgeableAdversary
      (scheme FipsParameterSet.SLHDSA_SHAKE_192f.validatedParams optRand
        ($ᵗ (Security.shakeCore FipsParameterSet.SLHDSA_SHAKE_192f.validatedParams).PkSeed)))
    {qh qs : Nat} (hadv : adv.RomQueryBound qh qs) :
    strongUnforgeableAdvantage
      (Security.shakeRuntime FipsParameterSet.SLHDSA_SHAKE_192f.validatedParams) adv ≤
      Security.byteBound FipsParameterSet.SLHDSA_SHAKE_192f.validatedParams qh qs +
        Security.honestAdrsCount FipsParameterSet.SLHDSA_SHAKE_192f.validatedParams / 2 ^ 256 *
          Security.weakSeedFactor FipsParameterSet.SLHDSA_SHAKE_192f.validatedParams
            (Security.everySeedBound FipsParameterSet.SLHDSA_SHAKE_192f.validatedParams qh qs) :=
  strongAdvantage_le .SLHDSA_SHAKE_192f adv hadv

/-- A SHAKE-192f hedged consumer keeps the sharper hedged bound. -/
theorem shake192f_hedged_consumer
    (adv : StrongUnforgeableAdversary
      (scheme FipsParameterSet.SLHDSA_SHAKE_192f.validatedParams
        (fun _ => $ᵗ (Security.shakeCore FipsParameterSet.SLHDSA_SHAKE_192f.validatedParams).Y)
        ($ᵗ (Security.shakeCore FipsParameterSet.SLHDSA_SHAKE_192f.validatedParams).PkSeed)))
    {qh qs : Nat} (hadv : adv.RomQueryBound qh qs) :
    strongUnforgeableAdvantage
      (Security.shakeRuntime FipsParameterSet.SLHDSA_SHAKE_192f.validatedParams) adv ≤
      Security.byteBoundHedged FipsParameterSet.SLHDSA_SHAKE_192f.validatedParams qh qs +
        Security.honestAdrsCount FipsParameterSet.SLHDSA_SHAKE_192f.validatedParams / 2 ^ 256 *
          Security.weakSeedFactor FipsParameterSet.SLHDSA_SHAKE_192f.validatedParams
            (Security.everySeedBoundHedged FipsParameterSet.SLHDSA_SHAKE_192f.validatedParams qh qs) :=
  strongAdvantage_hedged_le .SLHDSA_SHAKE_192f adv hadv

/-- Without the context validity obligation, the one-byte length can wrap. -/
@[expose] def uncheckedFrame (context message : List Byte) : List Byte :=
  [0, UInt8.ofNat context.length] ++ context ++ message

/-- A 256-byte context collides with an empty context and a longer message. -/
theorem invalid_context_collision :
    uncheckedFrame (List.replicate 256 0) [] =
      uncheckedFrame [] (List.replicate 256 0) := by
  simp only [uncheckedFrame, List.length_replicate, List.length_nil,
    List.append_nil]
  rfl

/-- The colliding contexts are distinct. -/
theorem invalid_context_distinct : (List.replicate 256 (0 : Byte)) ≠ [] := by
  intro h
  have := congrArg List.length h
  simp only [List.length_replicate, List.length_nil] at this
  omega

#print axioms frame_injective
#print axioms strongAdvantage_le
#print axioms strongAdvantage_hedged_le
#print axioms shake128s_consumer
#print axioms shake192f_consumer
#print axioms shake192f_hedged_consumer
#print axioms invalid_context_collision

end SLHDSA.RefactorResearch
