/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module
public import HashSig.SLHDSA.SHAKE128s.Statement.FIPS205
public import HashSig.SLHDSA.SHAKE128s.Bridge.Wire.Defs
public import HashSig.SLHDSA.SecretProvider
public import HashSigTest.SLHDSA.ForsSecretOrder
import all HashSigTest.SLHDSA.ForsSecretOrder

/-!
# Concrete FIPS and provider-order equations

The external interface retains exact framing and strict decoding. The provider-parametric
FORS program draws each selected secret before authentication work in that tree.
-/

public section

open OracleComp OracleSpec
open SLHDSA SLHDSA.Security SLHDSA.External SLHDSA.Concrete
open SLHDSA.SHAKE128s

namespace SLHDSA.Refactor.Semantics

/-- The concrete parameter dimensions and derived oracle output length are literal. -/
theorem shake128sParametersEquation :
    (FIPS205.params.params.n, FIPS205.params.params.h, FIPS205.params.params.d,
      FIPS205.params.params.hp, FIPS205.params.params.a, FIPS205.params.params.k,
      FIPS205.params.params.m) = (16, 63, 7, 9, 12, 14, 30) := rfl

/-- The structural wire transport uses the conservative verifier cap. -/
theorem conservativeVerifierCapEquation : Bridge.verifierCap = 3929 := Bridge.verifierCap_eq

/-- The concrete single-oracle interface returns exactly thirty bytes. -/
theorem answerCarrierEquation : FIPS205.Answer = SLHDSA.Bytes 30 := rfl

/-- The concrete deterministic randomizer is the public seed. -/
theorem deterministicRandomizerEquation (pk : PublicKeyCore FIPS205.core) :
    FIPS205.deterministicRand pk = pure pk.pkSeed := rfl

/-- The concrete internal scheme uses deterministic signing and uniform public seeds. -/
theorem internalSchemeEquation :
    FIPS205.internal = shakeRomScheme FIPS205.params (fun pk => pure pk.pkSeed)
      ($ᵗ FIPS205.core.PkSeed) := rfl

/-- External key generation preserves the actual typed key pair with its declared order. -/
theorem externalKeygenEquation :
    FIPS205.scheme.keygen = (fun keys => (keys.2, keys.1)) <$> FIPS205.internal.keygen := rfl

/-- Invalid contexts return a rejection reply; valid contexts use canonical signature encoding. -/
theorem externalSigningEquation (sk : SecretKeyCore FIPS205.core) (request : Message) :
    FIPS205.scheme.sign sk request =
      match encodePureMessage request.context request.message with
      | .error _ => pure none
      | .ok message =>
        (fun signature => some (encodeSignature FIPS205.params
          (shakeWireCodec FIPS205.params.params) signature)) <$>
            FIPS205.internal.sign ⟨sk.pkSeed, sk.pkRoot⟩ sk message := rfl

/-- Invalid framing or decoding returns false before the internal verifier executes. -/
theorem externalVerificationEquation (pk : PublicKeyCore FIPS205.core)
    (request : Message) (signature : SHAKE128s.Bytes) :
    FIPS205.scheme.verify pk request signature =
      match encodePureMessage request.context request.message with
      | .error _ => pure false
      | .ok message =>
        match decodeSignature FIPS205.params (shakeWireCodec FIPS205.params.params) signature with
        | .error _ => pure false
        | .ok decoded => FIPS205.internal.verify pk message decoded := rfl

/-- Each selected secret precedes its authentication work, with trees in ascending order. -/
theorem secretFirstProgramEquation {p : Params} (core : CorePrimitives p)
    {m : Type → Type*} [Monad m]
    (hash : Adrs → core.Y → m core.Y) (nodeHash : Adrs → core.Y → core.Y → m core.Y)
    (secret : Adrs → m core.Y) (digest : List Byte) (address : Adrs) :
    forsSignWithSecret core hash nodeHash secret digest address =
      Vector.ofFnM (fun i : Fin p.k => do
        let index := i.val * 2 ^ p.a + forsIdx p digest i.val
        let selected ← secret (forsSkAdrs address index)
        let path ← PerfectMerkleTree.intrinsicAuthPathM
          (forsLeafWithSecret core hash secret address)
          (forsNodeHashWith nodeHash address) index p.a
        return ⟨selected, path⟩) := rfl

/-- Inspect the non-exposed fixture implementation at its literal chronological observations. -/
private theorem literalForsTraceProof : ForsSecretOrderTest.expectedTrace = [
    .secret ⟨2, 7, 6, 3, 0, 1⟩,
    .secret ⟨2, 7, 6, 3, 0, 0⟩, .leafHash ⟨2, 7, 3, 3, 0, 0⟩ 100,
    .secret ⟨2, 7, 6, 3, 0, 2⟩, .leafHash ⟨2, 7, 3, 3, 0, 2⟩ 102,
    .secret ⟨2, 7, 6, 3, 0, 3⟩, .leafHash ⟨2, 7, 3, 3, 0, 3⟩ 103,
    .nodeHash ⟨2, 7, 3, 3, 1, 1⟩ 1122 1133,
    .secret ⟨2, 7, 6, 3, 0, 6⟩,
    .secret ⟨2, 7, 6, 3, 0, 7⟩, .leafHash ⟨2, 7, 3, 3, 0, 7⟩ 107,
    .secret ⟨2, 7, 6, 3, 0, 4⟩, .leafHash ⟨2, 7, 3, 3, 0, 4⟩ 104,
    .secret ⟨2, 7, 6, 3, 0, 5⟩, .leafHash ⟨2, 7, 3, 3, 0, 5⟩ 105,
    .nodeHash ⟨2, 7, 3, 3, 1, 2⟩ 1144 1155] := rfl

/-- The runtime chronology contains literal provider, leaf and ordered-parent observations. -/
theorem literalForsTraceEquation : ForsSecretOrderTest.expectedTrace = [
    .secret ⟨2, 7, 6, 3, 0, 1⟩,
    .secret ⟨2, 7, 6, 3, 0, 0⟩, .leafHash ⟨2, 7, 3, 3, 0, 0⟩ 100,
    .secret ⟨2, 7, 6, 3, 0, 2⟩, .leafHash ⟨2, 7, 3, 3, 0, 2⟩ 102,
    .secret ⟨2, 7, 6, 3, 0, 3⟩, .leafHash ⟨2, 7, 3, 3, 0, 3⟩ 103,
    .nodeHash ⟨2, 7, 3, 3, 1, 1⟩ 1122 1133,
    .secret ⟨2, 7, 6, 3, 0, 6⟩,
    .secret ⟨2, 7, 6, 3, 0, 7⟩, .leafHash ⟨2, 7, 3, 3, 0, 7⟩ 107,
    .secret ⟨2, 7, 6, 3, 0, 4⟩, .leafHash ⟨2, 7, 3, 3, 0, 4⟩ 104,
    .secret ⟨2, 7, 6, 3, 0, 5⟩, .leafHash ⟨2, 7, 3, 3, 0, 5⟩ 105,
    .nodeHash ⟨2, 7, 3, 3, 1, 2⟩ 1144 1155] := literalForsTraceProof

end SLHDSA.Refactor.Semantics
