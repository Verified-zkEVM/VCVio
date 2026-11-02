/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module
public import HashSig.SLHDSA.SigningView.Encoding
public import HashSig.SLHDSA.Security.ByteModel
public import HashSig.SLHDSA.External
public import HashSig.SLHDSA.Concrete.Codec
public import HashSig.SLHDSA.SHAKE128s.Bridge.SharedExperiment.Defs

/-!
# SHAKE pure views of the existing external request carrier

The bridge attaches the existing context/message frame to the reusable internal constructor.
Parameters, randomizers and public-seed programs remain those of the supplied SHAKE algorithm.
-/

public section

open OracleComp OracleSpec
open SLHDSA.Security

namespace SLHDSA.SHAKE128s.Bridge.SharedExperiment

/-- Use the existing external request and frame with every SHAKE parameter and sampling mode. -/
@[expose] noncomputable def pureShakeView (vp : ValidatedParams)
    (randomizer : PublicKeyCore (shakeCore vp) → ProbComp (shakeCore vp).Y)
    (seeds : ProbComp (shakeCore vp).PkSeed) :
    SignatureAlg.SigningView (OracleComp (unifSpec + shakeSpec vp)) Message
      (PublicKeyCore (shakeCore vp)) (SecretKeyCore (shakeCore vp))
      (List Byte) (Option (List Byte)) :=
  SLHDSA.SigningView.fromInternalPure vp (Concrete.shakeWireCodec vp.params)
    (shakeRomScheme vp randomizer seeds)
    (fun request => (External.encodePureMessage request.context request.message).toOption)

/-- Every sampling mode retains the complete internal key-generation program. -/
@[simp] theorem pureShakeView_keygen (vp : ValidatedParams)
    (randomizer : PublicKeyCore (shakeCore vp) → ProbComp (shakeCore vp).Y)
    (seeds : ProbComp (shakeCore vp).PkSeed) :
    (pureShakeView vp randomizer seeds).keygen = (shakeRomScheme vp randomizer seeds).keygen := rfl

end SLHDSA.SHAKE128s.Bridge.SharedExperiment
