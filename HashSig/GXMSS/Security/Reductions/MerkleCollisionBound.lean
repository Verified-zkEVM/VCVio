/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import HashSig.GXMSS.Completeness
import all HashSig.GXMSS.Completeness
public import HashSig.GXMSS.Security.Auxiliary.Encoding
import all HashSig.GXMSS.Security.Auxiliary.Encoding
public import HashSig.GXMSS.Security.Auxiliary.MerkleWitnesses
import all HashSig.GXMSS.Security.Auxiliary.MerkleWitnesses
public import HashSig.GXMSS.Security.Auxiliary.SigningQueries
import all HashSig.GXMSS.Security.Auxiliary.SigningQueries
public import HashSig.GXMSS.Security.Reductions.ReductionExperiments
import all HashSig.GXMSS.Security.Reductions.ReductionExperiments
public import HashSig.GXMSS.Security.Reductions.TargetRegistrationSimulation
import all HashSig.GXMSS.Security.Reductions.TargetRegistrationSimulation
public import VCVio.CryptoFoundations.HardnessAssumptions.TweakableHash.SMDTPRE
public import VCVio.CryptoFoundations.HardnessAssumptions.TweakableHash.SMDTTCR
public import VCVio.CryptoFoundations.HardnessAssumptions.TweakableHash.SMDTUD
public import VCVio.CryptoFoundations.SyncSignatureAlg
import all VCVio.CryptoFoundations.SyncSignatureAlg

/-!
# Merkle target-collision bound statement

The complete-tree first Merkle collision hop retains its exact query and sampling premises.
-/

public section

namespace GXMSS.Unforgeability

open Encoding ENNReal OracleComp OracleSpec TweakableHash

noncomputable section

variable {PP T X H M R : Type} {h w v : ℕ}

/-- The exact Game 0-to-Game 1 Merkle target-collision inequality.  The left side is the adopted
post-runtime strong-unforgeability winning mass, `gameOneAdvantage` observes the actual Game 1
program after the same partial runtime evaluation, and the other summand is the authoritative
SM-DT-TCR experiment for the executable reduction.  This proposition introduces no conditioning
or support-only surrogate. -/
@[expose]
def FirstMerkleTargetCollisionBound
    [SampleableType H] [SampleableType R]
    [DecidableEq T] [DecidableEq X] [DecidableEq H] [DecidableEq M]
    [DecidableEq (GXMSS.Signature R H h v)]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w)) (K : ℕ)
    (hv : 0 < v)
    (advGXMSS : SyncSignatureUnforgeability.Adversary unifSpec (GXMSS.PublicKey PP H)
      (Fin (2 ^ h)) M (GXMSS.Signature R H h v)) : Prop :=
  SyncSignatureUnforgeability.strongAdvantage (GXMSS.scheme hash enc K)
      ProbCompRuntime.probComp advGXMSS ≤
    SM_DT_TCR_Advantage
        (GXMSS.Reductions.merkleTargetCollisionReduction hash enc K hv advGXMSS) +
      GXMSS.Reductions.gameOneAdvantage hash enc K advGXMSS

end

end GXMSS.Unforgeability
