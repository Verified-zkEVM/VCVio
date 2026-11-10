/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import HashSig.GXMSS.Security.PRFDerivedUnforgeability

/-! # PRF-derived complete GXMSS public endpoint application

An ordinary consumer applies the complete three-law PRF security endpoint.
-/

public section

open GXMSS GXMSS.Encoding GXMSS.IntervalMerkle
open OracleComp OracleSpec TweakableHash SyncSignatureUnforgeability ENNReal

variable {Key PP T X H M R Response : Type} {h w v : ℕ}
section

open GXMSS.PRFDerived.Unforgeability

example
    [SampleableType H] [SampleableType R]
    [DecidableEq T] [DecidableEq X] [DecidableEq H] [DecidableEq M]
    [DecidableEq R] [DecidableEq (Signature R H h v)]
    [DecidableEq (GXMSS.PRFDerived.Query PP M h v)] [SampleableType Response]
    (hash : HashInstance PP T X H h w v) (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w))
    (prf : PRFScheme Key (GXMSS.PRFDerived.Query PP M h v) Response)
    (projection : GXMSS.PRFDerived.Interpretation PP H R Response) (budget qs : ℕ)
    (hv : 0 < v) (hw : 0 < w) (htwo : ∃ x y : Codeword v (2 ^ w),
      x ∈ enc.code ∧ y ∈ enc.code ∧ x ≠ y) (adv : SyncSignatureUnforgeability.Adversary unifSpec
      (PublicKey PP H) (Fin (2 ^ h)) M (Signature R H h v))
    (hbound : GXMSS.Unforgeability.SigningQueryBound qs adv)
    (hseed : PublicSeedSamplingLaw hash projection) (hstart : ChainStartSamplingLaw projection)
    (hretry : RetrySamplingLaw projection) :
    SyncSignatureUnforgeability.strongAdvantage
      (GXMSS.PRFDerived.scheme prf.keygen hash enc prf.eval projection budget)
      ProbCompRuntime.probComp adv ≤
    prf.prfAdvantage (randgenPRFReduction hash enc projection budget adv) +
      (SM_DT_TCR_Advantage
        (GXMSS.Reductions.merkleTargetCollisionReduction hash enc budget hv adv) +
      Encoding.TargetCollisionResistance.advantage
        (GXMSS.Reductions.encodingTargetCollisionReduction hash enc qs budget adv) +
      SM_DT_TCR_Advantage
        (GXMSS.Reductions.firstChainTargetCollisionReduction hash enc budget adv) +
      SM_DT_TCR_Advantage
        (GXMSS.Reductions.secondChainTargetCollisionReduction hash enc budget adv) +
      (↑((2 ^ h) * v * (2 ^ w)) : ℝ≥0∞) *
        ((↑(2 ^ w) : ℝ≥0∞) * SM_DT_UD_Advantage
          (GXMSS.Reductions.jointUndetectabilityReduction
            hash enc budget hv hw adv) +
          SM_DT_PRE_Advantage
            (GXMSS.Reductions.jointPreimageReduction hash enc budget hv hw adv))) :=
  GXMSS.PRFDerived.Unforgeability.strong_unforgeability_reduction_bound hash enc prf projection
    budget qs hv hw htwo adv hbound hseed hstart hretry

end
