/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import HashSig.GXMSS.Security.PRFDerived.PRFOracleInteraction

/-!
# PRF-derived GXMSS strong unforgeability

The final conditional bound composes the named full-interaction PRF advantage with generic
GXMSS strong unforgeability. The imported PRF oracle interaction provides its query bound,
real and ideal correspondences, and additive PRF bound.
-/

public section

namespace GXMSS.PRFDerived.Unforgeability

open Encoding ENNReal TweakableHash

variable {Key PP T X H M R Response : Type} {h w v : ℕ}

set_option maxHeartbeats 1600000 in
-- The six concrete reduction adversaries and their target counts make the
-- composed statement expensive to elaborate under the default limit.
/-- Strong unforgeability of the shared-response PRF-derived scheme follows
from the named adaptive PRF advantage and the proved two-codeword generic
reduction. Each hardness term keeps the exact reduction adversary and target
count from the generic theorem. -/
theorem strong_unforgeability_reduction_bound
    [SampleableType Key] [SampleableType H] [SampleableType R]
    [DecidableEq T] [DecidableEq X] [DecidableEq H] [DecidableEq M]
    [DecidableEq R] [DecidableEq (Signature R H h v)]
    [DecidableEq (GXMSS.PRFDerived.Query PP M h v)] [SampleableType Response]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w))
    (prf : SharedPRF Key PP M Response h v)
    (projection : GXMSS.PRFDerived.Interpretation PP H R Response)
    (budget qs : ℕ)
    (hv : 0 < v) (hw : 0 < w)
    (htwo : ∃ x y : Codeword v (2 ^ w),
      x ∈ enc.code ∧ y ∈ enc.code ∧ x ≠ y)
    (adv : SyncSignatureUnforgeability.Adversary unifSpec
      (PublicKey PP H) (Fin (2 ^ h)) M (Signature R H h v))
    (hbound : GXMSS.Unforgeability.SigningQueryBound qs adv)
    (keyLaw : prf.UniformKey)
    (hseed : PublicSeedSamplingLaw hash projection)
    (hstart : ChainStartSamplingLaw projection)
    (hretry : RetrySamplingLaw projection) :
    SyncSignatureUnforgeability.strongAdvantage
      (GXMSS.PRFDerived.scheme hash enc prf.eval projection budget)
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
            (GXMSS.Reductions.jointPreimageReduction hash enc budget hv hw adv))) := by
  have hhop := adaptive_strong_additive_bound hash enc prf projection budget adv
    keyLaw hseed hstart hretry
  have hgeneric := (GXMSS.Unforgeability.strong_unforgeability_reduction_bound
    hash enc budget qs hv hw htwo adv) hbound
  exact hhop.trans (add_le_add_right hgeneric _)


end GXMSS.PRFDerived.Unforgeability
