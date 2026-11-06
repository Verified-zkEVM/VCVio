/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import HashSig.GXMSS.PRFDerivedScheme
import all HashSig.GXMSS.PRFDerivedScheme
public import HashSig.GXMSS.Security.Auxiliary.SigningQueries
import all HashSig.GXMSS.Security.Auxiliary.SigningQueries
public import HashSig.GXMSS.Security.PRFDerived.KeyGeneration
import all HashSig.GXMSS.Security.PRFDerived.KeyGeneration
public import HashSig.GXMSS.Security.PRFDerived.KeyMaterial
import all HashSig.GXMSS.Security.PRFDerived.KeyMaterial
public import HashSig.GXMSS.Security.PRFDerived.OracleQueries
import all HashSig.GXMSS.Security.PRFDerived.OracleQueries
public import HashSig.GXMSS.Security.PRFDerived.PRFOracleInteraction
import all HashSig.GXMSS.Security.PRFDerived.PRFOracleInteraction
public import HashSig.GXMSS.Security.PRFDerived.ResponseCache
import all HashSig.GXMSS.Security.PRFDerived.ResponseCache
public import HashSig.GXMSS.Security.PRFDerived.RetrySampling
import all HashSig.GXMSS.Security.PRFDerived.RetrySampling
public import HashSig.GXMSS.Security.PRFDerived.Signing
import all HashSig.GXMSS.Security.PRFDerived.Signing
public import HashSig.GXMSS.Security.PRFDerived.SigningCoordinates
import all HashSig.GXMSS.Security.PRFDerived.SigningCoordinates
public import HashSig.GXMSS.Security.PRFDerived.SigningSimulation
import all HashSig.GXMSS.Security.PRFDerived.SigningSimulation
public import HashSig.GXMSS.Security.CompleteUnforgeability
import all HashSig.GXMSS.Security.CompleteUnforgeability
public import VCVio.CryptoFoundations.PRF
public import VCVio.CryptoFoundations.SyncSignatureAlg
import all VCVio.CryptoFoundations.SyncSignatureAlg
public import VCVio.ProgramLogic.Relational.SimulateQ.Coupling

/-!
# PRF-derived complete-tree strong unforgeability

The independent three-projection-law additive PRF hop composes with the direct complete-tree
strong-unforgeability bound. The displayed terms retain their named reductions.
-/

public section

namespace GXMSS.PRFDerived.Unforgeability

open OracleComp OracleSpec Encoding ENNReal GXMSS ProbabilityTheory MeasureTheory TweakableHash
open OracleComp.ProgramLogic.Relational
open GXMSS.PRFDerived.ResponseCache GXMSS.PRFDerived.RetrySampling
open GXMSS.PRFDerived.SigningSimulation

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
    (hash : HashInstance PP T X H h w v) (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w))
    (prf : SharedPRF Key PP M Response h v)
    (projection : GXMSS.PRFDerived.Interpretation PP H R Response) (budget qs : ℕ)
    (hv : 0 < v) (hw : 0 < w) (htwo : ∃ x y : Codeword v (2 ^ w),
      x ∈ enc.code ∧ y ∈ enc.code ∧ x ≠ y) (adv : SyncSignatureUnforgeability.Adversary unifSpec
      (PublicKey PP H) (Fin (2 ^ h)) M (Signature R H h v))
    (hbound : GXMSS.Unforgeability.SigningQueryBound qs adv) (keyLaw : prf.UniformKey)
    (hseed : PublicSeedSamplingLaw hash projection) (hstart : ChainStartSamplingLaw projection)
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
