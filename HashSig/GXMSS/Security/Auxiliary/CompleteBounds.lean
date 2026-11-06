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
public import HashSig.GXMSS.Security.Reductions.Experiments
import all HashSig.GXMSS.Security.Reductions.Experiments
public import HashSig.GXMSS.Security.Reductions.TCRSimulation
import all HashSig.GXMSS.Security.Reductions.TCRSimulation
public import Lean.Elab.Command
public import Lean.Util.CollectAxioms
public import VCVio.CryptoFoundations.HardnessAssumptions.TweakableHash.SMDTPRE
public import VCVio.CryptoFoundations.HardnessAssumptions.TweakableHash.SMDTTCR
public import VCVio.CryptoFoundations.HardnessAssumptions.TweakableHash.SMDTUD
public import VCVio.CryptoFoundations.SyncSignatureAlg
import all VCVio.CryptoFoundations.SyncSignatureAlg

/-!
# Complete-tree reduction statements

Named reduction interfaces state the complete-tree strong-unforgeability bound and its first
Merkle collision hop, retaining their exact query and sampling premises.
-/

public section

namespace GXMSS.Unforgeability

open Encoding ENNReal OracleComp OracleSpec TweakableHash

noncomputable section

variable {PP T X H M R : Type} {h w v : ℕ}

/-- The concrete separate-term reduction inequality underlying Theorem 1. The parameter `qs`
controls the encoding target-collision transcript, and `K` controls its retry law. The source
adversary has the explicit pathwise signing-query bound; the authoritative adversary types preserve
their own sampling, seed-reveal and oracle disciplines. This proposition does not claim
reduction-query or running-time bounds. -/
@[expose]
def StrongUnforgeabilityReductionBound
    [SampleableType H] [SampleableType R]
    [DecidableEq T] [DecidableEq X] [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w)) (K qs : ℕ)
    (advGXMSS : SyncSignatureUnforgeability.Adversary unifSpec (GXMSS.PublicKey PP H)
      (Fin (2 ^ h)) M (GXMSS.Signature R H h v))
    (advMerkleTCR : SM_DT_TCR_Adversary
      (SM_DT_TCR_Problem.standalone hash.thf (2 * (2 ^ h) * v * (2 ^ w))))
    (advEncodingTCR : Encoding.TargetCollisionResistance.Adversary
  (Encoding.TargetCollisionResistance.Problem.mk enc
    (HashInstance.thf hash).seedGen ($ᵗ R) qs K))
    (advFirstChainTCR : SM_DT_TCR_Adversary
      (SM_DT_TCR_Problem.standalone hash.thf ((2 ^ h) * v * (2 ^ w))))
    (advSecondChainTCR : SM_DT_TCR_Adversary
      (SM_DT_TCR_Problem.standalone hash.thf ((2 ^ h) * v * (2 ^ w))))
    (advUD : SM_DT_UD_Adversary
  (SM_DT_UD_Problem.standalone (HashInstance.thf hash) (HashInstance.digestInput hash)
    (HashInstance.digestInput hash).injective
        ($ᵗ H) ($ᵗ H) 1))
    (advPRE : SM_DT_PRE_Adversary
  (SM_DT_PRE_Problem.standalone (HashInstance.thf hash) (HashInstance.digestInput hash)
    (HashInstance.digestInput hash).injective 1)) :
    Prop :=
  SigningQueryBound qs advGXMSS →
  SyncSignatureUnforgeability.strongAdvantage (GXMSS.scheme hash enc K)
      ProbCompRuntime.probComp advGXMSS ≤
    SM_DT_TCR_Advantage advMerkleTCR +
      Encoding.TargetCollisionResistance.advantage advEncodingTCR +
      SM_DT_TCR_Advantage advFirstChainTCR + SM_DT_TCR_Advantage advSecondChainTCR +
      (↑((2 ^ h) * v * (2 ^ w)) : ℝ≥0∞) *
        ((↑(2 ^ w) : ℝ≥0∞) * SM_DT_UD_Advantage advUD +
          SM_DT_PRE_Advantage advPRE)

end

end GXMSS.Unforgeability

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
