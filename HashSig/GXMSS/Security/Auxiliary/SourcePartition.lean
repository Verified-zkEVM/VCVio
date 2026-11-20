/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import HashSig.GXMSS.Completeness
import all HashSig.GXMSS.Completeness
public import HashSig.GXMSS.Security.Reductions.MerkleCollisionBound
import all HashSig.GXMSS.Security.Reductions.MerkleCollisionBound
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
public import Lean.Elab.Command
public import Lean.Util.CollectAxioms
public import VCVio.CryptoFoundations.HardnessAssumptions.TweakableHash.SMDTPRE
public import VCVio.CryptoFoundations.HardnessAssumptions.TweakableHash.SMDTTCR
public import VCVio.CryptoFoundations.HardnessAssumptions.TweakableHash.SMDTUD
public import VCVio.CryptoFoundations.SyncSignatureAlg
import all VCVio.CryptoFoundations.SyncSignatureAlg

/-!
# Source winning-mass partition

The complete-tree strong winning mass splits into matching-opening mass and a Merkle
difference observation on the same partial interaction.
-/

public section

namespace GXMSS.Unforgeability

open Encoding ENNReal OracleComp OracleSpec TweakableHash

noncomputable section

variable {PP T X H M R : Type} {h w v : ℕ}

/-- The source winning mass is bounded by the two disjoint observations on the same partial
interaction. This statement preserves the runtime's unreturned mass. -/
theorem sourceStrongWinningMass_le_gameOne_add_merkleDifference
    [SampleableType H] [SampleableType R]
    [DecidableEq H] [DecidableEq M] [DecidableEq (GXMSS.Signature R H h v)]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w)) (K : ℕ)
    (adv : GXMSS.Reductions.SchemeAdversary PP H M R h v) :
    GXMSS.Reductions.sourceStrongOutputMeasure hash enc K adv {true} ≤
      GXMSS.Reductions.gameOneAdvantage hash enc K adv +
        ProbCompRuntime.probComp.evalDist
          (GXMSS.Reductions.merkleDifferenceObservation hash enc K <$>
            GXMSS.Reductions.sourceProgram hash enc K adv) {true} := by
  simp only [GXMSS.Reductions.sourceStrongOutputMeasure,
    GXMSS.Reductions.gameOneAdvantage, GXMSS.Reductions.gameOneOutputMeasure,
    GXMSS.Reductions.gameOne, ProbCompRuntime.probComp_evalDist]
  simp only [map_eq_bind_pure_comp]
  apply OracleComp.evalDist_bind_apply_le_add_of_support
    (GXMSS.Reductions.sourceProgram hash enc K adv)
    (fun out => pure (GXMSS.Reductions.sourceStrongObservation hash enc K out))
    (fun out => pure (GXMSS.Reductions.gameOneObservation hash enc K out))
    (fun out => pure (GXMSS.Reductions.merkleDifferenceObservation hash enc K out))
    (by measurability)
  intro out _
  rw [GXMSS.Reductions.sourceStrongObservation_eq_gameOne_or_merkleDifference]
  cases GXMSS.Reductions.gameOneObservation hash enc K out <;>
    cases GXMSS.Reductions.merkleDifferenceObservation hash enc K out <;>
    simp

end

end GXMSS.Unforgeability
