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
public import HashSig.GXMSS.Security.Auxiliary.SourcePartition
import all HashSig.GXMSS.Security.Auxiliary.SourcePartition
public import HashSig.GXMSS.Security.Reductions.ReductionExperiments
import all HashSig.GXMSS.Security.Reductions.ReductionExperiments
public import HashSig.GXMSS.Security.Reductions.SameMessageChainCollision
import all HashSig.GXMSS.Security.Reductions.SameMessageChainCollision
public import HashSig.GXMSS.Security.Reductions.MerkleCollision
import all HashSig.GXMSS.Security.Reductions.MerkleCollision
public import HashSig.GXMSS.Security.Reductions.MerkleForgery
import all HashSig.GXMSS.Security.Reductions.MerkleForgery
public import HashSig.GXMSS.Security.Reductions.ChainCutCollision
import all HashSig.GXMSS.Security.Reductions.ChainCutCollision
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
# Encoding collision probability bound

The successful-record difference between complete source observations is bounded by the
named encoding target-collision advantage.
-/

public section

namespace GXMSS.Unforgeability

open Encoding ENNReal OracleComp OracleSpec TweakableHash

noncomputable section

variable {PP T X H M R : Type} {h w v : ℕ}

/-- The successful-record Game 1 to Game 2 hop using the fixed target-collision reduction.
The pathwise signing bound counts repeated and failed queries. The inequality compares returned
native mass without conditioning on termination or on successful retries. -/
@[expose]
def SuccessfulEncodingTargetCollisionBound
    [SampleableType H] [SampleableType R]
    [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w)) (qs K : ℕ)
    (adv : GXMSS.Reductions.SchemeAdversary PP H M R h v) : Prop :=
  SigningQueryBound qs adv →
    GXMSS.Reductions.gameOneAdvantage hash enc K adv ≤
      GXMSS.Reductions.gameTwoAdvantage hash enc K adv +
        Encoding.TargetCollisionResistance.advantage
          (GXMSS.Reductions.encodingTargetCollisionReduction hash enc qs K adv)

/-- Returned Game 1 wins lost at Game 2 are charged to the successful recorded encoding target
in the authoritative collision game. -/
theorem successful_encoding_target_collision_bound
    [SampleableType H] [SampleableType R]
    [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w)) (qs K : ℕ)
    (adv : GXMSS.Reductions.SchemeAdversary PP H M R h v) :
    SuccessfulEncodingTargetCollisionBound hash enc qs K adv := by
  intro hbound
  exact (GXMSS.Reductions.gameOneAdvantage_le_gameTwo_add_successfulDifference
    hash enc K adv).trans (add_le_add_right
      (GXMSS.Reductions.successfulEncodingDifferenceMass_le_encodingTargetCollisionAdvantage
        hash enc qs K adv hbound) _)

end

end GXMSS.Unforgeability
