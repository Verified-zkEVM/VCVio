/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public meta import HashSigTest.GXMSS.TrustAuditSupport
meta import all HashSig.GXMSS.Chain
meta import all HashSig.GXMSS.Completeness
meta import all HashSig.GXMSS.Encoding.Basic
meta import all HashSig.GXMSS.Encoding.Error
meta import all HashSig.GXMSS.Encoding.Incomparable
meta import all HashSig.GXMSS.Encoding.Retry
meta import all HashSig.GXMSS.Encoding.RetryIndexed
meta import all HashSig.GXMSS.Encoding.TargetSum
meta import all HashSig.GXMSS.Encoding.Winternitz
meta import all HashSig.GXMSS.HashInstance
meta import all HashSig.GXMSS.Interval.Filler
meta import all HashSig.GXMSS.Interval.FrontierCount
meta import all HashSig.GXMSS.Interval.Merkle
meta import all HashSig.GXMSS.Interval.Scheme
meta import all HashSig.GXMSS.Merkle
meta import all HashSig.GXMSS.Scheme
meta import all HashSig.GXMSS.Security.Auxiliary.ChainSelection
meta import all HashSig.GXMSS.Security.Auxiliary.ChainSourceMass
meta import all HashSig.GXMSS.Security.Auxiliary.ChainSplicing
meta import all HashSig.GXMSS.Security.Auxiliary.ChainTelescope
meta import all HashSig.GXMSS.Security.Auxiliary.ChainWitnesses
meta import all HashSig.GXMSS.Security.Reductions.MerkleCollisionBound
meta import all HashSig.GXMSS.Security.Auxiliary.Encoding
meta import all HashSig.GXMSS.Security.Interval.Auxiliary.FullRangeInteraction
meta import all HashSig.GXMSS.Security.Auxiliary.HashWitnesses
meta import all HashSig.GXMSS.Security.Interval.Auxiliary.FillerOpening
meta import all HashSig.GXMSS.Security.Interval.Auxiliary.FillerTargets
meta import all HashSig.GXMSS.Security.Interval.Auxiliary.Interaction
meta import all HashSig.GXMSS.Security.Interval.Auxiliary.MerkleWitnesses
meta import all HashSig.GXMSS.Security.Auxiliary.MerkleWitnesses
meta import all HashSig.GXMSS.Security.Auxiliary.SigningQueries
meta import all HashSig.GXMSS.Security.Auxiliary.SourceGames
meta import all HashSig.GXMSS.Security.Auxiliary.SourcePartition
meta import all HashSig.GXMSS.Security.Unforgeability
meta import all HashSig.GXMSS.Security.EncodingInstances
meta import all HashSig.GXMSS.Security.Interval.Unforgeability
meta import all HashSig.GXMSS.Security.Reductions.ChainPreimage
meta import all HashSig.GXMSS.Security.Reductions.ChainUndetectability
meta import all HashSig.GXMSS.Security.Reductions.CollisionBounds
meta import all HashSig.GXMSS.Security.Reductions.ChainHybrid
meta import all HashSig.GXMSS.Security.Reductions.EncodingCollision
meta import all HashSig.GXMSS.Security.Reductions.EncodingCollisionBound
meta import all HashSig.GXMSS.Security.Reductions.EncodingComposition
meta import all HashSig.GXMSS.Security.Reductions.EncodingTargetCollisionReduction
meta import all HashSig.GXMSS.Security.Reductions.ReductionExperiments
meta import all HashSig.GXMSS.Security.Reductions.SameMessageChainCollision
meta import all HashSig.GXMSS.Security.Interval.Reductions.FullRange
meta import all HashSig.GXMSS.Security.Interval.Reductions.ActiveSecurity
meta import all HashSig.GXMSS.Security.Interval.Reductions.ActiveSimulation
meta import all HashSig.GXMSS.Security.Interval.Reductions.ChainReductions
meta import all HashSig.GXMSS.Security.Interval.Reductions.ChainCollision
meta import all HashSig.GXMSS.Security.Interval.Reductions.ChainHybrid
meta import all HashSig.GXMSS.Security.Interval.Reductions.FillerGames
meta import all HashSig.GXMSS.Security.Interval.Reductions.MerkleCollision
meta import all HashSig.GXMSS.Security.Interval.Reductions.MerkleGames
meta import all HashSig.GXMSS.Security.Interval.Reductions.SourcePartition
meta import all HashSig.GXMSS.Security.Reductions.MerkleCollision
meta import all HashSig.GXMSS.Security.Reductions.MerkleForgery
meta import all HashSig.GXMSS.Security.Reductions.Problems
meta import all HashSig.GXMSS.Security.Reductions.ChainCutCollision
meta import all HashSig.GXMSS.Security.Reductions.TargetRegistrationSimulation
meta import all HashSig.GXMSS.Security.Reductions.TargetCollision
meta import all HashSig.GXMSS.Security.Reductions.TargetSumEncodingTargetCollision
meta import all HashSig.GXMSS.Security.Reductions.WinternitzEncodingTargetCollision
meta import all VCVio.CryptoFoundations.SyncMultiSignatureAlg
meta import all VCVio.CryptoFoundations.SyncSignatureAlg

/-! # Direct GXMSS import trust audit

The explicit inventory audits owned declaration bodies and transitive axioms, exact theorem
origins, and zero declaration ownership for import-only facades.
-/

public meta section

run_cmd Lean.Elab.Command.liftTermElabM do
  let modules := #[
    `HashSig.GXMSS.Chain,
    `HashSig.GXMSS.Completeness,
    `HashSig.GXMSS.Encoding.Basic,
    `HashSig.GXMSS.Encoding.Error,
    `HashSig.GXMSS.Encoding.Incomparable,
    `HashSig.GXMSS.Encoding.Retry,
    `HashSig.GXMSS.Encoding.RetryIndexed,
    `HashSig.GXMSS.Encoding.TargetSum,
    `HashSig.GXMSS.Encoding.Winternitz,
    `HashSig.GXMSS.HashInstance,
    `HashSig.GXMSS.Interval.Filler,
    `HashSig.GXMSS.Interval.FrontierCount,
    `HashSig.GXMSS.Interval.Merkle,
    `HashSig.GXMSS.Interval.Scheme,
    `HashSig.GXMSS.Merkle,
    `HashSig.GXMSS.Scheme,
    `HashSig.GXMSS.Security.Auxiliary.ChainSelection,
    `HashSig.GXMSS.Security.Auxiliary.ChainSourceMass,
    `HashSig.GXMSS.Security.Auxiliary.ChainSplicing,
    `HashSig.GXMSS.Security.Auxiliary.ChainTelescope,
    `HashSig.GXMSS.Security.Auxiliary.ChainWitnesses,
    `HashSig.GXMSS.Security.Reductions.MerkleCollisionBound,
    `HashSig.GXMSS.Security.Auxiliary.Encoding,
    `HashSig.GXMSS.Security.Interval.Auxiliary.FullRangeInteraction,
    `HashSig.GXMSS.Security.Auxiliary.HashWitnesses,
    `HashSig.GXMSS.Security.Interval.Auxiliary.FillerOpening,
    `HashSig.GXMSS.Security.Interval.Auxiliary.FillerTargets,
    `HashSig.GXMSS.Security.Interval.Auxiliary.Interaction,
    `HashSig.GXMSS.Security.Interval.Auxiliary.MerkleWitnesses,
    `HashSig.GXMSS.Security.Auxiliary.MerkleWitnesses,
    `HashSig.GXMSS.Security.Auxiliary.SigningQueries,
    `HashSig.GXMSS.Security.Auxiliary.SourceGames,
    `HashSig.GXMSS.Security.Auxiliary.SourcePartition,
    `HashSig.GXMSS.Security.Unforgeability,
    `HashSig.GXMSS.Security.EncodingInstances,
    `HashSig.GXMSS.Security.Interval.Unforgeability,
    `HashSig.GXMSS.Security.Reductions.ChainPreimage,
    `HashSig.GXMSS.Security.Reductions.ChainUndetectability,
    `HashSig.GXMSS.Security.Reductions.CollisionBounds,
    `HashSig.GXMSS.Security.Reductions.ChainHybrid,
    `HashSig.GXMSS.Security.Reductions.EncodingCollision,
    `HashSig.GXMSS.Security.Reductions.EncodingCollisionBound,
    `HashSig.GXMSS.Security.Reductions.EncodingComposition,
    `HashSig.GXMSS.Security.Reductions.EncodingTargetCollisionReduction,
    `HashSig.GXMSS.Security.Reductions.ReductionExperiments,
    `HashSig.GXMSS.Security.Reductions.SameMessageChainCollision,
    `HashSig.GXMSS.Security.Interval.Reductions.FullRange,
    `HashSig.GXMSS.Security.Interval.Reductions.ActiveSecurity,
    `HashSig.GXMSS.Security.Interval.Reductions.ActiveSimulation,
    `HashSig.GXMSS.Security.Interval.Reductions.ChainReductions,
    `HashSig.GXMSS.Security.Interval.Reductions.ChainCollision,
    `HashSig.GXMSS.Security.Interval.Reductions.ChainHybrid,
    `HashSig.GXMSS.Security.Interval.Reductions.FillerGames,
    `HashSig.GXMSS.Security.Interval.Reductions.MerkleCollision,
    `HashSig.GXMSS.Security.Interval.Reductions.MerkleGames,
    `HashSig.GXMSS.Security.Interval.Reductions.SourcePartition,
    `HashSig.GXMSS.Security.Reductions.MerkleCollision,
    `HashSig.GXMSS.Security.Reductions.MerkleForgery,
    `HashSig.GXMSS.Security.Reductions.Problems,
    `HashSig.GXMSS.Security.Reductions.ChainCutCollision,
    `HashSig.GXMSS.Security.Reductions.TargetRegistrationSimulation,
    `HashSig.GXMSS.Security.Reductions.TargetCollision,
    `HashSig.GXMSS.Security.Reductions.TargetSumEncodingTargetCollision,
    `HashSig.GXMSS.Security.Reductions.WinternitzEncodingTargetCollision,
    `VCVio.CryptoFoundations.SyncMultiSignatureAlg,
    `VCVio.CryptoFoundations.SyncSignatureAlg]
  let endpoints := #[
    (`GXMSS.Unforgeability.strong_unforgeability_reduction_bound,
      `HashSig.GXMSS.Security.Unforgeability),
    (`GXMSS.Interval.Unforgeability.strongUnforgeabilityBound_full,
      `HashSig.GXMSS.Security.Interval.Reductions.FullRange),
    (`GXMSS.Interval.Unforgeability.powerOfTwoStrongUnforgeabilityBound_full,
      `HashSig.GXMSS.Security.Interval.Reductions.FullRange),
    (`GXMSS.Interval.Unforgeability.strong_unforgeability_reduction_bound,
      `HashSig.GXMSS.Security.Interval.Unforgeability),
    (`GXMSS.Reductions.jointChainGuess_probability,
      `HashSig.GXMSS.Security.Auxiliary.ChainSourceMass),
    (`GXMSS.Reductions.gameFiveGuess_probability,
      `HashSig.GXMSS.Security.Auxiliary.ChainSourceMass),
    (`GXMSS.Reductions.gameFiveAdvantage_eq_successfulGameFourMass_div_guess_card,
      `HashSig.GXMSS.Security.Auxiliary.ChainSourceMass),
    (`GXMSS.Reductions.successfulGameFourMass_eq_guess_card_mul_gameFiveAdvantage,
      `HashSig.GXMSS.Security.Auxiliary.ChainSourceMass),
    (`GXMSS.Reductions.jointChainAdvantage_eq_gameFourAdvantage_div_guess_card,
      `HashSig.GXMSS.Security.Auxiliary.ChainTelescope),
    (`GXMSS.Reductions.gameFourAdvantage_eq_guess_card_mul_jointChainAdvantage,
      `HashSig.GXMSS.Security.Auxiliary.ChainTelescope),
    (`GXMSS.Reductions.gameFourAdvantage_le_gameFive_add_unpaid_masses,
      `HashSig.GXMSS.Security.Auxiliary.ChainTelescope),
    (`GXMSS.Reductions.encoding_problem_eq,
      `HashSig.GXMSS.Security.Reductions.EncodingComposition),
    (`GXMSS.Reductions.encodingTargetCollisionAdvantage_le_hash,
      `HashSig.GXMSS.Security.Reductions.EncodingComposition)]
  let facades := #[
    `HashSig.GXMSS.Encoding.RetryIndexed,
    `HashSig.GXMSS.Security.Reductions.CollisionBounds,
    `HashSig.GXMSS.Security.Reductions.ReductionExperiments,
    `HashSig.GXMSS.Security.Interval.Reductions.ChainReductions]
  let definitions := #[
    (`GXMSS.Unforgeability.reductionBound,
      `HashSig.GXMSS.Security.Unforgeability),
    (`GXMSS.Unforgeability.StrongUnforgeabilityReductionBound,
      `HashSig.GXMSS.Security.Unforgeability),
    (`GXMSS.Unforgeability.FirstMerkleTargetCollisionBound,
      `HashSig.GXMSS.Security.Reductions.MerkleCollisionBound),
    (`GXMSS.Interval.Unforgeability.strongUnforgeabilityBound,
      `HashSig.GXMSS.Security.Interval.Unforgeability),
    (`GXMSS.Interval.Unforgeability.powerOfTwoStrongUnforgeabilityBound,
      `HashSig.GXMSS.Security.Interval.Unforgeability),
    (`GXMSS.Reductions.encodingHashTargetCollisionReduction,
      `HashSig.GXMSS.Security.Reductions.EncodingComposition)]
  GXMSS.Test.TrustAudit.check modules endpoints facades definitions
