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
meta import all HashSig.GXMSS.Security.Auxiliary.CompleteBounds
meta import all HashSig.GXMSS.Security.Auxiliary.Encoding
meta import all HashSig.GXMSS.Security.Auxiliary.FullRangeInteraction
meta import all HashSig.GXMSS.Security.Auxiliary.HashWitnesses
meta import all HashSig.GXMSS.Security.Auxiliary.Interval.FillerOpening
meta import all HashSig.GXMSS.Security.Auxiliary.Interval.FillerTargets
meta import all HashSig.GXMSS.Security.Auxiliary.Interval.Interaction
meta import all HashSig.GXMSS.Security.Auxiliary.Interval.MerkleWitnesses
meta import all HashSig.GXMSS.Security.Auxiliary.MerkleWitnesses
meta import all HashSig.GXMSS.Security.Auxiliary.SigningQueries
meta import all HashSig.GXMSS.Security.Auxiliary.SourceGames
meta import all HashSig.GXMSS.Security.Auxiliary.SourcePartition
meta import all HashSig.GXMSS.Security.CompleteUnforgeability
meta import all HashSig.GXMSS.Security.EncodingInstances
meta import all HashSig.GXMSS.Security.IntervalUnforgeability
meta import all HashSig.GXMSS.Security.Reductions.ChainPreimage
meta import all HashSig.GXMSS.Security.Reductions.ChainUndetectability
meta import all HashSig.GXMSS.Security.Reductions.CollisionBounds
meta import all HashSig.GXMSS.Security.Reductions.CompleteChainHybrid
meta import all HashSig.GXMSS.Security.Reductions.EncodingCollision
meta import all HashSig.GXMSS.Security.Reductions.EncodingCollisionBound
meta import all HashSig.GXMSS.Security.Reductions.EncodingComposition
meta import all HashSig.GXMSS.Security.Reductions.EncodingTargetCollisionReduction
meta import all HashSig.GXMSS.Security.Reductions.Experiments
meta import all HashSig.GXMSS.Security.Reductions.FirstChainCollision
meta import all HashSig.GXMSS.Security.Reductions.FullRange.OriginalDomain
meta import all HashSig.GXMSS.Security.Reductions.Interval.ActiveSecurity
meta import all HashSig.GXMSS.Security.Reductions.Interval.ActiveSimulation
meta import all HashSig.GXMSS.Security.Reductions.Interval.Chain
meta import all HashSig.GXMSS.Security.Reductions.Interval.ChainCollision
meta import all HashSig.GXMSS.Security.Reductions.Interval.ChainHybrid
meta import all HashSig.GXMSS.Security.Reductions.Interval.FillerGames
meta import all HashSig.GXMSS.Security.Reductions.Interval.MerkleCollision
meta import all HashSig.GXMSS.Security.Reductions.Interval.MerkleGames
meta import all HashSig.GXMSS.Security.Reductions.Interval.SourcePartition
meta import all HashSig.GXMSS.Security.Reductions.MerkleCollision
meta import all HashSig.GXMSS.Security.Reductions.MerkleForgery
meta import all HashSig.GXMSS.Security.Reductions.Problems
meta import all HashSig.GXMSS.Security.Reductions.SecondChainCollision
meta import all HashSig.GXMSS.Security.Reductions.TCRSimulation
meta import all HashSig.GXMSS.Security.Reductions.TargetCollision
meta import all HashSig.GXMSS.Security.Reductions.TargetSumEncodingTargetCollision
meta import all HashSig.GXMSS.Security.Reductions.WinternitzEncodingTargetCollision
meta import all HashSig.GXMSS.Security.Unforgeability
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
    `HashSig.GXMSS.Security.Auxiliary.CompleteBounds,
    `HashSig.GXMSS.Security.Auxiliary.Encoding,
    `HashSig.GXMSS.Security.Auxiliary.FullRangeInteraction,
    `HashSig.GXMSS.Security.Auxiliary.HashWitnesses,
    `HashSig.GXMSS.Security.Auxiliary.Interval.FillerOpening,
    `HashSig.GXMSS.Security.Auxiliary.Interval.FillerTargets,
    `HashSig.GXMSS.Security.Auxiliary.Interval.Interaction,
    `HashSig.GXMSS.Security.Auxiliary.Interval.MerkleWitnesses,
    `HashSig.GXMSS.Security.Auxiliary.MerkleWitnesses,
    `HashSig.GXMSS.Security.Auxiliary.SigningQueries,
    `HashSig.GXMSS.Security.Auxiliary.SourceGames,
    `HashSig.GXMSS.Security.Auxiliary.SourcePartition,
    `HashSig.GXMSS.Security.CompleteUnforgeability,
    `HashSig.GXMSS.Security.EncodingInstances,
    `HashSig.GXMSS.Security.IntervalUnforgeability,
    `HashSig.GXMSS.Security.Reductions.ChainPreimage,
    `HashSig.GXMSS.Security.Reductions.ChainUndetectability,
    `HashSig.GXMSS.Security.Reductions.CollisionBounds,
    `HashSig.GXMSS.Security.Reductions.CompleteChainHybrid,
    `HashSig.GXMSS.Security.Reductions.EncodingCollision,
    `HashSig.GXMSS.Security.Reductions.EncodingCollisionBound,
    `HashSig.GXMSS.Security.Reductions.EncodingComposition,
    `HashSig.GXMSS.Security.Reductions.EncodingTargetCollisionReduction,
    `HashSig.GXMSS.Security.Reductions.Experiments,
    `HashSig.GXMSS.Security.Reductions.FirstChainCollision,
    `HashSig.GXMSS.Security.Reductions.FullRange.OriginalDomain,
    `HashSig.GXMSS.Security.Reductions.Interval.ActiveSecurity,
    `HashSig.GXMSS.Security.Reductions.Interval.ActiveSimulation,
    `HashSig.GXMSS.Security.Reductions.Interval.Chain,
    `HashSig.GXMSS.Security.Reductions.Interval.ChainCollision,
    `HashSig.GXMSS.Security.Reductions.Interval.ChainHybrid,
    `HashSig.GXMSS.Security.Reductions.Interval.FillerGames,
    `HashSig.GXMSS.Security.Reductions.Interval.MerkleCollision,
    `HashSig.GXMSS.Security.Reductions.Interval.MerkleGames,
    `HashSig.GXMSS.Security.Reductions.Interval.SourcePartition,
    `HashSig.GXMSS.Security.Reductions.MerkleCollision,
    `HashSig.GXMSS.Security.Reductions.MerkleForgery,
    `HashSig.GXMSS.Security.Reductions.Problems,
    `HashSig.GXMSS.Security.Reductions.SecondChainCollision,
    `HashSig.GXMSS.Security.Reductions.TCRSimulation,
    `HashSig.GXMSS.Security.Reductions.TargetCollision,
    `HashSig.GXMSS.Security.Reductions.TargetSumEncodingTargetCollision,
    `HashSig.GXMSS.Security.Reductions.WinternitzEncodingTargetCollision,
    `HashSig.GXMSS.Security.Unforgeability,
    `VCVio.CryptoFoundations.SyncMultiSignatureAlg,
    `VCVio.CryptoFoundations.SyncSignatureAlg]
  let endpoints := #[
    (`GXMSS.Unforgeability.strong_unforgeability_reduction_bound,
      `HashSig.GXMSS.Security.CompleteUnforgeability),
    (`GXMSS.Interval.Unforgeability.strongUnforgeabilityBound_full,
      `HashSig.GXMSS.Security.Reductions.FullRange.OriginalDomain),
    (`GXMSS.Interval.Unforgeability.powerOfTwoStrongUnforgeabilityBound_full,
      `HashSig.GXMSS.Security.Reductions.FullRange.OriginalDomain),
    (`GXMSS.Interval.Unforgeability.strong_unforgeability_reduction_bound_of_two_codewords,
      `HashSig.GXMSS.Security.IntervalUnforgeability),
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
    `HashSig.GXMSS.Security.Reductions.Experiments,
    `HashSig.GXMSS.Security.Reductions.Interval.Chain,
    `HashSig.GXMSS.Security.Unforgeability]
  let definitions := #[
    (`GXMSS.Reductions.encodingHashTargetCollisionReduction,
      `HashSig.GXMSS.Security.Reductions.EncodingComposition)]
  GXMSS.Test.TrustAudit.check modules endpoints facades definitions
