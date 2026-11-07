/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import HashSig.GXMSS.Security.Interval.Auxiliary.FullRangeInteraction
public import HashSig.GXMSS.Security.Interval.Unforgeability
public import HashSig.GXMSS.Security.Interval.Reductions.ActiveSecurity
public import HashSig.GXMSS.Security.Interval.Reductions.ActiveSimulation
public import HashSig.GXMSS.Security.Interval.Reductions.ChainReductions
public import HashSig.GXMSS.Security.Interval.Reductions.MerkleCollision
public import HashSig.GXMSS.Security.Interval.Reductions.SourcePartition

/-!
# Ordinary consumers of the interval mathematical API

These checks use ordinary imports to consume the interval construction, whole adaptive view,
filler reductions, source partition, direct Merkle/active APIs and proved full-range equations.
Concrete fixtures and private registration machinery are outside this consumer interface.
-/

public section

open GXMSS GXMSS.IntervalMerkle GXMSS.Interval.Filler

noncomputable example := @GXMSS.Interval.scheme
noncomputable example := @GXMSS.Interval.viewFromKeys
example := @GXMSS.Interval.interaction_eq_keys_view
example := @GXMSS.Interval.interaction_measure_eq_fillers_view
example := @extractFillerOpening_sound
example := @sourceOpening_measure_eq_fillers_view
example := @sourceOpening_le_advantages
example := @GXMSS.Interval.Unforgeability.sourceStrongObservation_partition
noncomputable example := @GXMSS.Interval.Unforgeability.activeMatchingExperiment
noncomputable example := @GXMSS.Interval.Unforgeability.merkleObstructionExperiment
example := @GXMSS.Interval.Unforgeability.strongAdvantage_eq_source_partition
example := @GXMSS.Interval.Unforgeability.strongAdvantage_le_merkle_active_and_filler_advantages
example := @GXMSS.Interval.strongUnforgeableExp_full

example := (fun (f : Family) (h : ℕ) =>
  (targetCapacity_full f h : targetCapacity f (Interval.full h) = 0))

noncomputable example := @GXMSS.Interval.Unforgeability.merkleTargetCollisionAdversary
example := @GXMSS.Interval.Unforgeability.MerkleObstructionBound
noncomputable example := @GXMSS.Interval.Reductions.chainSpliceView
example := @GXMSS.Interval.Reductions.chainSpliceView_honest
noncomputable example := @GXMSS.Interval.Reductions.encodingTargetCollisionReduction


example := @GXMSS.Interval.Reductions.Chain.sameMessageRandomizerChainCollisionMass_le_advantage
example := @GXMSS.Interval.Reductions.Chain.chainCutCollisionMass_le_advantage
example := @GXMSS.Interval.Reductions.Chain.selectedPreimageMass_le_advantage

example := @GXMSS.Interval.Reductions.Chain.selectedSource_native_telescope

example := @GXMSS.Interval.Unforgeability.strong_unforgeability_reduction_bound
example :=
  @GXMSS.Interval.Unforgeability.strong_unforgeability_power_of_two_reduction_bound
