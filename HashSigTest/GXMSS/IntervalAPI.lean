/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import HashSig.GXMSS.Security.Auxiliary.FullRangeInteraction
public import HashSig.GXMSS.Security.IntervalUnforgeability
public import HashSig.GXMSS.Security.Reductions.Interval.ActiveSecurity
public import HashSig.GXMSS.Security.Reductions.Interval.ActiveSimulation
public import HashSig.GXMSS.Security.Reductions.Interval.Chain
public import HashSig.GXMSS.Security.Reductions.Interval.MerkleCollision
public import HashSig.GXMSS.Security.Reductions.Interval.SourcePartition

/-!
# Ordinary consumers of the interval mathematical API

These checks use ordinary imports to consume the interval construction, whole adaptive view,
filler reductions, source partition, direct Merkle/active APIs and proved full-range equations.
Concrete fixtures and private registration machinery are outside this consumer interface.
-/

public section

open GXMSS GXMSS.IntervalMerkle GXMSS.Interval.Filler

#check GXMSS.Interval.scheme
#check GXMSS.Interval.viewFromKeys
#check GXMSS.Interval.interaction_eq_keys_view
#check GXMSS.Interval.interaction_measure_eq_fillers_view
#check extractFillerOpening_sound
#check sourceOpening_measure_eq_fillers_view
#check sourceOpening_le_advantages
#check GXMSS.Interval.Unforgeability.sourceStrongObservation_partition
#check GXMSS.Interval.Unforgeability.activeMatchingExperiment
#check GXMSS.Interval.Unforgeability.merkleObstructionExperiment
#check GXMSS.Interval.Unforgeability.strongAdvantage_eq_source_partition
#check GXMSS.Interval.Unforgeability.strongAdvantage_le_merkle_active_and_filler_advantages
#check GXMSS.Interval.strongUnforgeableExp_full

#check (fun (f : Family) (h : ℕ) =>
  (targetCapacity_full f h : targetCapacity f (Interval.full h) = 0))

#check GXMSS.Interval.Unforgeability.merkleTargetCollisionAdversary
#check GXMSS.Interval.Unforgeability.MerkleObstructionBound
#check GXMSS.Interval.Reductions.chainSpliceView
#check GXMSS.Interval.Reductions.chainSpliceView_honest
#check GXMSS.Interval.Reductions.encodingTargetCollisionReduction


#check @GXMSS.Interval.Reductions.Chain.sameMessageRandomizerChainCollisionMass_le_advantage
#check @GXMSS.Interval.Reductions.Chain.chainCutCollisionMass_le_advantage
#check @GXMSS.Interval.Reductions.Chain.selectedPreimageMass_le_advantage

#check @GXMSS.Interval.Reductions.Chain.selectedSource_native_telescope

#check @GXMSS.Interval.Unforgeability.strong_unforgeability_reduction_bound_of_two_codewords
#check
  @GXMSS.Interval.Unforgeability.strong_unforgeability_power_of_two_reduction_bound_of_two_codewords
