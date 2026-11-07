/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import HashSig.GXMSS.Security.Interval.Reductions.MerkleCollision
public import HashSig.GXMSS.Security.Interval.Reductions.MerkleGames
public import HashSig.GXMSS.Security.Interval.Reductions.FullRange
import all HashSig.GXMSS.Security.Interval.Reductions.MerkleGames

/-!
# Pruned Merkle setup and reduction consumers

Typed checks cover the actual accepted setup equations, frontier counts, checked inactive
witness provenance, the native obstruction inequality and the entire full-range primitive
experiment.

Private imports supply the actual implementation kernels used by these controls. Ordinary public
endpoint applications live in `DirectEndpointApplications`.
-/

public section

open GXMSS GXMSS.IntervalMerkle GXMSS.Interval.Unforgeability

#check @merkleTargetCollisionAdversary
#check @merkleTargetCollisionExperiment_full
#check @merkleTargetCollisionAdvantage_full
#check @MerkleObstructionBound

#check (by decide : prunedCount (Interval.full 0) 0 0 = 1)
#check (by decide : prunedCount (Interval.full 3) 3 0 = 15)
#check (by decide : prunedCount (⟨3, 4, of_decide_eq_true rfl⟩ : Interval 3) 3 0 = 7)
#check (by decide : prunedCount (⟨3, 3, of_decide_eq_true rfl⟩ : Interval 3) 3 0 = 4)
#check (by decide : prunedCount (⟨3, 4, of_decide_eq_true rfl⟩ : Interval 3) 1 0 = 0)


#check @GXMSS.Interval.Filler.targetCapacity_sum_eq_frontier_card
#print axioms GXMSS.Interval.Filler.targetCapacity_sum_eq_frontier_card

#check @merkleObstructionMass_le_advantage
#print axioms merkleObstructionMass_le_advantage
