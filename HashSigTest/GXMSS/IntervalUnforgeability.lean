/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import HashSig.GXMSS.Security.Interval.Unforgeability

/-!
# Native interval security composition controls

The final and weakened bounds name their actual reductions. Concrete controls distinguish
sharp positive-position factors from the power-of-two coefficients.
-/

public section

open GXMSS GXMSS.IntervalMerkle GXMSS.Interval.Unforgeability

noncomputable example := @strongUnforgeabilityBound
noncomputable example := @powerOfTwoStrongUnforgeabilityBound
example := @strong_unforgeability_reduction_bound
example := @strong_unforgeability_power_of_two_reduction_bound
example := @strongUnforgeabilityBound_le_powerOfTwoStrongUnforgeabilityBound
example := @GXMSS.Interval.Filler.targetCapacity_sum_le_inactive_leaf_count

example : GXMSS.Interval.activeChainPositionCount (Interval.full 0) 2 2 = 6 := by decide

example : (Interval.full 0).length * 2 * 2 ^ 2 = 8 ∧
    (Interval.full 0).length * 2 * (2 ^ 2) ^ 2 = 32 := by decide
