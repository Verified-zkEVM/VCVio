/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import HashSig.GXMSS.Interval.Filler.Basic
public import HashSig.GXMSS.Interval.FrontierCount

/-!
# Filler target capacity

The two fixed target families partition the frontier and have at most one target per inactive
epoch, with the inclusive interval length retained exactly.
-/

public section

namespace GXMSS.Interval.Filler

open GXMSS.IntervalMerkle

variable {h : ℕ}

/-- The two fixed filler families together have at most one target per inactive epoch. -/
theorem targetCapacity_sum_le_inactive_leaf_count (I : Interval h) :
    targetCapacity .endpointVector I + targetCapacity .childPair I ≤ 2 ^ h - I.length := by
  rw [targetCapacity_sum_eq_frontier_card]
  exact GXMSS.IntervalMerkle.frontier_card_le_inactive I

end GXMSS.Interval.Filler
