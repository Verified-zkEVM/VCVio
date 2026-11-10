/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import HashSig.GXMSS.Interval.FrontierCount

/-!
# Inactive frontier count consumers
-/

public section

open GXMSS.IntervalMerkle

example : (Interval.full 0).length = 1 := by decide

example : Fintype.card (Subtree.FrontierNode (Interval.full 0)) = 0 := by decide

example : Fintype.card (Subtree.FrontierNode
    (⟨3, 4, of_decide_eq_true rfl⟩ : Interval 3)) = 4 := by decide

example : Fintype.card (Subtree.FrontierNode
    (⟨3, 3, of_decide_eq_true rfl⟩ : Interval 3)) = 3 := by decide

/-- The inclusive height-three range [2,4] has maximal inactive roots (1,0), (0,5), (1,3). -/
example : Fintype.card (Subtree.FrontierNode
    (⟨2, 4, by decide⟩ : Interval 3)) = 3 := by decide
