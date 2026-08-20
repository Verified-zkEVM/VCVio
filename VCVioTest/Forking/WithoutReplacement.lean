/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import VCVio.OracleComp.Constructions.WithoutReplacement

/-!
# Regression checks for drawing without replacement

`ProbComp.expectedLength_drawUntil` equates a sampling loop with the arithmetic recursion
`NegHypergeom.expectedDraws`, so a green build establishes the two agree but not that either says
anything. The checks below pin down concrete values on both sides, and pin down the boundary that
motivates the whole generalization.

**Exhaustion is real.** `NegHypergeom.expectedDraws_eq` needs `r ≤ G`; below that the loop cannot
collect `r` successes and instead drains the pool, and the closed form is then strictly wrong
(`expectedDraws_ne_closedForm_of_exhaustion`). `NegHypergeom.expectedDraws_le` survives, which is
why the coordinate-wise extractor can use one bound for both cases.
-/

@[expose] public section

open ProbComp NegHypergeom OracleComp.EvalDist

open scoped ENNReal

namespace VCVioTest.Forking

/-! ## The loop agrees with the arithmetic -/

/-- A three-element pool of which exactly one value accepts. -/
def pool3 : List (Fin 3) := [0, 1, 2]

def acceptZero : Fin 3 → Bool := fun x => x == 0

example : pool3.length = 3 := by decide

example : pool3.countP acceptZero = 1 := by decide

/-- Collecting the single accepting value takes `1 * 4 / 2 = 2` draws on average. -/
theorem expectedDraws_pool3 : expectedDraws 3 1 1 = 2 := by
  rw [expectedDraws_eq (by norm_num) (by norm_num)]
  norm_num
  rw [show (4 : ℝ≥0∞) = 2 * 2 from by norm_num,
    ENNReal.mul_div_cancel_right (by norm_num) (by finiteness)]

theorem expectedValue_length_drawUntil_pool3 :
    expectedValue (drawUntil acceptZero 1 pool3) (fun d => (d.length : ℝ≥0∞)) = 2 := by
  rw [expectedValue_length_drawUntil acceptZero pool3.length 1 pool3 rfl,
    show pool3.length = 3 from rfl, show pool3.countP acceptZero = 1 from rfl,
    expectedDraws_pool3]

/-! ## The loop as a truncated ordering -/

/-- The reformulation instantiates: the loop's law is `takeUntil` applied to a random ordering. -/
example : evalDist (drawUntil acceptZero 1 pool3)
    = evalDist (takeUntil acceptZero 1 <$> drawAll pool3) :=
  evalDist_drawUntil_eq_map_drawAll acceptZero pool3.length 1 pool3 rfl

/-- A four-element alphabet with two accepting values, to exercise the budget. -/
def acceptLow : Fin 4 → Bool := fun x => x == 0 || x == 1

/-- `takeUntil` keeps the `r`-th accepting element and stops there. -/
example : takeUntil acceptLow 2 [2, 0, 3, 1, 2] = [2, 0, 3, 1] := rfl

/-- A single accepting value ends it immediately. -/
example : takeUntil acceptLow 1 [2, 0, 3, 1] = [2, 0] := rfl

/-- The budget counts accepting elements, not draws: with no accepting element in reach it keeps
the whole ordering rather than stopping at `r` draws. -/
example : takeUntil acceptLow 1 [2, 3, 2, 3] = [2, 3, 2, 3] := rfl

/-- A zero budget keeps nothing, which is why the reformulation is a distributional identity and
not a program identity: `drawUntil` at `r = 0` samples nothing, while the right-hand side still
draws a whole ordering and discards it. -/
example : takeUntil acceptLow 0 [2, 0, 3, 1] = [] := rfl

/-- Drawing the whole pool is the loop that never spends its budget. -/
example : drawAll pool3 = drawUntil (fun _ => false) 1 pool3 := rfl

/-! ## Exhaustion -/

/-- The exhausting experiment stops after draining its one-element pool. -/
theorem expectedDraws_one_one_two : expectedDraws 1 1 2 = 1 := by
  show expectedDraws (0 + 1) 1 (1 + 1) = 1
  rw [expectedDraws_succ]
  simp

/-- Wanting two successes from a pool holding one: the loop drains the pool after a single draw. -/
theorem expectedValue_length_drawUntil_exhausted :
    expectedValue (drawUntil acceptZero 2 [(0 : Fin 3)]) (fun d => (d.length : ℝ≥0∞)) = 1 := by
  rw [expectedValue_length_drawUntil acceptZero [(0 : Fin 3)].length 2 _ rfl,
    show [(0 : Fin 3)].length = 1 from rfl,
    show [(0 : Fin 3)].countP acceptZero = 1 from rfl, expectedDraws_one_one_two]

/-- **The boundary that forces the inequality.** At `G < r` the closed form of
`expectedDraws_eq` is not merely unproved, it is false: the experiment cannot collect two
successes from a pool with one, so it stops at one draw while the formula reads `2`. -/
theorem expectedDraws_ne_closedForm_of_exhaustion :
    expectedDraws 1 1 2 ≠ ((2 : ℕ) : ℝ≥0∞) * (((1 : ℕ) : ℝ≥0∞) + 1) / (((1 : ℕ) : ℝ≥0∞) + 1) := by
  rw [expectedDraws_one_one_two]
  norm_num
  rw [show (4 : ℝ≥0∞) = 2 * 2 from by norm_num,
    ENNReal.mul_div_cancel_right (by norm_num) (by finiteness)]
  norm_num

/-- The general bound still holds there, with slack. -/
theorem expectedValue_length_drawUntil_exhausted_le :
    expectedValue (drawUntil acceptZero 2 [(0 : Fin 3)]) (fun d => (d.length : ℝ≥0∞)) ≤ 2 := by
  rw [expectedValue_length_drawUntil_exhausted]
  norm_num

/-! ## Degenerate cases -/

/-- Wanting nothing draws nothing. -/
example (l : List (Fin 3)) :
    expectedValue (drawUntil acceptZero 0 l) (fun d => (d.length : ℝ≥0∞)) = 0 := by simp

/-- An empty pool draws nothing. -/
example (r : ℕ) :
    expectedValue (drawUntil acceptZero r []) (fun d => (d.length : ℝ≥0∞)) = 0 := by simp

end VCVioTest.Forking
