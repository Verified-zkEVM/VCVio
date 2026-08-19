/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import VCVio.CryptoFoundations.CoordinateFork.SamplingGame

/-!
# Regression checks for the abstract sampling game

`expectedValue_cost_samplingGame_le` bounds the game's cost by `1 + ℓ(k-1)·P`. A green build shows
the inequality holds, not that either side is informative, so the checks below compute both at
concrete parameters.

`gatedArray` is chosen so the bound is **attained**: the array accepts on two of twenty-five
assignments, each with one further accepting value in its block's single column, so the game
examines `(23 + 2·(1 + 5/2))/25 = 6/5` entries on average, which is exactly `1 + 1·1·(1/5)`.

Two canaries guard the reading of `P`. `blockHitTotal_forkedArray` exhibits a `P` strictly above
one, so `blockHitTotal` must not be read as a probability — it is a sum over the query index, and
`blockHitTotal_le_card` is the only bound available. `columnCount_lt_blockCount_wide` exhibits a
block whose per-coordinate count is strictly below its per-query count, so the relaxation in
`columnCount_le_blockCount` genuinely loses information rather than being an equality in disguise.
-/

@[expose] public section

open OracleComp OracleComp.EvalDist CoordinateWise

open scoped ENNReal

namespace VCVioTest.Forking

/-! ## A gated array -/

/-- Two random oracle queries, one coordinate each, over a five-element challenge alphabet. -/
abbrev Slot : Type := Fin 2 × Fin 1 → Fin 5

/-- The forgery always uses query `0`, and verifies only when query `0`'s challenge is small *and*
query `1`'s challenge is zero. The second conjunct is what makes most blocks hit-free. -/
def gatedArray (j : Slot) : Bool × Fin 2 :=
  (decide (j (0, 0) < 2 ∧ j (1, 0) = 0), 0)

example : (gatedArray (fun _ => 0)).1 = true := by decide

example : (gatedArray (fun p => if p.1 = 0 then 0 else 1)).1 = false := by decide

/-- A block of query `0` holds hits exactly when query `1`'s challenge is zero. -/
theorem card_filter_blockCount_gatedArray_zero :
    (Finset.univ.filter fun j : Slot => 0 < blockCount gatedArray 0 j).card = 5 := by decide

/-- Query `1` never wins, so none of its blocks holds a hit. -/
theorem card_filter_blockCount_gatedArray_one :
    (Finset.univ.filter fun j : Slot => 0 < blockCount gatedArray 1 j).card = 0 := by decide

theorem card_slot : Fintype.card Slot = 25 := by decide

/-- One query in five of the assignments, and nothing from the other query. -/
theorem blockHitTotal_gatedArray : blockHitTotal gatedArray = 1 / 5 := by
  rw [blockHitTotal, Fin.sum_univ_two, card_filter_blockCount_gatedArray_zero,
    card_filter_blockCount_gatedArray_one, card_slot]
  push_cast
  rw [ENNReal.zero_div, add_zero,
    ENNReal.div_eq_div_iff (by norm_num) (by finiteness) (by norm_num) (by finiteness)]
  norm_num

/-- **The expected-cost half of Lemma 8.1 at concrete parameters.** The game reads the drawn
assignment and, on the two of twenty-five that accept, resamples the single column of query `0`'s
block until it finds the one further accepting value there. The bound `6/5` is exactly the average
cost, so it is tight. -/
theorem expectedValue_cost_samplingGame_gatedArray_le :
    expectedValue (samplingGame 2 gatedArray) (fun r => (r.2 : ℝ≥0∞)) ≤ 6 / 5 := by
  have h := expectedValue_cost_samplingGame_le (Q := Fin 2) (ι := Fin 1) (S := Fin 5) 2 gatedArray
  refine h.trans (le_of_eq ?_)
  rw [blockHitTotal_gatedArray, show (2 - 1 : ℕ) = 1 from rfl]
  simp only [Fintype.card_fin, Nat.cast_one, one_mul]
  rw [show (1 : ℝ≥0∞) + 1 / 5 = (5 + 1) / 5 from by
    rw [← ENNReal.div_add_div_same, ENNReal.div_self (by norm_num) (by finiteness)]]
  norm_num

/-! ## A rejecting array -/

/-- An array that never verifies. -/
def deadArray (_ : Slot) : Bool × Fin 2 := (false, 0)

theorem blockHitTotal_deadArray : blockHitTotal deadArray = 0 := by
  rw [blockHitTotal, Fin.sum_univ_two,
    show (Finset.univ.filter fun j : Slot => 0 < blockCount deadArray 0 j).card = 0 from by decide,
    show (Finset.univ.filter fun j : Slot => 0 < blockCount deadArray 1 j).card = 0 from by decide]
  simp

/-- With nothing to rewind, the game reads exactly the one entry it drew. -/
theorem expectedValue_cost_samplingGame_deadArray_le :
    expectedValue (samplingGame 2 deadArray) (fun r => (r.2 : ℝ≥0∞)) ≤ 1 := by
  have h := expectedValue_cost_samplingGame_le (Q := Fin 2) (ι := Fin 1) (S := Fin 5) 2 deadArray
  refine h.trans (le_of_eq ?_)
  rw [blockHitTotal_deadArray]
  simp

/-! ## `P` is not a probability -/

/-- Both queries win, on complementary halves of the assignment space. -/
def forkedArray (j : Slot) : Bool × Fin 2 :=
  (true, if j (0, 0) = 0 then 0 else 1)

/-- Every block of query `0` holds a hit, and four fifths of query `1`'s blocks do, so `P = 9/5`.
`blockHitTotal` is a sum over the query index, not a probability. -/
theorem blockHitTotal_forkedArray : blockHitTotal forkedArray = 9 / 5 := by
  rw [blockHitTotal, Fin.sum_univ_two,
    show (Finset.univ.filter fun j : Slot => 0 < blockCount forkedArray 0 j).card = 25 from
      by decide,
    show (Finset.univ.filter fun j : Slot => 0 < blockCount forkedArray 1 j).card = 20 from
      by decide,
    card_slot]
  push_cast
  rw [ENNReal.div_add_div_same,
    ENNReal.div_eq_div_iff (by norm_num) (by finiteness) (by norm_num) (by finiteness)]
  norm_num

/-- Yet it never exceeds the number of queries. -/
example : blockHitTotal forkedArray ≤ Fintype.card (Fin 2) :=
  blockHitTotal_le_card forkedArray

/-! ## The per-coordinate count is strictly coarser -/

/-- The same alphabet, but query `0` now has two coordinates. -/
abbrev WideSlot : Type := Fin 1 × Fin 2 → Fin 5

/-- Accepting exactly when both of the query's coordinates are zero. -/
def wideArray (j : WideSlot) : Bool × Fin 1 :=
  (decide (j (0, 0) = 0 ∧ j (0, 1) = 0), 0)

/-- At an accepting assignment the block holds one hit — itself — while each column holds one too,
so the two agree there. -/
example : columnCount (fun j' => hitsAt wideArray 0 j') (0, 0) (fun _ => 0) = 1 := by decide

example : blockCount wideArray 0 (fun _ => 0) = 1 := by decide

/-- One coordinate away from accepting, the column through the *other* coordinate is empty while
the block still holds a hit. So `columnCount_le_blockCount` is a strict inequality in general, and
Lemma 8.1's per-query count really is coarser than the per-coordinate one. -/
theorem columnCount_lt_blockCount_wide :
    columnCount (fun j' => hitsAt wideArray 0 j') (0, 0) (fun p => if p.2 = 0 then 0 else 1) <
      blockCount wideArray 0 (fun p => if p.2 = 0 then 0 else 1) := by decide

example (j : WideSlot) :
    columnCount (fun j' => hitsAt wideArray 0 j') (0, 0) j ≤ blockCount wideArray 0 j :=
  columnCount_le_blockCount wideArray 0 0 j

end VCVioTest.Forking
