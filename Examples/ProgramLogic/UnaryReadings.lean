/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import VCVio.ProgramLogic.Tactics.PrVCGen

/-!
# The four readings of one program

A statement about one oracle computation is read by `prvcgen` in the reading its shape selects,
each a core `Std.WP` instance on `OracleComp`:

| Statement | Reading | Verification conditions |
|---|---|---|
| `Pr{…}[p] = 1` | necessary (the global instance) | `p` on every possible outcome |
| `0 < Pr{…}[p]` | possible | a witness among the possible outcomes |
| `r ≤ Pr{…}[p]` | lower bound | `r ≤ …` over the outcomes, or an exact average |
| `Pr{…}[p] ≤ r` | upper bound | `… ≤ r` over the outcomes, or an exact average |

The examples state the four shapes about one coin-and-die program, then run a `for … in` loop
under the necessary reading with a loop invariant, through core's own rule `Spec.forIn_list`.
-/

public section

open OracleSpec OracleComp Std.WP ENNReal

namespace Examples.ProgramLogic.UnaryReadings

/-- A coin and a die: the result is the die's face, doubled on heads. -/
def coinAndDie : ProbComp ℕ := do
  let b ← $ᵗ Bool
  let d ← $[0..5]
  pure (if b then 2 * d else d)

/-- Necessary: every outcome is below `10`. The registered rules range over the possible
outcomes of each draw, named after the program's binders. -/
example : Pr{let n ← coinAndDie}[n ≤ 10] = 1 := by
  prvcgen [coinAndDie]
  cases b <;> simp <;> omega

/-- Possible: some outcome is `10`. The registered rules ask for a witness of each draw and
leave the continuation of a draw as the reading's `wp`, which `wp_iff_exists_support` turns
into an outcome in its support. -/
example : 0 < Pr{let n ← coinAndDie}[n = 10] := by
  prvcgen [coinAndDie]
  refine ⟨true, ?_⟩
  simp only [binderNameHint]
  rw [OracleComp.Possible.wp_iff_exists_support]
  simp only [↓existsAndEq, Nat.reduceAdd, ↓reduceIte, bind_pure_comp, MonadAttach.support_map,
    ProbComp.support_uniformFin, Set.image_univ, Set.mem_range, and_true]
  exact ⟨5, rfl⟩

/-- Lower bound: the result is even with probability at least one half, since every outcome on
heads is even. The coin is averaged exactly (`Spec.uniformSample_sum`, passed in brackets), which
leaves the continuation of each side of the coin as an event; the readback set and `simp` write
the average as a sum over the two sides, and a second `prvcgen` reads the heads event, whose
die draw is bounded on its outcomes. -/
example : 1 / 2 ≤ Pr{let n ← coinAndDie}[Even n] := by
  prvcgen [coinAndDie, OracleComp.Lower.Spec.uniformSample_sum]
  simp only [lower_readback, Fintype.univ_bool, Finset.sum_insert, Finset.mem_singleton,
    Bool.true_eq_false, not_false_eq_true, Finset.sum_singleton, Fintype.card_bool,
    Nat.cast_ofNat, ite_true]
  calc (1 : ℝ≥0∞) / 2 = (1 + 0) / 2 := by rw [add_zero]
    _ ≤ _ := by
      gcongr
      · prvcgen
        simp
      · exact zero_le

/-- Upper bound: the result is `10` with probability at most one half, since it needs heads.
The coin is averaged exactly (`Spec.uniformSample_avg`); the heads event is at most one, and a
second `prvcgen` reads the tails event, where the die's six faces are all below `10`. -/
example : Pr{let n ← coinAndDie}[n = 10] ≤ 1 / 2 := by
  prvcgen [coinAndDie, OracleComp.Upper.Spec.uniformSample_avg]
  simp only [upper_readback, Fintype.univ_bool, Finset.sum_insert, Finset.mem_singleton,
    Bool.true_eq_false, not_false_eq_true, Finset.sum_singleton, Fintype.card_bool,
    Nat.cast_ofNat, ite_true]
  calc _ ≤ ((1 : ℝ≥0∞) + 0) / 2 := by
        gcongr
        · exact prEvent_le_one _
        · prvcgen
          simp [propInd_eq_ite]
          omega
    _ = 1 / 2 := by rw [add_zero]

/-- A loop: draw a coin per element and count the heads. -/
def countHeads (xs : List ℕ) : ProbComp ℕ := do
  let mut c := 0
  for _ in xs do
    let b ← $ᵗ Bool
    if b then c := c + 1
  return c

/-- The count never exceeds the number of draws: a `for … in` loop under the necessary reading
takes its invariant through `invariants`, as a function of the elements consumed so far, the
elements remaining and the loop's state. Core's `Spec.forIn_list` applies to the loop as
elaborated; `prvcgen` supplies nothing beyond the reading. -/
example (xs : List ℕ) : Pr{let c ← countHeads xs}[c ≤ xs.length] = 1 := by
  prvcgen [countHeads] invariants
    · fun pref _ c => c ≤ pref.length
  all_goals simp_all
  omega

end Examples.ProgramLogic.UnaryReadings
