/-
Copyright (c) 2026 VCVio Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import VCVio.CryptoFoundations.CoordinateFork.Finder
public import VCVio.CryptoFoundations.Rewinding.FixedTape

/-!
# Figure 11 as a black-box finder: instances and comparisons

**Non-vacuity.** At `ι = Fin 2`, `S = Fin 5` and `k = 2`, the finder contract holds at error
`2 / 5 < 1` and cost `3`, so neither bound collapses.

**Agreement with the threshold finder.** On one coordinate, the coordinate-wise error
`ℓ (k - 1) / N` equals the threshold error `1 - ∏ (1 - (k - 1) / N)`; the two finders differ only
from two coordinates on.

**Transfer to a prover.** `Rewinding.ResetPolicy.finder_bounds_honest` applies to the finder as it
does to the threshold finder: against reruns of a prover with a frozen coin tape, the honest
acceptance probability bounds the finder's success, and the expected number of reruns is at most
three.
-/

public section

open OracleComp OracleSpec Rewinding
open scoped ENNReal

namespace CoordinateFinderTest

/-- The contract at two coordinates of five values each, with `k = 2`: error `2 / 5`, cost `3`. -/
theorem isFinder_twoCoordinates :
    IsFinder (fun ρ X => CoordinateWise.IsCoordSpecialSound 2 X ∧ ∀ c ∈ X, ρ c = true)
      (coordFinder (ι := Fin 2) (S := Fin 5) 2) (2 / 5) 3 := by
  have h := isFinder_coordFinder (ι := Fin 2) (S := Fin 5) 2
  simp only [Fintype.card_fin, Nat.cast_ofNat, show (2 - 1 : ℕ) = 1 from rfl, Nat.cast_one,
    mul_one] at h
  convert h using 1
  norm_num

/-- On one coordinate the coordinate-wise and threshold errors agree. -/
example : thresholdError (fun _ : Fin 1 => Fin 5) (fun _ => 2) =
    (Fintype.card (Fin 1) : ℝ≥0∞) * (2 - 1 : ℕ) / Fintype.card (Fin 5) := by
  have hle : (1 : ℝ≥0∞) / 5 ≤ 1 := ENNReal.div_le_of_le_mul (by norm_num)
  simp only [thresholdError, Finset.univ_unique, Finset.prod_singleton, Fintype.card_fin,
    show (2 - 1 : ℕ) = 1 from rfl, Nat.cast_one, Nat.cast_ofNat, one_mul]
  exact ENNReal.sub_sub_cancel ENNReal.one_ne_top hle

/-- Against reruns of a prover with a frozen coin tape, the honest acceptance probability,
averaged over the twenty-five challenges, is at most `2 / 5` plus `3 / 5` times the finder's success
probability, and the finder makes at most three reruns in expectation. -/
example (run : ((i : Fin 2) → Fin 5) → ProbComp Bool) :
    (∑ c, Pr{let b ← (do (simulateQ (coins (S := Unit)) (run c)).run' (← pure ()))}[b = true]) /
          Fintype.card ((i : Fin 2) → Fin 5) ≤
        2 / 5 + (1 - 2 / 5) *
          Pr{let z ← fixedTape.attempt run (coordFinder (ι := Fin 2) (S := Fin 5) 2)}[z.1.isSome] ∧
      expectedCalls (fixedTape.attempt run (coordFinder (ι := Fin 2) (S := Fin 5) 2)) ≤ 3 :=
  fixedTape.finder_bounds_honest run isFinder_twoCoordinates

end CoordinateFinderTest
