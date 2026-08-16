/-
Copyright (c) 2026 Oleksandr Vovkotrub. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oleksandr Vovkotrub
-/

module
public import Mathlib.Analysis.SumIntegralComparisons
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Improper Integrals Of One-Sided Monotone Functions Versus Unit-Grid Sums

Mathlib's `AntitoneOn.integral_le_sum` and `MonotoneOn.integral_le_sum` compare the integral
of a monotone function over a bounded interval with a finite sum of its values on a
unit-spaced grid. This file passes to the limit, comparing the *improper* integral over a
half-infinite ray with the corresponding `tsum` over the unit grid anchored at the ray's
endpoint.

## Main Results

- `integral_Ioi_le_tsum_of_antitoneOn`: for `f` antitone on `Ici c`,
  `∫ x in Ioi c, f x ≤ ∑' n : ℕ, f (c + n)`.
- `integral_Iic_le_tsum_of_monotoneOn`: for `f` monotone on `Iic c`,
  `∫ x in Iic c, f x ≤ ∑' n : ℕ, f (c - n)`.

Both directions ask for integrability on the ray and summability of the grid values, and
each is proved by comparing the two limits termwise along the truncations `[c, c + N]` and
`[c - N, c]` respectively.
-/

@[expose] public section

open Filter MeasureTheory Set

/-- The integral of an antitone function over `(c, ∞)` is at most the sum of its values on
the unit grid `c, c + 1, c + 2, …`: each grid value dominates the integral over the unit
interval to its right. -/
theorem integral_Ioi_le_tsum_of_antitoneOn {f : ℝ → ℝ} {c : ℝ}
    (hf : AntitoneOn f (Ici c)) (hint : IntegrableOn f (Ioi c))
    (hsum : Summable fun n : ℕ => f (c + n)) :
    ∫ x in Ioi c, f x ≤ ∑' n : ℕ, f (c + n) := by
  refine le_of_tendsto_of_tendsto'
    (intervalIntegral_tendsto_integral_Ioi c hint
      (tendsto_atTop_add_const_left atTop c tendsto_natCast_atTop_atTop))
    hsum.hasSum.tendsto_sum_nat
    fun N => AntitoneOn.integral_le_sum (hf.mono Icc_subset_Ici_self)

/-- The integral of a monotone function over `(-∞, c]` is at most the sum of its values on
the unit grid `c, c - 1, c - 2, …`: each grid value dominates the integral over the unit
interval to its left. -/
theorem integral_Iic_le_tsum_of_monotoneOn {f : ℝ → ℝ} {c : ℝ}
    (hf : MonotoneOn f (Iic c)) (hint : IntegrableOn f (Iic c))
    (hsum : Summable fun n : ℕ => f (c - n)) :
    ∫ x in Iic c, f x ≤ ∑' n : ℕ, f (c - n) := by
  have hlim : Tendsto (fun N : ℕ => c - (N : ℝ)) atTop atBot := by
    simpa [sub_eq_add_neg] using
      tendsto_atBot_add_const_left atTop c
        (tendsto_neg_atTop_atBot.comp tendsto_natCast_atTop_atTop)
  refine le_of_tendsto_of_tendsto'
    (intervalIntegral_tendsto_integral_Iic c hint hlim)
    hsum.hasSum.tendsto_sum_nat
    fun N => ?_
  have hc : c - (N : ℝ) + (N : ℝ) = c := by ring
  have key := MonotoneOn.integral_le_sum (f := f) (x₀ := c - (N : ℝ)) (a := N)
    (by rw [hc]; exact hf.mono Icc_subset_Iic_self)
  rw [hc] at key
  refine key.trans (le_of_eq ?_)
  rw [← Finset.sum_range_reflect (fun i => f (c - (N : ℝ) + (i + 1 : ℕ))) N]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hiN : i < N := Finset.mem_range.mp hi
  congr 1
  rw [show N - 1 - i + 1 = N - i by omega, Nat.cast_sub hiN.le]
  ring
