/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import Mathlib.Data.ENNReal.Inv

/-!
# Expected draws of a negative hypergeometric experiment

Sampling without replacement from a population of `M` items containing `G` successes, how many
draws are needed on average before `r` successes have been collected? Conditioning on the first
draw gives the recursion implemented by `expectedDraws`, and `expectedDraws_eq` evaluates it to
the closed form `r * (M + 1) / (G + 1)` whenever `r ≤ G ≤ M`.

The closed form is carried by `mul_expectedDraws`, which clears the denominator so that the
induction proving it never divides in `ℝ≥0∞`; `expectedDraws_eq` recovers the divided form.

Coordinate-wise rewinding arguments use this at `M = N - 1`, `G = l - 1` and `r = k - 1`: when a
challenge coordinate ranges over a set of size `N` of which `l` values are accepting, resampling
that coordinate without replacement collects `k - 1` further accepting values after at most
`(k - 1) * N / l` draws on average.
-/

@[expose] public section

open scoped ENNReal

namespace NegHypergeom

/-- Expected number of draws needed to collect `r` successes when sampling without replacement
from a population of `M` items containing `G` successes.

The first draw succeeds with probability `G / M`, leaving `G - 1` successes among `M - 1` items,
and fails with probability `(M - G) / M`, leaving `G` successes among `M - 1` items. Truncated
subtraction is harmless here: `G - 1` is only reached with a nonzero coefficient when `G ≠ 0`,
and `M + 1 - G` with a nonzero coefficient only when `G ≤ M`. An exhausted population draws
nothing. -/
noncomputable def expectedDraws : ℕ → ℕ → ℕ → ℝ≥0∞
  | _, _, 0 => 0
  | 0, _, _ + 1 => 0
  | M + 1, G, r + 1 =>
      1 + (G : ℝ≥0∞) / (M + 1) * expectedDraws M (G - 1) r
        + ((M + 1 - G : ℕ) : ℝ≥0∞) / (M + 1) * expectedDraws M G (r + 1)

@[simp] theorem expectedDraws_zero_right (M G : ℕ) : expectedDraws M G 0 = 0 := by
  cases M <;> rfl

@[simp] theorem expectedDraws_zero_left (G r : ℕ) : expectedDraws 0 G r = 0 := by
  cases r <;> rfl

theorem expectedDraws_succ (M G r : ℕ) :
    expectedDraws (M + 1) G (r + 1) =
      1 + (G : ℝ≥0∞) / (M + 1) * expectedDraws M (G - 1) r
        + ((M + 1 - G : ℕ) : ℝ≥0∞) / (M + 1) * expectedDraws M G (r + 1) :=
  rfl

/-- The closed form of `expectedDraws`, cleared of denominators: collecting `r` of the `G`
successes available among `M` items takes `r * (M + 1) / (G + 1)` draws on average. -/
theorem mul_expectedDraws (M : ℕ) : ∀ G r : ℕ, r ≤ G → G ≤ M →
    ((G : ℝ≥0∞) + 1) * expectedDraws M G r = r * (M + 1) := by
  induction M with
  | zero =>
      intro G r hr hG
      obtain rfl : G = 0 := Nat.le_zero.mp hG
      obtain rfl : r = 0 := Nat.le_zero.mp hr
      simp
  | succ M ih =>
      intro G r hr hG
      cases r with
      | zero => simp
      | succ r =>
        -- `G` is positive, so peel off the success the first draw might consume.
        obtain ⟨Gp, rfl⟩ : ∃ Gp, G = Gp + 1 := ⟨G - 1, by omega⟩
        have hGpM : Gp ≤ M := by omega
        -- Name the failure count, so the closing algebra never subtracts in `ℝ≥0∞`.
        obtain ⟨B, hB⟩ : ∃ B, Gp + B = M := ⟨M - Gp, by omega⟩
        have hBcast : (Gp : ℝ≥0∞) + (B : ℝ≥0∞) = (M : ℝ≥0∞) := by exact_mod_cast hB
        have hMne : ((M : ℝ≥0∞) + 1) ≠ 0 := by positivity
        have hMtop : ((M : ℝ≥0∞) + 1) ≠ ⊤ := by finiteness
        have hcancel : ((M : ℝ≥0∞) + 1) * ((M : ℝ≥0∞) + 1)⁻¹ = 1 :=
          ENNReal.mul_inv_cancel hMne hMtop
        -- A successful first draw leaves `r` successes to collect from `Gp` among `M`.
        have hgood : ((Gp : ℝ≥0∞) + 1) * ((M : ℝ≥0∞) + 1)⁻¹ * expectedDraws M Gp r =
            (r : ℝ≥0∞) := by
          have h1 := ih Gp r (by omega) hGpM
          calc ((Gp : ℝ≥0∞) + 1) * ((M : ℝ≥0∞) + 1)⁻¹ * expectedDraws M Gp r
              = (((Gp : ℝ≥0∞) + 1) * expectedDraws M Gp r) * ((M : ℝ≥0∞) + 1)⁻¹ := by ring
            _ = ((r : ℝ≥0∞) * ((M : ℝ≥0∞) + 1)) * ((M : ℝ≥0∞) + 1)⁻¹ := by rw [h1]
            _ = (r : ℝ≥0∞) * (((M : ℝ≥0∞) + 1) * ((M : ℝ≥0∞) + 1)⁻¹) := by ring
            _ = (r : ℝ≥0∞) := by rw [hcancel, mul_one]
        -- A failed first draw still leaves `r + 1` successes to collect from `Gp + 1` among `M`.
        -- When `Gp = M` the population has no failures left and the coefficient `B` is zero.
        have hbad : ((Gp : ℝ≥0∞) + 1 + 1) *
            ((B : ℝ≥0∞) * ((M : ℝ≥0∞) + 1)⁻¹ * expectedDraws M (Gp + 1) (r + 1)) =
            (B : ℝ≥0∞) * ((r : ℝ≥0∞) + 1) := by
          rcases le_or_gt (Gp + 1) M with hle | hgt
          · have h2 := ih (Gp + 1) (r + 1) (by omega) hle
            have h2' : ((Gp : ℝ≥0∞) + 1 + 1) * expectedDraws M (Gp + 1) (r + 1) =
                ((r : ℝ≥0∞) + 1) * ((M : ℝ≥0∞) + 1) := by
              push_cast at h2; exact h2
            calc ((Gp : ℝ≥0∞) + 1 + 1) *
                  ((B : ℝ≥0∞) * ((M : ℝ≥0∞) + 1)⁻¹ * expectedDraws M (Gp + 1) (r + 1))
                = (B : ℝ≥0∞) * (((Gp : ℝ≥0∞) + 1 + 1) * expectedDraws M (Gp + 1) (r + 1)) *
                    ((M : ℝ≥0∞) + 1)⁻¹ := by ring
              _ = (B : ℝ≥0∞) * (((r : ℝ≥0∞) + 1) * ((M : ℝ≥0∞) + 1)) *
                    ((M : ℝ≥0∞) + 1)⁻¹ := by rw [h2']
              _ = (B : ℝ≥0∞) * ((r : ℝ≥0∞) + 1) *
                    (((M : ℝ≥0∞) + 1) * ((M : ℝ≥0∞) + 1)⁻¹) := by ring
              _ = (B : ℝ≥0∞) * ((r : ℝ≥0∞) + 1) := by rw [hcancel, mul_one]
          · obtain rfl : B = 0 := by omega
            simp
        have hsub₁ : Gp + 1 - 1 = Gp := by omega
        have hsub₂ : M + 1 - (Gp + 1) = B := by omega
        rw [expectedDraws_succ, hsub₁, hsub₂, div_eq_mul_inv, div_eq_mul_inv]
        push_cast
        -- `(Gp + 2) + (Gp + 2) * r + B * (r + 1) = (r + 1) * (Gp + B + 2)`, and `Gp + B = M`.
        rw [mul_add, mul_add, mul_one, hgood, hbad, ← hBcast]
        ring

/-- Closed form for the expected number of draws, as a quotient. -/
theorem expectedDraws_eq {M G r : ℕ} (hr : r ≤ G) (hG : G ≤ M) :
    expectedDraws M G r = r * (M + 1) / (G + 1) := by
  have h := mul_expectedDraws M G r hr hG
  rw [div_eq_mul_inv, ← h, mul_right_comm,
    ENNReal.mul_inv_cancel (by positivity) (by finiteness), one_mul]

/-- The shape in which a coordinate resampling consumes this bound.

A coordinate ranges over a set of size `N` of which `l` values are accepting. One accepting value
is already in hand, so collecting `r` further accepting values draws without replacement from the
remaining `N - 1` values, `l - 1` of which are accepting, and takes `r * N / l` draws on
average. -/
theorem expectedDraws_resample {N l r : ℕ} (hr : r < l) (hl : l ≤ N) :
    expectedDraws (N - 1) (l - 1) r = r * N / l := by
  obtain ⟨l, rfl⟩ : ∃ l', l = l' + 1 := ⟨l - 1, by omega⟩
  obtain ⟨N, rfl⟩ : ∃ N', N = N' + 1 := ⟨N - 1, by omega⟩
  have h := expectedDraws_eq (M := N) (G := l) (r := r) (by omega) (by omega)
  simpa using h

/-- Unfolding the recursion twice agrees with the closed form, independently of
`mul_expectedDraws`: one accepting value among two, one more to collect. -/
example : expectedDraws 2 1 1 = 3 / 2 := by
  norm_num [expectedDraws]
  rw [div_eq_mul_inv, show (3 : ℝ≥0∞) = 2 + 1 by norm_num, add_mul,
    ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_mul]

end NegHypergeom
