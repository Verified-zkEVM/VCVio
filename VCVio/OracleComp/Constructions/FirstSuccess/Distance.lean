/-
Copyright (c) 2026 Quang Dao, Oleksandr Vovkotrub, Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Oleksandr Vovkotrub, Matthias Meijers
-/

module
public import VCVio.Algorithms.FirstSuccess.Basic
public import VCVio.OracleComp.EvalDist.Sum
public import VCVio.OracleComp.ProbComp.Basic
public import Mathlib.Algebra.Ring.GeomSum

/-!
# Total variation of bounded first-success search

A per-attempt distance is amplified only along the prefixes of returned failures. Bounding the
second sampler's returned-failure probability gives a finite geometric sum, without an assumption
that each attempt returns a payload.
-/

public section

namespace VCVio.Algorithms.FirstSuccess

open OracleComp
open scoped ENNReal BigOperators

/-- Per-attempt total variation accumulates along the second loop's returned-failure prefixes. -/
lemma measureTVDist_run_le_geometric {α : Type} [MeasurableSpace (Option α)]
    [DiscreteMeasurableSpace (Option α)] (a₁ a₂ : ProbComp (Option α))
    {ζ q : ℝ} (hζ : measureTVDist a₁ a₂ ≤ ζ) (hq : Pr{let x ← a₂}[x = none].toReal ≤ q) :
    ∀ n : ℕ, measureTVDist (run a₁ n) (run a₂ n) ≤
      ζ * ∑ j ∈ Finset.range n, q ^ j
  | 0 => by simp
  | (n + 1) => by
    have hq0 : 0 ≤ q := le_trans ENNReal.toReal_nonneg hq
    have hζ0 : 0 ≤ ζ := le_trans (measureTVDist_nonneg a₁ a₂) hζ
    have ih := measureTVDist_run_le_geometric a₁ a₂ hζ hq n
    have hGeomNonneg : (0 : ℝ) ≤ ∑ j ∈ Finset.range n, q ^ j :=
      Finset.sum_nonneg fun j _ => pow_nonneg hq0 j
    set k₁ : Option α → ProbComp (Option α) := fun r =>
      match r with
      | some a => pure (some a)
      | none => run a₁ n with hk₁
    set k₂ : Option α → ProbComp (Option α) := fun r =>
      match r with
      | some a => pure (some a)
      | none => run a₂ n with hk₂
    have hterm : ∀ b : Option α, b ≠ (none : Option α) →
        Pr{let x ← a₂}[x = b].toReal * measureTVDist (k₁ b) (k₂ b) = 0 := by
      intro b hb
      match b, hb with
      | some a, _ => simp [hk₁, hk₂]
    have hStep : measureTVDist (a₂ >>= k₁) (a₂ >>= k₂) ≤
        Pr{let x ← a₂}[x = none].toReal * measureTVDist (run a₁ n) (run a₂ n) := by
      refine le_trans (measureTVDist_bind_left_le_tsum a₂ k₁ k₂) (le_of_eq ?_)
      rw [tsum_eq_single (none : Option α) hterm]
    calc
      measureTVDist (run a₁ (n + 1)) (run a₂ (n + 1))
          = measureTVDist (a₁ >>= k₁) (a₂ >>= k₂) := by
            rw [run_succ, run_succ]
            rfl
      _ ≤ measureTVDist (a₁ >>= k₁) (a₂ >>= k₁) + measureTVDist (a₂ >>= k₁) (a₂ >>= k₂) :=
            measureTVDist_triangle _ _ _
      _ ≤ ζ + Pr{let x ← a₂}[x = none].toReal *
            measureTVDist (run a₁ n) (run a₂ n) :=
            add_le_add (le_trans (measureTVDist_bind_right_le a₁ a₂ k₁) hζ) hStep
      _ ≤ ζ + q * (ζ * ∑ j ∈ Finset.range n, q ^ j) :=
            add_le_add le_rfl (mul_le_mul hq ih (measureTVDist_nonneg _ _) hq0)
      _ = ζ * ∑ j ∈ Finset.range (n + 1), q ^ j := by
            have hsum : ∑ j ∈ Finset.range (n + 1), q ^ j =
                q * (∑ j ∈ Finset.range n, q ^ j) + 1 := by
              rw [Finset.sum_range_succ', Finset.mul_sum]
              simp [pow_succ']
            rw [hsum]
            ring

end VCVio.Algorithms.FirstSuccess
