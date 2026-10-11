/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module
public import VCVio

/-!
# Real total variation of oracle computations

The real-valued total variation laws in the shapes hybrid arguments use: a common continuation
contracts the distance, a common prefix bounds it by the prefix-weighted sum of the continuations'
distances, the triangle inequality chains two hops, post-processing contracts the distance, and the
real probabilities of an event under two computations differ by at most their distance. The last
entry is the complement of an event, which oracle computations never fail to decide.
-/

open OracleComp

namespace VCVioTest.TotalVariationReal

variable {α β : Type} [MeasurableSpace α] [DiscreteMeasurableSpace α] [MeasurableSpace β]

example (a₁ a₂ : ProbComp α) (k : α → ProbComp β) :
    measureTVDist (a₁ >>= k) (a₂ >>= k) ≤ measureTVDist a₁ a₂ :=
  measureTVDist_bind_right_le a₁ a₂ k

example (a : ProbComp α) (k₁ k₂ : α → ProbComp β) :
    measureTVDist (a >>= k₁) (a >>= k₂) ≤
      ∑' x, (Pr{let y ← a}[y = x]).toReal * measureTVDist (k₁ x) (k₂ x) :=
  measureTVDist_bind_left_le_tsum a k₁ k₂

/-- One hybrid step: change the prefix, then the continuation. -/
example (a₁ a₂ : ProbComp α) (k₁ k₂ : α → ProbComp β) {ζ : ℝ}
    (hζ : measureTVDist a₁ a₂ ≤ ζ) :
    measureTVDist (a₁ >>= k₁) (a₂ >>= k₂) ≤
      ζ + ∑' x, (Pr{let y ← a₂}[y = x]).toReal * measureTVDist (k₁ x) (k₂ x) :=
  calc measureTVDist (a₁ >>= k₁) (a₂ >>= k₂)
      ≤ measureTVDist (a₁ >>= k₁) (a₂ >>= k₁) + measureTVDist (a₂ >>= k₁) (a₂ >>= k₂) :=
        measureTVDist_triangle _ _ _
    _ ≤ ζ + ∑' x, (Pr{let y ← a₂}[y = x]).toReal * measureTVDist (k₁ x) (k₂ x) :=
        add_le_add ((measureTVDist_bind_right_le a₁ a₂ k₁).trans hζ)
          (measureTVDist_bind_left_le_tsum a₂ k₁ k₂)

example (a₁ a₂ : ProbComp ℕ) (f : ℕ → Bool) :
    measureTVDist (f <$> a₁) (f <$> a₂) ≤ measureTVDist a₁ a₂ :=
  measureTVDist_map_le a₁ a₂ f Measurable.of_discrete

/-- The real success probabilities of two games differ by at most their distance. -/
example (g₁ g₂ : ProbComp Bool) :
    (Pr{let b ← g₁}[b = true]).toReal ≤
      (Pr{let b ← g₂}[b = true]).toReal + measureTVDist g₁ g₂ := by
  have h := abs_prEvent_toReal_sub_le_measureTVDist g₁ g₂ (· = true) Measurable.of_discrete
  linarith [(abs_le.mp h).2]

example (oa : ProbComp α) (p : α → Prop) :
    Pr{let x ← oa}[¬ p x] = 1 - Pr{let x ← oa}[p x] :=
  prEvent_not_eq_one_sub oa p

end VCVioTest.TotalVariationReal
