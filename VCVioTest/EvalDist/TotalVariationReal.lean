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
entry is the complement of an event, which oracle computations never fail to decide; then
a uniform bound and an identical-until-bad bound after a common prefix, and the commutation
of independent draws inside a two-draw event.
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

/-- A per-continuation bound survives a common prefix. -/
example (a : ProbComp α) (k₁ k₂ : α → ProbComp β) {δ : ℝ} (hδ : 0 ≤ δ)
    (h : ∀ x, measureTVDist (k₁ x) (k₂ x) ≤ δ) :
    measureTVDist (a >>= k₁) (a >>= k₂) ≤ δ :=
  measureTVDist_bind_left_le_of_forall_le a k₁ k₂ hδ h

/-- Identical until bad: continuations equal in distribution off a bad prefix event. -/
example (a : ProbComp α) (k₁ k₂ : α → ProbComp β) (bad : α → Prop)
    (h : ∀ x, ¬ bad x → k₁ x =ᵈ k₂ x) :
    measureTVDist (a >>= k₁) (a >>= k₂) ≤ (Pr{let x ← a}[bad x]).toReal :=
  measureTVDist_bind_left_le_prEvent_of_evalDistEq a k₁ k₂ bad h

/-- Independent draws commute inside a two-draw event, written as the notation writes it. -/
example (a : ProbComp α) (b : ProbComp β) (p : α → β → Prop) :
    Pr{let x ← a; let y ← b}[p x y] = Pr{let y ← b; let x ← a}[p x y] := by
  rw [prEvent_bind_map_swap]

open scoped ENNReal in
open OracleComp.ProgramLogic.Relational in
/-- The flag-guarded expectation of a step is a sum over its unflagged outputs; at `ProbComp` the
answer types are finite, as the lemma asks. -/
example (mx : ProbComp (ℕ × Bool × Bool)) (F : ℕ × Bool × Bool → ℝ≥0∞) :=
  wp_ite_flag_eq_tsum mx F

end VCVioTest.TotalVariationReal
