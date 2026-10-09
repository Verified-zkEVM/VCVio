/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import VCVio.ProgramLogic.Unary.HoareTriple

/-!
# `gcongr` through `wp`

Canaries for the `@[gcongr]` tag on `wp_mono`: `gcongr` descends through `wp` into the
postcondition and structural support, also under a finite sum. Measurable assertions use
`wp_eq_lintegral` in the chosen output space.
-/

public section

open scoped OracleComp.Quantitative Std.Internal.Do

open ENNReal OracleSpec OracleComp MeasureTheory
open OracleComp.ProgramLogic
open scoped OracleComp.ProgramLogic

run_cmd do
  let env ← Lean.getEnv
  for name in [`PMF, `SPMF, `EvalDistCompatible, `DiscreteEvalDistCompatible] do
    if env.contains name then
      throwError "native Hoare WP unexpectedly imports {name}"

namespace VCVioTest.ProgramLogicGCongr

universe u

variable {ι : Type u} {spec : OracleSpec ι} {α : Type}
  [∀ t, MeasurableSpace (spec.Range t)]
  [∀ t, DiscreteMeasurableSpace (spec.Range t)] [OracleSpec.IsMeasureSpec spec]

example (P Q : Prop) (h : P → Q) : propInd P ≤ propInd Q := by apply_rw [h]

example (oa : OracleComp spec α) (p q : α → Prop) (h : ∀ x, p x → q x) :
    wp oa (fun x ↦ propInd (p x)) ≤ wp oa (fun x ↦ propInd (q x)) := by apply_rw [h]

example (oa : OracleComp spec α) (f g : α → ℝ≥0∞) (h : ∀ x, f x ≤ g x) :
    wp oa f ≤ wp oa g := by
  gcongr with x
  exact h x

example (oa : OracleComp spec α) (f g : Fin 3 → α → ℝ≥0∞) (h : ∀ s x, f s x ≤ g s x) :
    ∑ s, wp oa (f s) ≤ ∑ s, wp oa (g s) := by
  gcongr with s _ x
  exact h s x

example [MeasurableSpace α] (oa : OracleComp spec α) (post : α → ℝ≥0∞)
    (hpost : Measurable post) :
    wp oa post = ∫⁻ x, post x ∂𝒟[oa] :=
  wp_eq_lintegral oa post hpost

/-- Support-aware descent exposes exactly the hypothesis needed by the continuation. -/
example (oa : OracleComp spec α) (f g : α → ℝ≥0∞)
    (h : ∀ x ∈ support oa, f x ≤ g x) : wp oa f ≤ wp oa g := by
  gcongr with x hx
  guard_hyp hx : x ∈ support oa
  guard_target = f x ≤ g x
  exact h x hx

example (oa : OracleComp spec α) (f g : Fin 3 → α → ℝ≥0∞)
    (h : ∀ i, ∀ x ∈ support oa, f i x ≤ g i x) :
    ∑ i, wp oa (f i) ≤ ∑ i, wp oa (g i) := by
  gcongr with i _ x hx
  exact h i x hx

/-- Public normalization exposes structural support to core WP congruence. -/
example (oa : OracleComp spec α) (f g : α → ℝ≥0∞)
    (h : ∀ x ∈ support oa, f x ≤ g x) :
    Std.Internal.Do.wp oa f Lean.Order.bot ≤ Std.Internal.Do.wp oa g Lean.Order.bot := by
  simp only [OracleComp.Quantitative.wp_eq_mAlgOrdered_wp]
  gcongr with x hx
  exact h x hx

example [Finite α] (oa : OracleComp spec α) (post : α → ℝ≥0∞)
    (hpost : ∀ x, post x ≠ ⊤) : wp oa post ≠ ⊤ := by finiteness

end VCVioTest.ProgramLogicGCongr
