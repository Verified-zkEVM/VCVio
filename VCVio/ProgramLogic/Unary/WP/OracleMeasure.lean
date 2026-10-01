/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module
public import VCVio.ProgramLogic.Unary.WP.Measure
public import VCVio.OracleComp.EvalDist.Measure

/-!
# Quantitative correctness from possible oracle outputs

Structural postcondition bounds imply almost-everywhere bounds under the chosen response
measures. Discrete answers suffice; uniformity and positive answer masses are unnecessary.
-/

public section

open MeasureTheory
open scoped ENNReal

universe u

namespace ExpectationWP

variable {ι : Type u} {spec : OracleSpec.{u, 0} ι}
  [OracleSpec.IsMeasureSpec spec]
  {α : Type}

/-- A bound on the possible outputs bounds the expectation. -/
theorem wp_le_const_of_support (mx : OracleComp spec α) {f : α → ℝ≥0∞} {c : ℝ≥0∞}
    (hf : ∀ x ∈ support mx, f x ≤ c) : wp⟦mx⟧ f ≤ c :=
  (_root_.wp_mono_of_support mx hf).trans_eq (wp_const_of_oracle mx c)

/-- An additive allowance on the possible outputs bounds the expectation. -/
theorem wp_le_const_add_of_support (mx : OracleComp spec α) {f g : α → ℝ≥0∞} {c : ℝ≥0∞}
    (hfg : ∀ x ∈ support mx, f x ≤ c + g x) : wp⟦mx⟧ f ≤ c + wp⟦mx⟧ g := by
  refine (_root_.wp_mono_of_support mx hfg).trans_eq ?_
  rw [wp_add, wp_const_of_oracle]

end ExpectationWP
