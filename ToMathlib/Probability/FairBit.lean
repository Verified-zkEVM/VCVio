/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module
public import ToMathlib.Probability.UniformOn
public import Mathlib.MeasureTheory.Measure.GiryMonad

/-! # The measure-level fair-bit mixture rule -/

public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace MeasureTheory.Measure

/-- Binding a fair Boolean law gives the equal mixture of its two continuation measures. -/
theorem bind_uniformOn_bool {X : Type*} [MeasurableSpace X] (f : Bool → Measure X) :
    (uniformOn (Set.univ : Set Bool)).bind f = (2 : ℝ≥0∞)⁻¹ • (f false + f true) := by
  ext s hs
  rw [Measure.bind_apply hs Measurable.of_discrete.aemeasurable, lintegral_fintype,
    Measure.smul_apply, Measure.add_apply]
  simp only [uniformOn_univ_apply_singleton, Fintype.card_bool, Nat.cast_ofNat,
    Fintype.sum_bool, smul_eq_mul]
  ring

end MeasureTheory.Measure
