/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module
public import VCVio.EvalDist.Expectation

/-!
# Selecting the measure interpretation

`open scoped MeasureProgramLogic.Quantitative` makes the expectation interpretation of lawful
measure semantics, `MeasureProgramLogic.measureWP` (`VCVio.EvalDist.Expectation`), the core
weakest-precondition instance of every such monad, so `wp mx post ⊥` and core triples read
expectations. Its laws are stated on `wp⟦mx⟧ post` in `VCVio.EvalDist.Expectation` and
`VCVio.EvalDist.ProbabilityNotation`.

Opening the scope selects the quantitative carrier before core instances whose carrier is
`Prop`.
-/

public section

open MeasureTheory Std.Internal.Do
open scoped ENNReal

universe v

namespace MeasureProgramLogic.Quantitative

variable (m : Type → Type v) [Monad m] [EvalDistSemantics m] [LawfulEvalDistSemantics m]

/-- Select the ordered expectation algebra of successful-output measures. -/
noncomputable scoped instance (priority := 1100) instMAlgOrdered : MAlgOrdered m ℝ≥0∞ :=
  toMAlgOrdered m

variable {m} in
/-- The selected algebra integrates its actual nonnegative output. -/
@[simp]
theorem μ_eq_lintegral (mx : m ℝ≥0∞) : MAlgOrdered.μ mx = ∫⁻ x, x ∂𝒟[mx] := rfl

/-- Select the expectation interpretation of successful-output measures. -/
noncomputable scoped instance (priority := 1100) instWP [LawfulMonad m] :
    WPMonad m ℝ≥0∞ EPost.Nil :=
  measureWP m

end MeasureProgramLogic.Quantitative
