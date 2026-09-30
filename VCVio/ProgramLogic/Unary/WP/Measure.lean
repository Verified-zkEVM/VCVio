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

open MeasureTheory Std.WP
open scoped ENNReal

universe v

namespace MeasureProgramLogic.Quantitative

variable (m : Type → Type v) [Monad m] [EvalDistSemantics m] [LawfulEvalDistSemantics m]

/-- Select the ordered expectation algebra of successful-output measures. The scope's priority
sits above core's direct instances and below the reading scopes of `OracleComp`
(`OracleComp.Qualitative.Dispatch`, `OracleComp.Angelic`, `OracleComp.Upper`, …), so a reading
opened for oracle computations is never outranked by this generic one. -/
noncomputable scoped instance (priority := 1050) instMAlgOrdered : MAlgOrdered m ℝ≥0∞ :=
  toMAlgOrdered m

variable {m} in
/-- The selected algebra integrates its actual nonnegative output. -/
@[simp]
theorem μ_eq_lintegral (mx : m ℝ≥0∞) : MAlgOrdered.μ mx = ∫⁻ x, x ∂𝒟[mx] := rfl

/-- Select the expectation interpretation of successful-output measures. -/
noncomputable scoped instance (priority := 1050) instWP [LawfulMonad m] :
    WPMonad m ℝ≥0∞ EStack⟨⟩ :=
  measureWP m

/-- The expectation interpretation as a direct `WP` instance on programs. Core interprets its
concrete monads (`Id`, `Option`, `Except`, …) through direct `WP` instances, which instance search
tries before any `WPMonad`-derived one; this instance outranks them while the scope is open. -/
noncomputable scoped instance (priority := 1050) wpInst [LawfulMonad m] {α : Type} :
    WP (m α) α ℝ≥0∞ EStack⟨⟩ :=
  (measureWP m).toWP α

end MeasureProgramLogic.Quantitative
