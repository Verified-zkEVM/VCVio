/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module
public import VCVio.OracleComp.Constructions.WithoutReplacement.Basic
public import VCVio.EvalDist.Expectation
public import VCVio.OracleComp.EvalDist.Measure

/-!
# Drawing without replacement and discrete expectation equations

The drawing loop, operational properties, and measure-valued draw-count integrals live in
`VCVio.OracleComp.Constructions.WithoutReplacement.Basic`. This module also provides discrete
`expectedValue` equations for its expected length.
-/

public section

open scoped ENNReal

namespace ProbComp

variable {S : Type}

/-! ## Discrete expectation equations -/


open OracleComp.EvalDist in
/-- Prefixing a fixed value adds one to the discrete expected length. -/
@[deprecated lintegral_evalDist_length_cons_map (since := "2026-09-16")]
theorem expectedValue_length_cons_map (y : S) (mc : ProbComp (List S)) :
    expectedValue ((y :: ·) <$> mc) (fun d ↦ (d.length : ENNReal)) =
      expectedValue mc (fun d ↦ (d.length : ENNReal)) + 1 := by
  simpa only [DiscreteEvalDistCompatible.lintegral_evalDist, Measurable.of_discrete,
    ← expectedValue_def, expectedValue_map] using lintegral_evalDist_length_cons_map y mc

open OracleComp.EvalDist in
/-- The discrete expected length agrees with the negative hypergeometric recursion. -/
@[deprecated lintegral_evalDist_length_drawUntil (since := "2026-09-16")]
theorem expectedValue_length_drawUntil (accept : S → Bool) (n : ℕ) :
    ∀ (r : ℕ) (l : List S), l.length = n →
      expectedValue (drawUntil accept r l) (fun d ↦ (d.length : ENNReal)) =
        NegHypergeom.expectedDraws n (l.countP accept) r := by
  intro r l hl
  simpa only [DiscreteEvalDistCompatible.lintegral_evalDist, Measurable.of_discrete,
    ← expectedValue_def, expectedValue_map] using
    lintegral_evalDist_length_drawUntil accept n r l hl

open OracleComp.EvalDist in
/-- The negative hypergeometric bound applies to the discrete expected length. -/
@[deprecated lintegral_evalDist_length_drawUntil_le (since := "2026-09-16")]
theorem expectedValue_length_drawUntil_le (accept : S → Bool) (r : ℕ) (l : List S) :
    expectedValue (drawUntil accept r l) (fun d ↦ (d.length : ENNReal)) ≤
      r * (l.length + 1) / (l.countP accept + 1) := by
  simpa only [DiscreteEvalDistCompatible.lintegral_evalDist, Measurable.of_discrete,
    ← expectedValue_def, expectedValue_map] using
    lintegral_evalDist_length_drawUntil_le accept r l

end ProbComp
