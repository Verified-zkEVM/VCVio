/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module
public import VCVio.EvalDist.Defs.Measure.Core

/-!
# Successful-output measure of failure

`LawfulFailureEvalDistSemantics` certifies that failure has zero successful-output measure.
This law is independent of attachment, pure, bind, and any discrete probability representation.
-/

public section

open MeasureTheory

universe u v

/-- A measure interpretation assigns zero successful-output mass to failure. -/
class LawfulFailureEvalDistSemantics (m : Type u → Type v) [Alternative m]
    [EvalDistSemantics m] : Prop where
  /-- Failure denotes the zero measure. -/
  denote_failure {α : Type u} [MeasurableSpace α] : 𝒟[(failure : m α)] = 0

/-- Failure has zero successful-output measure. -/
@[simp, grind =]
theorem evalDist_failure_eq_zero {m : Type u → Type v} [Alternative m]
    [EvalDistSemantics m] [LawfulFailureEvalDistSemantics m]
    {α : Type u} [MeasurableSpace α] : 𝒟[(failure : m α)] = 0 :=
  LawfulFailureEvalDistSemantics.denote_failure
