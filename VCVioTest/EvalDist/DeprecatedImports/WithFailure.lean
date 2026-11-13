/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import VCVio.EvalDist.WithFailure -- deprecated_module: ignore

/-!
# Importing the deprecated `VCVio.EvalDist.WithFailure`

The only import is the deprecated `VCVio.EvalDist.WithFailure`. The examples check that it provides
the failure-completed measure and the `Pr{…}[…]` notation. The import suppresses its deprecation
warning, so the test library still builds without warnings.
-/

public section

open MeasureTheory

namespace VCVioTest.DeprecatedImports.WithFailure

example {m : Type → Type} [EvalDistSemantics m] {α : Type} [MeasurableSpace α] (mx : m α) :
    IsProbabilityMeasure (evalDistWithFailure mx) :=
  inferInstance

example {m : Type → Type} [Monad m] [EvalDistSemantics m] {α : Type} [MeasurableSpace α]
    (mx : m α) (p : α → Prop) : Pr{let x ← mx}[p x] ≤ 1 :=
  prEvent_le_one _

end VCVioTest.DeprecatedImports.WithFailure
