/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import VCVio.EvalDist.Lossless -- deprecated_module: ignore

/-!
# Importing the deprecated `VCVio.EvalDist.Lossless`

The only import is the deprecated `VCVio.EvalDist.Lossless`. The examples check that it provides
the lossless measure semantics, the `𝒟[…]` notation and Mathlib's `ProbabilityMeasure`. The import
suppresses its deprecation warning, so the test library still builds without warnings.
-/

public section

open MeasureTheory

namespace VCVioTest.DeprecatedImports.Lossless

example {m : Type → Type} [EvalDistSemantics m] [LosslessEvalDistSemantics m] {α : Type}
    [MeasurableSpace α] (mx : m α) : 𝒟[mx] Set.univ = 1 :=
  evalDist_apply_univ_of_lossless mx

noncomputable example {m : Type → Type} [EvalDistSemantics m] [LosslessEvalDistSemantics m]
    {α : Type} [MeasurableSpace α] (mx : m α) : ProbabilityMeasure α :=
  ⟨𝒟[mx], inferInstance⟩

end VCVioTest.DeprecatedImports.Lossless
