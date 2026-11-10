/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.PFunctor.Free.Measure.Path
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import PolyFun.PFunctor.Free.Measure.EvalDist
public import VCVio.EvalDist.Defs.Measure.Core

/-!
# Deprecated: re-exports `PolyFun.PFunctor.Free.Measure.Path`

This module is deprecated. It re-exports `PolyFun.PFunctor.Free.Measure.Path`, together with
`Mathlib.MeasureTheory.Measure.ProbabilityMeasure`, `PolyFun.PFunctor.Free.Measure.EvalDist` and
`VCVio.EvalDist.Defs.Measure.Core` for the `𝒟[…]` notation. Import those modules instead.
-/

deprecated_module
  "Import `PolyFun.PFunctor.Free.Measure.Path` and this module's other imports instead."
  (since := "2026-11-10")
