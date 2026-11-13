/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.PFunctor.Free.Measure.EvalDist
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import VCVio.EvalDist.Defs.Measure.Core

/-!
# Deprecated: re-exports `PolyFun.PFunctor.Free.Measure.EvalDist`

This module is deprecated. It re-exports `PolyFun.PFunctor.Free.Measure.EvalDist`, together with
`Mathlib.MeasureTheory.Measure.ProbabilityMeasure` and `VCVio.EvalDist.Defs.Measure.Core` for the
`𝒟[…]` notation. Import those modules instead.
-/

deprecated_module
  "Import `PolyFun.PFunctor.Free.Measure.EvalDist` and this module's other imports instead."
  (since := "2026-11-10")
