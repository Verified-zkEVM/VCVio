/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import PolyFun.Control.Monad.Measure.SemanticsVia
public import ToMathlib.MeasureTheory.Measure.GiryMonad
public import VCVio.EvalDist.Defs.Measure.Core

/-!
# Deprecated: re-exports `PolyFun.Control.Monad.Measure.SemanticsVia`

This module is deprecated. It re-exports `PolyFun.Control.Monad.Measure.SemanticsVia`, together with
`ToMathlib.MeasureTheory.Measure.GiryMonad` and `VCVio.EvalDist.Defs.Measure.Core` for the `𝒟[…]`
notation. Import those modules instead.
-/

deprecated_module
  "Import `PolyFun.Control.Monad.Measure.SemanticsVia` and this module's other imports instead."
  (since := "2026-11-10")
