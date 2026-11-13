/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.Control.Monad.Measure.ExceptT
public import ToMathlib.MeasureTheory.Measure.GiryMonad
public import VCVio.EvalDist.Defs.Measure.Core

/-!
# Deprecated: re-exports `PolyFun.Control.Monad.Measure.ExceptT`

This module is deprecated. It re-exports `PolyFun.Control.Monad.Measure.ExceptT`, together with
`ToMathlib.MeasureTheory.Measure.GiryMonad` and `VCVio.EvalDist.Defs.Measure.Core` for the `𝒟[…]`
notation. Import those modules instead.
-/

deprecated_module
  "Import `PolyFun.Control.Monad.Measure.ExceptT` and this module's other imports instead."
  (since := "2026-11-10")
