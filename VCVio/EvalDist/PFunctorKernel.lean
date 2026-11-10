/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.PFunctor.Free.Measure.Kernel
public import ToCslib.MeasureTheory.Function.AEMeasurable
public import ToCslib.MeasureTheory.Measure.Coupling.Bind
public import ToMathlib.MeasureTheory.Measure.GiryMonad
public import ToMathlib.MeasureTheory.Measure.Monotone

/-!
# Deprecated: re-exports `PolyFun.PFunctor.Free.Measure.Kernel`

This module is deprecated. It re-exports `PolyFun.PFunctor.Free.Measure.Kernel`, together with
`ToCslib.MeasureTheory.Function.AEMeasurable`, `ToCslib.MeasureTheory.Measure.Coupling.Bind`,
`ToMathlib.MeasureTheory.Measure.GiryMonad` and `ToMathlib.MeasureTheory.Measure.Monotone`. Import
those modules instead.
-/

deprecated_module
  "Import `PolyFun.PFunctor.Free.Measure.Kernel` and this module's other imports instead."
  (since := "2026-11-10")
