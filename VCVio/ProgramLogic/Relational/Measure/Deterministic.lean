/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.Control.Monad.Measure.Relational.Deterministic
public import ToMathlib.Control.Except
public import ToMathlib.Control.Option
public import VCVio.EvalDist.ProbabilityNotation

/-!
# Deprecated: re-exports `PolyFun.Control.Monad.Measure.Relational.Deterministic`

This module is deprecated. It re-exports `PolyFun.Control.Monad.Measure.Relational.Deterministic`,
together with `ToMathlib.Control.Except`, `ToMathlib.Control.Option` and
`VCVio.EvalDist.ProbabilityNotation` for the `Pr{…}[…]` notation. Import those modules instead.
-/

deprecated_module
  "Import `PolyFun.Control.Monad.Measure.Relational.Deterministic` and this module's \
    other imports instead."
  (since := "2026-11-10")
