/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import VCVio.EvalDist.Defs.Measure.OptionT -- deprecated_module: ignore

/-!
# Importing the deprecated `VCVio.EvalDist.Defs.Measure.OptionT`

The only import is the deprecated `VCVio.EvalDist.Defs.Measure.OptionT`. The example checks that it
provides the `OptionT` measure semantics and the `𝒟[…]` notation, which its importers receive
through `VCVio.EvalDist.Defs.Measure.Failure`, itself a deprecated module. The import suppresses its
deprecation warning, so the test library still builds without warnings.
-/

public section

namespace VCVioTest.DeprecatedImports.OptionT

example {m : Type → Type} [EvalDistSemantics m] {α : Type} [MeasurableSpace α]
    (mx : OptionT m α) : 𝒟[mx] = 𝒟[mx.run].comap some :=
  OptionT.evalDist_eq_comap_some mx

end VCVioTest.DeprecatedImports.OptionT
