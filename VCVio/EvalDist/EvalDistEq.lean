/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.Control.Monad.Measure.EvalDistEq
public import VCVio.EvalDist.ProbabilityNotation

/-!
# Equality-in-distribution notation

`EvalDistEq` and its laws live in PolyFun's `PolyFun.Control.Monad.Measure.EvalDistEq`.
This module adds VCVio's notation `mx =ᵈ my` for `EvalDistEq mx my`.
-/

public section

@[inherit_doc] infix:50 " =ᵈ " => EvalDistEq
