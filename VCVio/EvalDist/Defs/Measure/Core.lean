/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module
public import PolyFun.Control.Monad.Measure
public import ToCslib.MeasureTheory.Measure.Prop
public import ToMathlib.MeasureTheory.Measure.Bool
public import Mathlib.MeasureTheory.Measure.Prod
public import VCVio.Prelude.Core

/-!
# Evaluation-measure notation

`EvalDistSemantics`, `evalDist` and their composition laws live in PolyFun's
`PolyFun.Control.Monad.Measure`. This module adds VCVio's notation `𝒟[mx]` for
`evalDist mx` and registers the Dirac law in the `game_rule` simp set.
-/

public section

/-- Evaluation-measure notation. -/
notation "𝒟[" mx "]" => evalDist mx

attribute [game_rule] evalDist_pure
