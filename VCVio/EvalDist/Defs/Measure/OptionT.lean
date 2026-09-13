/-
Copyright (c) 2026 VCVio Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module
public import VCVio.EvalDist.Defs.Measure.Core
public import ToMathlib.MeasureTheory.Measure.Option

/-!
# Successful-output measure semantics for optional computations

An `OptionT` computation denotes the successful-output measure of its underlying
`Option`-valued computation. The low priority leaves an existing specialized
semantics in place when one is available.
-/

public section

open MeasureTheory

universe u v

/-- Interpret successful `OptionT` results by discarding the `none` outcome. -/
noncomputable instance (priority := 5) instEvalDistSemanticsOptionT
    {m : Type u → Type v} [EvalDistSemantics m] :
    EvalDistSemantics (OptionT m) where
  denote mx := (𝒟[mx.run]).dropNone
  apply_univ_le_one mx :=
    (Measure.dropNone_apply_univ_le _).trans (evalDist_apply_univ_le_one mx.run)
