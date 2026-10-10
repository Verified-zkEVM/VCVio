/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import VCVio.Prelude.Core
public import Mathlib.Probability.Distributions.Uniform
public import VCVio.EvalDist.Defs.Support
public import VCVio.EvalDist.Defs.Measure.Core
public import VCVio.EvalDist.Defs.Measure.Deterministic
public import VCVio.EvalDist.Defs.Measure.ExceptT
public import VCVio.EvalDist.Defs.Measure.OptionT
public import ToMathlib.MeasureTheory.Measure.Option

/-!
# Measure-valued evaluation

This module collects the measure semantics of `VCVio.EvalDist.Defs.Measure.Core` with its
instances for deterministic, optional and exceptional computations. An `EvalDistSemantics m`
interprets `m α` as a Mathlib `Measure α` with total mass at most one. Missing mass represents
failure or nontermination. In particular, the output distribution itself does not introduce an
`Option` outcome.

Measurable spaces are explicit arguments to the semantics. There is deliberately no blanket
measurable-space instance for finite types: statements give their countability and measurability
assumptions where they are used.

`LawfulPureEvalDistSemantics` records the Giry `pure` law without imposing conditions on effects.
`LawfulEvalDistSemantics` adds the bind law, keeping measurability of the continuation visible;
`evalDist_bind_of_discrete` is the usual cryptographic specialization.
-/
