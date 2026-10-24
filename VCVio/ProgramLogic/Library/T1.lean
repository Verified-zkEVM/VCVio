/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import VCVio.ProgramLogic.Library.T1.Attr
public import VCVio.ProgramLogic.Library.T1.RunNF
public import VCVio.ProgramLogic.Library.T1.SimulateQ
public import VCVio.ProgramLogic.Library.T1.Support
public import VCVio.ProgramLogic.Library.T1.Bridges
public import VCVio.ProgramLogic.Library.T1.Lifts
public import VCVio.ProgramLogic.Library.T1.Bisim
public import VCVio.ProgramLogic.Library.T1.Upper
public import VCVio.ProgramLogic.Library.T1.UpperRanked
public import VCVio.ProgramLogic.Library.T1.QueryBound
public import VCVio.ProgramLogic.Library.T1.QueryBoundBudget
public import VCVio.ProgramLogic.Library.T1.ProbBounds

/-!
# Program-logic library, tier 1: handler-agnostic rules

Structural `simulateQ` specs and the `simulateQ_nf` normal form, a support calculus for
simulation runs, invariant lifts and frames (`QueryImpl.MonotoneState`), support and
probability bridges, bisimulation rules, the upper and budget readings (scoped), query-bound
rules and probability bounds through binds.
-/
