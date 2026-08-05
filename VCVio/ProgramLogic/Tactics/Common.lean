/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public meta import VCVio.ProgramLogic.Tactics.Common.Backward
public meta import VCVio.ProgramLogic.Tactics.Common.Core
public meta import VCVio.ProgramLogic.Tactics.Common.Naming
public meta import VCVio.ProgramLogic.Tactics.Common.Registry
public meta import VCVio.ProgramLogic.Tactics.Common.SpecIR
public meta import VCVio.ProgramLogic.Tactics.Common.Suggestions
public meta import VCVio.ProgramLogic.Tactics.Common.WpStepDispatch
public meta import VCVio.ProgramLogic.Tactics.Common.WpStepRegistry

/-!
# Common Program-Logic Tactic Infrastructure

Aggregator import for the shared metaprogramming layer underlying the unary and relational
program-logic tactics: the core helpers, naming utilities, spec IR, rule registries, backward
reasoning, `wpStep` dispatch, and `Try this` suggestions.
-/

public meta section
