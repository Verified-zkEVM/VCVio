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

/-!
# Common Program-Logic Tactic Infrastructure

Aggregator import for the shared metaprogramming layer underlying the relational program-logic
tactics and `prrw`: the core helpers, naming utilities, spec IR, the `@[vcspec]` registry,
backward reasoning, and `Try this` suggestions.
-/

public meta section
