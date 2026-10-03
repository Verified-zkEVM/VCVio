/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public meta import VCVio.ProgramLogic.Tactics.Handler
public meta import VCVio.EvalDist.MeasureTVDist.Positivity
public meta import VCVio.ProgramLogic.Tactics.Unary
public meta import VCVio.ProgramLogic.Tactics.Relational
public meta import VCVio.ProgramLogic.Tactics.PrVCGen

/-!
# VCGen Tactics for Probabilistic Program Logic

This is the canonical user-facing umbrella import for tactic-based program-logic proofs.

- `VCVio.ProgramLogic.Tactics.PrVCGen` contains `prvcgen`, which restates a goal about one
  program (a bound, probability one, a possible or necessary outcome, or a core triple) as a
  triple of the reading it belongs to (the necessary, possible, lower or upper reading) and
  runs core's `vcgen` in that reading. Rules are core `@[spec]` theorems.
- `VCVio.ProgramLogic.Tactics.Unary` contains `prrw`, which rewrites an equality between the
  probabilities of two programs by bind swaps (`prrw`, `prrw under n`), shared prefixes
  (`prrw congr`, `prrw congr'`) and a bounded search over both (`prrw normalize`), together with
  `expect_arith` and `by_hoare`.
- `VCVio.ProgramLogic.Tactics.Relational` contains relational proof-mode tactics such as
  `rvcstep`, `rvcgen`, `by_equiv`, `rel_dist`, `game_trans`, `by_dist`, and `by_upto`;
  `@[vcspec]` registers a relational rule for their bounded lookup.

An equation between an expectation of one program and its value is proved by
`simp only [expect_norm, expect_eval]`. To trace the choices of the relational tactics, enable
`set_option vcvio.vcgen.traceSteps true`.

For normal proof work, import `VCVio.ProgramLogic.Tactics` and treat it as the default
interactive tactic surface.
-/

public meta section
