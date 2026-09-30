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

- `VCVio.ProgramLogic.Tactics.Unary` contains unary / quantitative tactics such as
  `pvcstep`, `pvcgen`, `exp_norm`, and `by_hoare`.
- `VCVio.ProgramLogic.Tactics.Relational` contains relational proof-mode tactics such as
  `rvcstep`, `rvcgen`, `by_equiv`, `rel_dist`, `game_trans`, `by_dist`, and `by_upto`.
- `VCVio.ProgramLogic.Tactics.PrVCGen` contains `prvcgen`, which states an event goal as a core
  triple of the reading it belongs to (structural, angelic, expectation lower or upper bound) and
  runs core's `vcgen` in that reading.

For probability equalities, use `pvcstep` directly:
- plain `pvcstep` keeps the heuristic swap/congruence dispatcher;
- `pvcstep rw` / `pvcstep rw under n` expose explicit bind-swap rewrites;
- `pvcstep rw congr` / `pvcstep rw congr'` expose one shared bind explicitly.

For unary theorem-driven steps:
- `pvcstep with thm` forces one explicit unary theorem/assumption step;
- `@[vcspec]` registers an explicit opt-in theorem for bounded lookup by
  `pvcstep` / `pvcgen` / `rvcstep` / `rvcgen`.

For tactic-choice debugging, enable `set_option vcvio.vcgen.traceSteps true`.

For normal proof work, import `VCVio.ProgramLogic.Tactics` and treat it as the default
interactive tactic surface.
-/

public meta section
