/-
Copyright (c) 2026 Tom Wambsgans. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Wambsgans
-/

module

public import VCVio.OracleComp.QueryTracking.RandomOracle.Simulation
public import VCVio.OracleComp.QueryTracking.WriterCost

/-!
# The classical random-oracle model

All parties share one lazily sampled hash oracle. Each hash call costs one unit, including
repeated inputs; private uniform sampling is free. Each experiment starts with an empty cache.
-/

public section

open OracleComp OracleSpec

namespace SlhDsaSecurity.RandomOracleModel

variable (Input Output : Type) [DecidableEq Input] [SampleableType Output]

/-- The hash oracle `H : Input → Output`. -/
abbrev HashSpec : OracleSpec Input := Input →ₒ Output

/-- Private uniform sampling and the shared hash oracle. -/
abbrev World := unifSpec + HashSpec Input Output

/-- Forward uniform sampling; answer a fresh hash input by a uniform output and cache it, and a
repeated input from the cache. -/
@[expose] noncomputable def impl :
    QueryImpl (World Input Output) (StateT (QueryCache (HashSpec Input Output)) ProbComp) :=
  unifFwdImpl (HashSpec Input Output) +
    (randomOracle : QueryImpl (HashSpec Input Output)
      (StateT (QueryCache (HashSpec Input Output)) ProbComp))

/-- One unit per hash call, including repeated inputs; nothing per uniform sample. -/
@[expose] def hashCost : (World Input Output).Domain → ℕ
  | .inl _ => 0
  | .inr _ => 1

variable {Input Output}

/-- Run a computation of the random-oracle world from an empty cache. -/
@[expose] noncomputable def run {α : Type} (computation : OracleComp (World Input Output) α) :
    ProbComp α :=
  (simulateQ (impl Input Output) computation).run' ∅

end SlhDsaSecurity.RandomOracleModel
