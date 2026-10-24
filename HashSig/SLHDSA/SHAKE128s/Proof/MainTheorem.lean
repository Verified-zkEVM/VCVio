/-
Copyright (c) 2026 Tom Wambsgans. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Wambsgans
-/

module

public import HashSig.SLHDSA.SHAKE128s.Proof.Experiment
public import Mathlib.Topology.Instances.ENNReal.Lemmas
public import HashSig.SLHDSA.SHAKE128s.Proof.WholeGameStructural
public import HashSig.SLHDSA.SHAKE128s.Proof.WarmedGame

/-!
# The cache-keeping run

The charges of this development bound events about the oracle cache, so they are stated about
the run that keeps the cache (`WholeGameStructural.instrumentedRun`), while the statement
`slhDsa_sufCma_127` is about `Security.runAll`, which discards it. This file contains the one
lemma that links the two: an event about the outcome alone has the same probability in both.
-/

public section

open OracleComp OracleSpec ENNReal

namespace SLHDSA.SHAKE128s.MainTheorem

open Security

/-! ## The game with its cache kept

`Security.runAll` is `run'`, which keeps only the value. The two runs are the same experiment,
so an event about the value alone has the same probability either way. -/

/-- **An event about the value alone does not see the cache.** The cache-keeping run is
`WholeGameStructural.instrumentedRun`; this says the projection costs nothing. -/
theorem prEvent_runAll (adversary : Adversary) (event : Outcome × Nat → Prop) :
    Pr{let x ← runAll adversary}[event x] =
      Pr{let result ← WholeGameStructural.instrumentedRun adversary}[event result.1] := by
  rw [runAll, RandomOracleModel.run, WholeGameStructural.instrumentedRun,
    show (simulateQ KeygenUniform.rom (countAllHashes (experiment adversary))).run' ∅ =
      Prod.fst <$> (simulateQ KeygenUniform.rom (countAllHashes (experiment adversary))).run ∅
      from rfl, prEvent_map]

end SLHDSA.SHAKE128s.MainTheorem
