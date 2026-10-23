/-
Copyright (c) 2026 Tom Wambsgans. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Wambsgans
-/

module

public import HashSig.SLHDSA.SHAKE128s.Proof.StructuralTerm
public import HashSig.SLHDSA.SHAKE128s.Proof.GrowthBudget
public import HashSig.SLHDSA.SHAKE128s.Proof.CombinedCharge
public import HashSig.SLHDSA.SHAKE128s.Proof.GrowthCharge
public import HashSig.SLHDSA.SHAKE128s.Proof.Experiment

/-!
# The whole game, instrumented

`instrumentedRun` runs the experiment under the all-queries counter `countAllHashes`, keeping the
cache and the count of every hash call, so a statement about the whole game's work reads off this
one run. `mem_support_runAll_of_mem_support` ties its support back to `runAll`.
-/

@[expose] public section

open OracleComp OracleSpec ENNReal

namespace SlhDsaSecurity.WholeGameStructural

open Security CanonicalGraph

/-- The instrumented run, before the count is projected away. -/
noncomputable def instrumentedRun (adversary : Adversary) :
    ProbComp ((Outcome × Nat) × QueryCache HashSpec) :=
  (simulateQ KeygenUniform.rom (countAllHashes (experiment adversary))).run ∅

/-- Every outcome of the instrumented run, with the count projected away, is a possible outcome
of `runAll`. -/
theorem mem_support_runAll_of_mem_support {adversary : Adversary}
    {result : (Outcome × Nat) × QueryCache HashSpec}
    (hmem : result ∈ support (instrumentedRun adversary)) :
    result.1 ∈ support (runAll adversary) := by
  unfold runAll RandomOracleModel.run
  rw [StateT.run'_eq, support_map]
  exact ⟨result, hmem, rfl⟩

end SlhDsaSecurity.WholeGameStructural
