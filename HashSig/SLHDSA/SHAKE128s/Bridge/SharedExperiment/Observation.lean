/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module
public import HashSig.SLHDSA.SHAKE128s.Bridge.SharedExperiment.Recorded

/-!
# Complete source observations under one cached interpretation

The full original outcome and source vector follow from the recorded program equality.
A single arbitrary cached handler and continuation retain the joint result and final cache.
-/

public section

open OracleComp OracleSpec

universe v

namespace SLHDSA.SHAKE128s.Bridge.SharedExperiment

/-- The original outcome and complete source vector agree as one free-oracle program. -/
theorem fullProgram {Output PK SK : Type} (scheme : Game.ExternalScheme Output PK SK)
    (adversary : Game.Adversary Output PK) :
    Game.experimentBySource scheme adversary =
      legacyObservation <$> canonicalExperiment scheme adversary := by
  unfold legacyObservation
  let project : Game.Outcome × Nat × Nat → Game.Outcome × SourceCounts :=
    fun result => (result.1, Game.sourceCounts result.1 result.2.1 result.2.2)
  have equality := congrArg (fun program => project <$> program)
    (recordedProgram scheme adversary)
  simpa [Game.experimentBySource, project, map_bind, Functor.map_map] using equality

/-- The same cached handler and continuation observe the full same result and final cache. -/
theorem sharedContinuation {Output PK SK Cache β : Type} {m : Type → Type v}
    [Monad m] [LawfulMonad m] (scheme : Game.ExternalScheme Output PK SK)
    (adversary : Game.Adversary Output PK)
    (handler : QueryImpl (Game.World Output) (StateT Cache m)) (initial : Cache)
    (next : (Game.Outcome × SourceCounts) × Cache → m β) :
    ((simulateQ handler (canonicalExperiment scheme adversary)).run initial >>=
      fun result => next (legacyObservation result.1, result.2)) =
      ((simulateQ handler (Game.experimentBySource scheme adversary)).run initial >>= next) := by
  have equality := congrArg (fun program =>
    ((simulateQ handler program).run initial >>= next)) (fullProgram scheme adversary)
  simpa only [simulateQ_map, StateT.run_map, bind_map_left] using equality.symm

end SLHDSA.SHAKE128s.Bridge.SharedExperiment
