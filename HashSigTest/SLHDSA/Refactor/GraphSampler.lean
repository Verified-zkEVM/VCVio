/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module
public import VCVio.OracleComp.QueryTracking.RandomOracle.Traversal
public import HashSig.SLHDSA.SHAKE128s.Proof.GraphFreshSampling

/-!
# Byte-oracle specializations of stateful coordinate traversal

The generic traversal recovers the five concrete byte-oracle definitions and their five
complete state/cache laws. The theorem witnesses use the generic owner at exactly the concrete
input/output types, with the same coordinate lists and hypotheses.
-/

public section

open OracleComp OracleSpec

namespace SLHDSA.SHAKE128s.GraphSamplerCompatibility

variable {Index State : Type}

/-- The byte-oracle traversal has the generic free-program definition. -/
theorem evaluate_eq_byteTraversal (input : Index → State → Bytes)
    (step : Index → State → HashOutput → State) (nodes : List Index) (state : State) :
    RandomOracleTraversal.evaluate input step nodes state =
      GraphFreshSampling.evaluate input step nodes state := by
  exact (GraphFreshSampling.evaluate_eq_traversal input step nodes state).symm

/-- Independent byte-oracle sampling retains the same entire state and cache. -/
theorem sample_eq_byteTraversal (input : Index → State → Bytes)
    (step : Index → State → HashOutput → State) (nodes : List Index) (state : State)
    (cache : QueryCache HashSpec) :
    RandomOracleTraversal.sample input step nodes state cache =
      GraphFreshSampling.sample input step nodes state cache := by
  rfl

/-- Programming a complete byte-answer table retains the same entire state and cache. -/
theorem program_eq_byteTraversal (input : Index → State → Bytes)
    (step : Index → State → HashOutput → State) (outputs : Index → HashOutput)
    (nodes : List Index) (state : State) (cache : QueryCache HashSpec) :
    RandomOracleTraversal.program input step outputs nodes state cache =
      GraphFreshSampling.program input step outputs nodes state cache := by
  rfl

/-- The namespace-separation condition has the same quantifiers over all payload states. -/
theorem separated_iff_byteTraversal (input : Index → State → Bytes) :
    RandomOracleTraversal.Separated input ↔ GraphFreshSampling.Separated input := Iff.rfl

/-- Cache freshness ranges over every possible payload state at each remaining coordinate. -/
theorem freshFor_iff_byteTraversal (input : Index → State → Bytes) (nodes : List Index)
    (cache : QueryCache HashSpec) :
    RandomOracleTraversal.FreshFor input nodes cache ↔
      GraphFreshSampling.FreshFor input nodes cache := Iff.rfl

/-- The generic full-state/cache sampling law has the exact concrete byte-oracle type. -/
theorem evaluate_eq_sample (input : Index → State → Bytes)
    (step : Index → State → HashOutput → State) (hseparated : GraphFreshSampling.Separated input)
    (nodes : List Index) (hnodup : nodes.Nodup) (state : State) (cache : QueryCache HashSpec)
    (hfresh : GraphFreshSampling.FreshFor input nodes cache) :
    (simulateQ randomOracle (GraphFreshSampling.evaluate input step nodes state)).run cache =
      GraphFreshSampling.sample input step nodes state cache := by
  simpa only [evaluate_eq_byteTraversal, sample_eq_byteTraversal] using
    RandomOracleTraversal.evaluate_eq_sample input step hseparated nodes hnodup state cache hfresh

/-- The generic table-locality law has the exact concrete byte-oracle type. -/
theorem program_congr (input : Index → State → Bytes)
    (step : Index → State → HashOutput → State) (left right : Index → HashOutput)
    (nodes : List Index) (hagrees : ∀ node ∈ nodes, left node = right node)
    (state : State) (cache : QueryCache HashSpec) :
    GraphFreshSampling.program input step left nodes state cache =
      GraphFreshSampling.program input step right nodes state cache := by
  simpa only [program_eq_byteTraversal] using
    RandomOracleTraversal.program_congr input step left right nodes hagrees state cache

variable [DecidableEq Index]

/-- The generic outside-coordinate law has the exact concrete byte-oracle type. -/
theorem program_update_outside (input : Index → State → Bytes)
    (step : Index → State → HashOutput → State) (outputs : Index → HashOutput)
    (nodes : List Index) (node : Index) (hnot : node ∉ nodes) (output : HashOutput)
    (state : State) (cache : QueryCache HashSpec) :
    GraphFreshSampling.program input step (Function.update outputs node output) nodes state cache =
      GraphFreshSampling.program input step outputs nodes state cache := by
  simpa only [program_eq_byteTraversal] using
    RandomOracleTraversal.program_update_outside
      input step outputs nodes node hnot output state cache

variable [Fintype Index]

/-- The generic full-table sampling law has the exact concrete byte-oracle type. -/
theorem evalDist_sample_eq_uniform_program (input : Index → State → Bytes)
    (step : Index → State → HashOutput → State) (nodes : List Index)
    (hnodup : nodes.Nodup) (state : State) (cache : QueryCache HashSpec) :
    GraphFreshSampling.sample input step nodes state cache =ᵈ
      ((fun outputs => GraphFreshSampling.program input step outputs nodes state cache) <$>
        ($ᵗ (Index → HashOutput) : ProbComp (Index → HashOutput))) := by
  simpa only [sample_eq_byteTraversal, program_eq_byteTraversal] using
    RandomOracleTraversal.evalDist_sample_eq_uniform_program input step nodes hnodup state cache

/-- The generic lazy-oracle full-table law has the exact concrete byte-oracle type. -/
theorem evalDist_evaluate_eq_uniform_program (input : Index → State → Bytes)
    (step : Index → State → HashOutput → State) (hseparated : GraphFreshSampling.Separated input)
    (nodes : List Index) (hnodup : nodes.Nodup) (state : State) (cache : QueryCache HashSpec)
    (hfresh : GraphFreshSampling.FreshFor input nodes cache) :
    (simulateQ randomOracle (GraphFreshSampling.evaluate input step nodes state)).run cache =ᵈ
      ((fun outputs => GraphFreshSampling.program input step outputs nodes state cache) <$>
        ($ᵗ (Index → HashOutput) : ProbComp (Index → HashOutput))) := by
  simpa only [evaluate_eq_byteTraversal, program_eq_byteTraversal] using
    RandomOracleTraversal.evalDist_evaluate_eq_uniform_program
      input step hseparated nodes hnodup state cache hfresh


end SLHDSA.SHAKE128s.GraphSamplerCompatibility

namespace SLHDSA.SHAKE128s.GraphSamplerCompatibility

variable {Index State : Type}

/-! ## Complete recursive program comparisons -/

private def historicalEvaluate (input : Index → State → Bytes)
    (step : Index → State → HashOutput → State) :
    List Index → State → OracleComp HashSpec State
  | [], state => pure state
  | node :: nodes, state => do
      let output ← liftM (HashSpec.query (input node state))
      historicalEvaluate input step nodes (step node state output)

private def historicalSample (input : Index → State → Bytes)
    (step : Index → State → HashOutput → State) :
    List Index → State → QueryCache HashSpec → ProbComp (State × QueryCache HashSpec)
  | [], state, cache => pure (state, cache)
  | node :: nodes, state, cache => do
      let output ← $ᵗ HashOutput
      historicalSample input step nodes (step node state output)
        (cache.cacheQuery (input node state) output)

private def historicalProgram (input : Index → State → Bytes)
    (step : Index → State → HashOutput → State) (outputs : Index → HashOutput) :
    List Index → State → QueryCache HashSpec → State × QueryCache HashSpec
  | [], state, cache => (state, cache)
  | node :: nodes, state, cache =>
      historicalProgram input step outputs nodes (step node state (outputs node))
        (cache.cacheQuery (input node state) (outputs node))

private theorem historical_evaluate_eq (input : Index → State → Bytes)
    (step : Index → State → HashOutput → State) (nodes : List Index) (state : State) :
    historicalEvaluate input step nodes state =
      GraphFreshSampling.evaluate input step nodes state := by
  induction nodes generalizing state with
  | nil => rfl
  | cons node nodes ih =>
      simp only [historicalEvaluate, GraphFreshSampling.evaluate, RandomOracleTraversal.evaluate]
      exact bind_congr fun output => ih (step node state output)

private theorem historical_sample_eq (input : Index → State → Bytes)
    (step : Index → State → HashOutput → State) (nodes : List Index) (state : State)
    (cache : QueryCache HashSpec) :
    historicalSample input step nodes state cache =
      GraphFreshSampling.sample input step nodes state cache := by
  induction nodes generalizing state cache with
  | nil => rfl
  | cons node nodes ih =>
      simp only [historicalSample, GraphFreshSampling.sample, RandomOracleTraversal.sample]
      exact bind_congr fun output => ih (step node state output)
        (cache.cacheQuery (input node state) output)

private theorem historical_program_eq (input : Index → State → Bytes)
    (step : Index → State → HashOutput → State) (outputs : Index → HashOutput)
    (nodes : List Index) (state : State) (cache : QueryCache HashSpec) :
    historicalProgram input step outputs nodes state cache =
      GraphFreshSampling.program input step outputs nodes state cache := by
  induction nodes generalizing state cache with
  | nil => rfl
  | cons node nodes ih =>
      exact ih (step node state (outputs node)) (cache.cacheQuery (input node state) (outputs node))

end SLHDSA.SHAKE128s.GraphSamplerCompatibility
