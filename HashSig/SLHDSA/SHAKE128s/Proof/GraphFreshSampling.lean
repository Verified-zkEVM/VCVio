/-
Copyright (c) 2026 Tom Wambsgans. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Wambsgans
-/

module

public import HashSig.SLHDSA.SHAKE128s.Proof.Experiment
public import VCVio.OracleComp.QueryTracking.RandomOracle.Traversal

/-!
# Sampling distinct structural coordinates in the shared byte oracle

Each coordinate has a byte-input namespace disjoint from all other coordinates,
for every possible payload state. Thus a traversal without repeated coordinates
samples independent full 240-bit answers. The result below preserves both the
computed state and the entire programmed byte-input cache.
-/

public section

open OracleComp OracleSpec

namespace SLHDSA.SHAKE128s.GraphFreshSampling

variable {Index State : Type}

/-- Run the actual shared hash oracle while carrying the partially computed graph. -/
@[expose] def evaluate (input : Index → State → Bytes) (step : Index → State → HashOutput → State) :
    List Index → State → OracleComp HashSpec State :=
  RandomOracleTraversal.evaluate input step

/-- The corresponding experiment with an independent fresh answer at every coordinate. -/
@[expose] def sample (input : Index → State → Bytes) (step : Index → State → HashOutput → State) :
    List Index → State → QueryCache HashSpec → ProbComp (State × QueryCache HashSpec) :=
  RandomOracleTraversal.sample input step

/-- Deterministically program the traversal from a table of full oracle answers. -/
@[expose] def program (input : Index → State → Bytes) (step : Index → State → HashOutput → State)
    (outputs : Index → HashOutput) : List Index → State → QueryCache HashSpec →
      State × QueryCache HashSpec :=
  RandomOracleTraversal.program input step outputs

/-- Distinct coordinates have distinct byte inputs, whatever the payload states on either
side. -/
@[expose] def Separated (input : Index → State → Bytes) : Prop :=
  RandomOracleTraversal.Separated input

/-- No byte input of a coordinate in `nodes`, in any state, has been cached yet. -/
@[expose] def FreshFor (input : Index → State → Bytes) (nodes : List Index)
    (cache : QueryCache HashSpec) : Prop :=
  RandomOracleTraversal.FreshFor input nodes cache

/-- On separated inputs, evaluating a duplicate-free traversal against the lazily sampled random
oracle from a fresh cache is sampling an independent answer at each coordinate. -/
theorem evaluate_eq_sample (input : Index → State → Bytes)
    (step : Index → State → HashOutput → State) (hseparated : Separated input)
    (nodes : List Index) (hnodup : nodes.Nodup) (state : State) (cache : QueryCache HashSpec)
    (hfresh : FreshFor input nodes cache) :
    (simulateQ randomOracle (evaluate input step nodes state)).run cache =
      sample input step nodes state cache :=
  RandomOracleTraversal.evaluate_eq_sample input step hseparated nodes hnodup state cache hfresh

/-- Programming a traversal depends only on the answers at its coordinates. -/
theorem program_congr (input : Index → State → Bytes)
    (step : Index → State → HashOutput → State) (left right : Index → HashOutput)
    (nodes : List Index) (hagrees : ∀ node ∈ nodes, left node = right node)
    (state : State) (cache : QueryCache HashSpec) :
    program input step left nodes state cache = program input step right nodes state cache :=
  RandomOracleTraversal.program_congr input step left right nodes hagrees state cache

variable [DecidableEq Index]

/-- Changing the answer at a coordinate outside the traversal does not change its
programming. -/
theorem program_update_outside (input : Index → State → Bytes)
    (step : Index → State → HashOutput → State) (outputs : Index → HashOutput)
    (nodes : List Index) (node : Index) (hnot : node ∉ nodes) (output : HashOutput)
    (state : State) (cache : QueryCache HashSpec) :
    program input step (Function.update outputs node output) nodes state cache =
      program input step outputs nodes state cache :=
  RandomOracleTraversal.program_update_outside input step outputs nodes node hnot output state cache

variable [Fintype Index]

/-- Sampling the traversed coordinates individually is exactly sampling one
independent complete full-output table and programming the same traversal. -/
theorem evalDist_sample_eq_uniform_program (input : Index → State → Bytes)
    (step : Index → State → HashOutput → State) (nodes : List Index)
    (hnodup : nodes.Nodup) (state : State) (cache : QueryCache HashSpec) :
    sample input step nodes state cache =ᵈ
      ((fun outputs => program input step outputs nodes state cache) <$>
        ($ᵗ (Index → HashOutput) : ProbComp (Index → HashOutput))) :=
  RandomOracleTraversal.evalDist_sample_eq_uniform_program input step nodes hnodup state cache

/-- Full state-and-cache law for a traversal in the actual shared random oracle. -/
theorem evalDist_evaluate_eq_uniform_program (input : Index → State → Bytes)
    (step : Index → State → HashOutput → State) (hseparated : Separated input)
    (nodes : List Index) (hnodup : nodes.Nodup) (state : State) (cache : QueryCache HashSpec)
    (hfresh : FreshFor input nodes cache) :
    (simulateQ randomOracle (evaluate input step nodes state)).run cache =ᵈ
      ((fun outputs => program input step outputs nodes state cache) <$>
        ($ᵗ (Index → HashOutput) : ProbComp (Index → HashOutput))) :=
  RandomOracleTraversal.evalDist_evaluate_eq_uniform_program
    input step hseparated nodes hnodup state cache hfresh

end SLHDSA.SHAKE128s.GraphFreshSampling

namespace SLHDSA.SHAKE128s.GraphFreshSampling

/-- The byte-oracle evaluator is the generic traversal at the full byte-answer types. -/
theorem evaluate_eq_traversal
    {Index State : Type}
    (input : Index → State → Bytes)
    (step : Index → State → HashOutput → State)
    (nodes : List Index) (state : State) :
    GraphFreshSampling.evaluate input step nodes state =
      OracleComp.RandomOracleTraversal.evaluate input step nodes state :=
  rfl

/-- The byte-oracle programmer is the generic traversal with the same full state and cache. -/
theorem program_eq_traversal {Index State : Type} (input : Index → State → Bytes)
    (step : Index → State → HashOutput → State) (outputs : Index → HashOutput)
    (nodes : List Index) (state : State) (cache : QueryCache HashSpec) :
    GraphFreshSampling.program input step outputs nodes state cache =
      OracleComp.RandomOracleTraversal.program input step outputs nodes state cache :=
  rfl

end SLHDSA.SHAKE128s.GraphFreshSampling
