/-
Copyright (c) 2026 Tom Wambsgans, Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Wambsgans, Alexander Hicks
-/

module
public import VCVio.OracleComp.QueryTracking.RandomOracle.Basic
public import VCVio.OracleComp.EvalDist.Measure
import VCVio.OracleComp.QueryTracking.RandomOracle.EagerTable

/-!
# Stateful traversal of separated random-oracle coordinates

A traversal computes each query input from its current state and incorporates the full answer
into the next state. Every listed coordinate issues a query. On separated input namespaces,
a duplicate-free traversal fresh for its initial cache has the same complete state and cache
as independent full-answer sampling. For finite coordinates this also equals sampling a full
answer table and deterministically programming the same list.
-/

public section

open OracleSpec

namespace OracleComp.RandomOracleTraversal

variable {Index State Input Output : Type}

/-- Run the actual shared hash oracle while carrying the partially computed graph. -/
@[expose] def evaluate (input : Index → State → Input) (step : Index → State → Output → State) :
    List Index → State → OracleComp (Input →ₒ Output) State
  | [], state => pure state
  | node :: nodes, state => do
      let output ← liftM ((Input →ₒ Output).query (input node state))
      evaluate input step nodes (step node state output)

/-- Distinct coordinates have distinct byte inputs, whatever the payload states on either
side. -/
@[expose] def Separated (input : Index → State → Input) : Prop :=
  ∀ left right, left ≠ right → ∀ leftState rightState,
    input left leftState ≠ input right rightState

/-- No byte input of a coordinate in `nodes`, in any state, has been cached yet. -/
@[expose] def FreshFor (input : Index → State → Input) (nodes : List Index)
    (cache : QueryCache (Input →ₒ Output)) : Prop :=
  ∀ node ∈ nodes, ∀ state, cache (input node state) = none

section Programming

variable [DecidableEq Input]

/-- Deterministically program the traversal from a table of full oracle answers. -/
@[expose] def program (input : Index → State → Input) (step : Index → State → Output → State)
    (outputs : Index → Output) : List Index → State → QueryCache (Input →ₒ Output) →
      State × QueryCache (Input →ₒ Output)
  | [], state, cache => (state, cache)
  | node :: nodes, state, cache =>
      program input step outputs nodes (step node state (outputs node))
        (cache.cacheQuery (input node state) (outputs node))

/-- Programming a traversal depends only on the answers at its coordinates. -/
theorem program_congr (input : Index → State → Input)
    (step : Index → State → Output → State) (left right : Index → Output)
    (nodes : List Index) (hagrees : ∀ node ∈ nodes, left node = right node)
    (state : State) (cache : QueryCache (Input →ₒ Output)) :
    program input step left nodes state cache = program input step right nodes state cache := by
  induction nodes generalizing state cache with
  | nil => rfl
  | cons node nodes ih =>
      simp only [program, hagrees node (by simp)]
      exact ih (fun other hother => hagrees other (by simp [hother])) _ _

variable [DecidableEq Index]

/-- Changing the answer at a coordinate outside the traversal does not change its
programming. -/
theorem program_update_outside (input : Index → State → Input)
    (step : Index → State → Output → State) (outputs : Index → Output)
    (nodes : List Index) (node : Index) (hnot : node ∉ nodes) (output : Output)
    (state : State) (cache : QueryCache (Input →ₒ Output)) :
    program input step (Function.update outputs node output) nodes state cache =
      program input step outputs nodes state cache := by
  apply program_congr
  intro other hother
  apply Function.update_of_ne
  intro h
  subst other
  exact hnot hother

end Programming

section Sampling

variable [DecidableEq Input] [SampleableType Output]

/-- The corresponding experiment with an independent fresh answer at every coordinate. -/
@[expose] def sample (input : Index → State → Input) (step : Index → State → Output → State) :
    List Index → State → QueryCache (Input →ₒ Output) →
      ProbComp (State × QueryCache (Input →ₒ Output))
  | [], state, cache => pure (state, cache)
  | node :: nodes, state, cache => do
      let output ← $ᵗ Output
      sample input step nodes (step node state output)
        (cache.cacheQuery (input node state) output)

/-- On separated inputs, evaluating a duplicate-free traversal against the lazily sampled random
oracle from a fresh cache is sampling an independent answer at each coordinate. -/
theorem evaluate_eq_sample (input : Index → State → Input)
    (step : Index → State → Output → State) (hseparated : Separated input)
    (nodes : List Index) (hnodup : nodes.Nodup) (state : State)
    (cache : QueryCache (Input →ₒ Output))
    (hfresh : FreshFor input nodes cache) :
    (simulateQ randomOracle (evaluate input step nodes state)).run cache =
      sample input step nodes state cache := by
  induction nodes generalizing state cache with
  | nil => simp [evaluate, sample]
  | cons node nodes ih =>
      have hnot : node ∉ nodes := (List.nodup_cons.mp hnodup).1
      have hnodes : nodes.Nodup := (List.nodup_cons.mp hnodup).2
      rw [evaluate, simulateQ_bind, StateT.run_bind, simulateQ_spec_query]
      rw [QueryImpl.withCaching_run_none _ (hfresh node (by simp) state), bind_map_left]
      change (($ᵗ Output) >>= fun output =>
        (simulateQ randomOracle
          (evaluate input step nodes (step node state output))).run
          (cache.cacheQuery (input node state) output)) = _
      unfold sample
      apply congrArg (Bind.bind ($ᵗ Output : ProbComp Output))
      funext output
      apply ih hnodes
      intro other hother otherState
      rw [QueryCache.cacheQuery_of_ne _ _
        (hseparated other node (by intro h; subst other; exact hnot hother) otherState state)]
      exact hfresh other (by simp [hother]) otherState

variable [DecidableEq Index] [Fintype Index]

/-- Sampling the traversed coordinates individually is exactly sampling one
independent complete full-output table and programming the same traversal. -/
theorem evalDist_sample_eq_uniform_program (input : Index → State → Input)
    (step : Index → State → Output → State) (nodes : List Index)
    (hnodup : nodes.Nodup) (state : State) (cache : QueryCache (Input →ₒ Output)) :
    sample input step nodes state cache =ᵈ
      ((fun outputs => program input step outputs nodes state cache) <$>
        ($ᵗ (Index → Output) : ProbComp (Index → Output))) := by
  induction nodes generalizing state cache with
  | nil =>
      exact (OracleComp.EvalDistEq.map_const _ _).symm
  | cons node nodes ih =>
      have hnot : node ∉ nodes := (List.nodup_cons.mp hnodup).1
      have hnodes : nodes.Nodup := (List.nodup_cons.mp hnodup).2
      have hstep : sample input step (node :: nodes) state cache =ᵈ (do
          let output ← $ᵗ Output
          (fun outputs => program input step outputs nodes (step node state output)
            (cache.cacheQuery (input node state) output)) <$>
              ($ᵗ (Index → Output) : ProbComp (Index → Output))) :=
        EvalDistEq.bind_right _ fun output => ih hnodes _ _
      have hprog : (do
          let output ← $ᵗ Output
          (fun outputs => program input step outputs nodes (step node state output)
            (cache.cacheQuery (input node state) output)) <$>
              ($ᵗ (Index → Output) : ProbComp (Index → Output))) = (do
          let output ← $ᵗ Output
          let outputs ← $ᵗ (Index → Output)
          pure ((fun outputs => program input step outputs (node :: nodes) state cache)
            (Function.update outputs node output))) := by
        simp only [map_eq_bind_pure_comp, Function.comp_def, program,
          Function.update_self, program_update_outside input step _ nodes node hnot]
      refine (hprog ▸ hstep).trans ?_
      let _ : MeasurableSpace Output := ⊤
      let _ : MeasurableSpace (State × QueryCache (Input →ₒ Output)) := ⊤
      refine EvalDistEq.of_evalDist_eq ?_
      rw [map_eq_bind_pure_comp]
      exact OracleComp.evalDist_uniformSample_bind_update_map (D := Index) (R := Output)
        (SampleableType.evalDist_uniformSample) (SampleableType.evalDist_uniformSample) node
        (fun outputs => program input step outputs (node :: nodes) state cache)

/-- Full state-and-cache law for a traversal in the actual shared random oracle. -/
theorem evalDist_evaluate_eq_uniform_program (input : Index → State → Input)
    (step : Index → State → Output → State) (hseparated : Separated input)
    (nodes : List Index) (hnodup : nodes.Nodup) (state : State)
    (cache : QueryCache (Input →ₒ Output))
    (hfresh : FreshFor input nodes cache) :
    (simulateQ randomOracle (evaluate input step nodes state)).run cache =ᵈ
      ((fun outputs => program input step outputs nodes state cache) <$>
        ($ᵗ (Index → Output) : ProbComp (Index → Output))) := by
  rw [evaluate_eq_sample input step hseparated nodes hnodup state cache hfresh]
  exact evalDist_sample_eq_uniform_program input step nodes hnodup state cache

end Sampling

end OracleComp.RandomOracleTraversal
