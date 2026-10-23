/-
Copyright (c) 2026 Tom Wambsgans. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Wambsgans
-/

module

public import HashSig.SLHDSA.SHAKE128s.Proof.Experiment
public import VCVio.OracleComp.QueryTracking.RandomOracle.DeferredSampling
import VCVio.OracleComp.QueryTracking.RandomOracle.EagerTable

/-!
# Sampling distinct structural coordinates in the shared byte oracle

Each coordinate has a byte-input namespace disjoint from all other coordinates,
for every possible payload state. Thus a traversal without repeated coordinates
samples independent full 240-bit answers. The result below preserves both the
computed state and the entire programmed byte-input cache.
-/

@[expose] public section

open OracleComp OracleSpec

namespace SlhDsaSecurity.GraphFreshSampling

variable {Index State : Type} [DecidableEq Index]

/-- Run the actual shared hash oracle while carrying the partially computed graph. -/
def evaluate (input : Index → State → Bytes) (step : Index → State → HashOutput → State) :
    List Index → State → OracleComp HashSpec State
  | [], state => pure state
  | node :: nodes, state => do
      let output ← liftM (HashSpec.query (input node state))
      evaluate input step nodes (step node state output)

/-- The corresponding experiment with an independent fresh answer at every coordinate. -/
def sample (input : Index → State → Bytes) (step : Index → State → HashOutput → State) :
    List Index → State → QueryCache HashSpec → ProbComp (State × QueryCache HashSpec)
  | [], state, cache => pure (state, cache)
  | node :: nodes, state, cache => do
      let output ← $ᵗ HashOutput
      sample input step nodes (step node state output)
        (cache.cacheQuery (input node state) output)

/-- Deterministically program the traversal from a table of full oracle answers. -/
def program (input : Index → State → Bytes) (step : Index → State → HashOutput → State)
    (outputs : Index → HashOutput) : List Index → State → QueryCache HashSpec →
      State × QueryCache HashSpec
  | [], state, cache => (state, cache)
  | node :: nodes, state, cache =>
      program input step outputs nodes (step node state (outputs node))
        (cache.cacheQuery (input node state) (outputs node))

/-- Byte-input separation is uniform over the payload states on both sides. -/
def Separated (input : Index → State → Bytes) : Prop :=
  ∀ left right, left ≠ right → ∀ leftState rightState,
    input left leftState ≠ input right rightState

def FreshFor (input : Index → State → Bytes) (nodes : List Index)
    (cache : QueryCache HashSpec) : Prop :=
  ∀ node ∈ nodes, ∀ state, cache (input node state) = none

omit [DecidableEq Index] in
theorem evaluate_eq_sample (input : Index → State → Bytes)
    (step : Index → State → HashOutput → State) (hseparated : Separated input)
    (nodes : List Index) (hnodup : nodes.Nodup) (state : State) (cache : QueryCache HashSpec)
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
      change (($ᵗ HashOutput) >>= fun output =>
        (simulateQ randomOracle (evaluate input step nodes (step node state output))).run
          (cache.cacheQuery (input node state) output)) = _
      unfold sample
      apply congrArg (Bind.bind ($ᵗ HashOutput : ProbComp HashOutput))
      funext output
      apply ih hnodes
      intro other hother otherState
      rw [QueryCache.cacheQuery_of_ne _ _
        (hseparated other node (by intro h; subst other; exact hnot hother) otherState state)]
      exact hfresh other (by simp [hother]) otherState

omit [DecidableEq Index] in
theorem program_congr (input : Index → State → Bytes)
    (step : Index → State → HashOutput → State) (left right : Index → HashOutput)
    (nodes : List Index) (hagrees : ∀ node ∈ nodes, left node = right node)
    (state : State) (cache : QueryCache HashSpec) :
    program input step left nodes state cache = program input step right nodes state cache := by
  induction nodes generalizing state cache with
  | nil => rfl
  | cons node nodes ih =>
      simp only [program, hagrees node (by simp)]
      exact ih (fun other hother => hagrees other (by simp [hother])) _ _

theorem program_update_outside (input : Index → State → Bytes)
    (step : Index → State → HashOutput → State) (outputs : Index → HashOutput)
    (nodes : List Index) (node : Index) (hnot : node ∉ nodes) (output : HashOutput)
    (state : State) (cache : QueryCache HashSpec) :
    program input step (Function.update outputs node output) nodes state cache =
      program input step outputs nodes state cache := by
  apply program_congr
  intro other hother
  apply Function.update_of_ne
  intro h
  subst other
  exact hnot hother

variable [Fintype Index]

/-- Sampling the traversed coordinates individually is exactly sampling one
independent complete full-output table and programming the same traversal. -/
theorem evalDist_sample_eq_uniform_program (input : Index → State → Bytes)
    (step : Index → State → HashOutput → State) (nodes : List Index)
    (hnodup : nodes.Nodup) (state : State) (cache : QueryCache HashSpec) :
    sample input step nodes state cache =ᵈ
      ((fun outputs => program input step outputs nodes state cache) <$>
        ($ᵗ (Index → HashOutput) : ProbComp (Index → HashOutput))) := by
  induction nodes generalizing state cache with
  | nil =>
      exact (OracleComp.EvalDistEq.map_const _ _).symm
  | cons node nodes ih =>
      have hnot : node ∉ nodes := (List.nodup_cons.mp hnodup).1
      have hnodes : nodes.Nodup := (List.nodup_cons.mp hnodup).2
      have hstep : sample input step (node :: nodes) state cache =ᵈ (do
          let output ← $ᵗ HashOutput
          (fun outputs => program input step outputs nodes (step node state output)
            (cache.cacheQuery (input node state) output)) <$>
              ($ᵗ (Index → HashOutput) : ProbComp (Index → HashOutput))) :=
        EvalDistEq.bind_right _ fun output => ih hnodes _ _
      have hprog : (do
          let output ← $ᵗ HashOutput
          (fun outputs => program input step outputs nodes (step node state output)
            (cache.cacheQuery (input node state) output)) <$>
              ($ᵗ (Index → HashOutput) : ProbComp (Index → HashOutput))) = (do
          let output ← $ᵗ HashOutput
          let outputs ← $ᵗ (Index → HashOutput)
          pure ((fun outputs => program input step outputs (node :: nodes) state cache)
            (Function.update outputs node output))) := by
        simp only [map_eq_bind_pure_comp, Function.comp_def, program,
          Function.update_self, program_update_outside input step _ nodes node hnot]
      refine (hprog ▸ hstep).trans ?_
      let _ : MeasurableSpace HashOutput := ⊤
      let _ : MeasurableSpace (State × QueryCache HashSpec) := ⊤
      refine EvalDistEq.of_evalDist_eq ?_
      rw [map_eq_bind_pure_comp]
      exact OracleComp.evalDist_uniformSample_bind_update_map (D := Index) (R := HashOutput)
        (SampleableType.evalDist_uniformSample) (SampleableType.evalDist_uniformSample) node
        (fun outputs => program input step outputs (node :: nodes) state cache)

/-- Full state-and-cache law for a traversal in the actual shared random oracle. -/
theorem evalDist_evaluate_eq_uniform_program (input : Index → State → Bytes)
    (step : Index → State → HashOutput → State) (hseparated : Separated input)
    (nodes : List Index) (hnodup : nodes.Nodup) (state : State) (cache : QueryCache HashSpec)
    (hfresh : FreshFor input nodes cache) :
    (simulateQ randomOracle (evaluate input step nodes state)).run cache =ᵈ
      ((fun outputs => program input step outputs nodes state cache) <$>
        ($ᵗ (Index → HashOutput) : ProbComp (Index → HashOutput))) := by
  rw [evaluate_eq_sample input step hseparated nodes hnodup state cache hfresh]
  exact evalDist_sample_eq_uniform_program input step nodes hnodup state cache

end SlhDsaSecurity.GraphFreshSampling
