/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module
public import PolyFun.Interaction.UC.ReactiveNetwork.Behavior
public import VCVio.OracleComp.EvalDist
public import VCVio.OracleComp.Constructions.SampleableType

/-!
# Runtime-derived observations of reactive networks

These experiments sample private shared setup, execute the actual token or FIFO runner,
and read the designated environment's terminal outcome. The observation distinguishes
successful return, explicit abort, and an unfinished finite prefix. The final laws are
Mathlib measures; no measurable structure on a private machine state is required.

The network and its component handlers are fixed before setup is sampled. A security
instantiation must still specify the allowed component programs, effect interfaces,
schedules, and initial distribution. These definitions do not assert computational
admissibility or a UC composition theorem.

The exact behavior adequacy theorems derive these observations from execution. Replacing
private machine states by their cofree behaviors preserves both experiments and measures.
-/

public section

namespace Interaction.UC.ReactiveRuntime

open PFunctor OracleComp ReactiveProcess ReactiveNetwork MeasureTheory

variable {Node result S : Type} {boundary : PortBoundary}
  [DecidableEq Node] (network : Network Node boundary result)
  (impl : (id : Node) → Handler (StateT S ProbComp) (network.effect id))
  (setup : ProbComp S)

/-- Sample setup, execute token passing, and read the actual environment's terminal outcome. -/
@[expose] def tokenExperiment (fuel : ℕ) : ProbComp (Option (Outcome result)) := do
  let service ← setup
  let finalState ← runToken impl fuel (initial network service)
  pure (outcome network.environment finalState)

/-- Sample setup, execute the FIFO schedule, and read the actual environment's terminal outcome. -/
@[expose] def fifoExperiment (schedule : List (Activation Node)) :
    ProbComp (Option (Outcome result)) := do
  let service ← setup
  let finalState ← runFIFO impl schedule (initial network service)
  pure (outcome network.environment finalState)

/-- Passing to exact cofree behavior preserves the token experiment. -/
theorem tokenExperiment_behavior (fuel : ℕ) :
    tokenExperiment network.behavior impl setup fuel = tokenExperiment network impl setup fuel := by
  simp only [tokenExperiment, initial_behavior, runToken_behavior, bind_map_left]
  congr 1
  funext service
  congr 1
  funext finalState
  rw [show network.behavior.environment = network.environment from rfl, outcome_behavior]

/-- Passing to exact cofree behavior preserves the FIFO experiment. -/
theorem fifoExperiment_behavior (schedule : List (Activation Node)) :
    fifoExperiment network.behavior impl setup schedule =
      fifoExperiment network impl setup schedule := by
  simp only [fifoExperiment, initial_behavior, runFIFO_behavior, bind_map_left]
  congr 1
  funext service
  congr 1
  funext finalState
  rw [show network.behavior.environment = network.environment from rfl, outcome_behavior]

variable [MeasurableSpace (Option (Outcome result))] [EvalDistSemantics ProbComp]

/-- The measure of terminal token observations at a finite execution horizon. -/
noncomputable def tokenLaw (fuel : ℕ) : Measure (Option (Outcome result)) :=
  𝒟[tokenExperiment network impl setup fuel]

/-- The measure of terminal FIFO observations after a specified finite schedule. -/
noncomputable def fifoLaw (schedule : List (Activation Node)) : Measure (Option (Outcome result)) :=
  𝒟[fifoExperiment network impl setup schedule]

/-- The token law is the measure denoted by the actual execution experiment. -/
theorem tokenLaw_eq_evalDist (fuel : ℕ) :
    tokenLaw network impl setup fuel = 𝒟[tokenExperiment network impl setup fuel] := by rfl

/-- The FIFO law is the measure denoted by the actual execution experiment. -/
theorem fifoLaw_eq_evalDist (schedule : List (Activation Node)) :
    fifoLaw network impl setup schedule = 𝒟[fifoExperiment network impl setup schedule] := by rfl

/-- The cofree behavior map is adequate for the actual token observation measure. -/
theorem tokenLaw_behavior (fuel : ℕ) :
    tokenLaw network.behavior impl setup fuel = tokenLaw network impl setup fuel := by
  simp only [tokenLaw, tokenExperiment_behavior]

/-- The cofree behavior map is adequate for the actual FIFO observation measure. -/
theorem fifoLaw_behavior (schedule : List (Activation Node)) :
    fifoLaw network.behavior impl setup schedule = fifoLaw network impl setup schedule := by
  simp only [fifoLaw, fifoExperiment_behavior]

end Interaction.UC.ReactiveRuntime
