/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module
public import PolyFun.Interaction.UC.ReactiveNetwork.Behavior
public import PolyFun.Interaction.UC.ReactiveNetwork.Serial
public import PolyFun.Interaction.UC.ReactiveNetwork.Transport
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

/-- Execute the serial FIFO policy, charging one local and one delivery activation per round.
Only the public control holder selects the next local activation. -/
@[expose] def serialExperiment (rounds : ℕ) : ProbComp (Option (Outcome result)) := do
  let service ← setup
  let finalState ← runSerial impl rounds (initial network service)
  pure (outcome network.environment finalState)

/-- The serial FIFO policy has the same terminal observation as token passing at the
corresponding round count, including all unfinished prefixes. -/
theorem serialExperiment_eq_tokenExperiment (rounds : ℕ) :
    serialExperiment network impl setup rounds = tokenExperiment network impl setup rounds := by
  simp only [serialExperiment, tokenExperiment, ← map_eq_pure_bind]
  apply bind_congr
  intro service
  exact outcome_runSerial impl network.environment rounds (initial network service) rfl

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

/-- Renaming nodes preserves the token experiment when handlers and control move together. -/
theorem tokenExperiment_reindex {Node' : Type} [DecidableEq Node'] (e : Node' ≃ Node)
    (fuel : ℕ) :
    tokenExperiment (network.reindex e) (fun node => impl (e node)) setup fuel =
      tokenExperiment network impl setup fuel := by
  simp only [tokenExperiment, initial_reindex, runToken_reindex, bind_map_left]
  congr 1
  funext service
  congr 1
  funext state
  rw [Network.reindex_environment]
  simpa only [Equiv.apply_symm_apply] using
    congrArg (pure (f := ProbComp)) (outcome_reindex e (e.symm network.environment) state)

/-- FIFO relabeling preserves observations when delivery positions and node activations are
transported together. -/
theorem fifoExperiment_reindex {Node' : Type} [DecidableEq Node'] (e : Node' ≃ Node)
    (schedule : List (Activation Node)) :
    fifoExperiment (network.reindex e) (fun node => impl (e node)) setup
        (schedule.map (Activation.reindex e)) =
      fifoExperiment network impl setup schedule := by
  simp only [fifoExperiment, initial_reindex, runFIFO_reindex, bind_map_left]
  congr 1
  funext service
  congr 1
  funext state
  rw [Network.reindex_environment]
  simpa only [Equiv.apply_symm_apply] using
    congrArg (pure (f := ProbComp)) (outcome_reindex e (e.symm network.environment) state)

/-- Equal network data has the same token experiment with the transported handlers. -/
theorem tokenExperiment_castNetwork {network' : Network Node boundary result}
    (h : network = network') (fuel : ℕ) :
    tokenExperiment network' (castHandlers h impl) setup fuel =
      tokenExperiment network impl setup fuel := by
  cases h
  rw [castHandlers_rfl]

/-- Equal network data has the same FIFO experiment with the transported handlers. -/
theorem fifoExperiment_castNetwork {network' : Network Node boundary result}
    (h : network = network') (schedule : List (Activation Node)) :
    fifoExperiment network' (castHandlers h impl) setup schedule =
      fifoExperiment network impl setup schedule := by
  cases h
  rw [castHandlers_rfl]

/-- A proved graph factorization preserves the actual token experiment and private setup. -/
theorem tokenExperiment_factorization {Node' : Type} [DecidableEq Node']
    {network' : Network Node' boundary result} (e : Node' ≃ Node)
    (h : network.reindex e = network') (fuel : ℕ) :
    tokenExperiment network' (castHandlers h (fun node => impl (e node))) setup fuel =
      tokenExperiment network impl setup fuel :=
  (tokenExperiment_castNetwork _ _ setup h fuel).trans
    (tokenExperiment_reindex network impl setup e fuel)

/-- A proved graph factorization preserves the actual FIFO experiment with its schedule
transported, including the order of effects and delivery activations. -/
theorem fifoExperiment_factorization {Node' : Type} [DecidableEq Node']
    {network' : Network Node' boundary result} (e : Node' ≃ Node)
    (h : network.reindex e = network') (schedule : List (Activation Node)) :
    fifoExperiment network' (castHandlers h (fun node => impl (e node))) setup
        (schedule.map (Activation.reindex e)) =
      fifoExperiment network impl setup schedule :=
  (fifoExperiment_castNetwork _ _ setup h _).trans
    (fifoExperiment_reindex network impl setup e schedule)

variable [MeasurableSpace (Option (Outcome result))]

/-- The measure of terminal token observations at a finite execution horizon. -/
noncomputable def tokenLaw (fuel : ℕ) : Measure (Option (Outcome result)) :=
  𝒟[tokenExperiment network impl setup fuel]

/-- The measure of terminal FIFO observations after a specified finite schedule. -/
noncomputable def fifoLaw (schedule : List (Activation Node)) : Measure (Option (Outcome result)) :=
  𝒟[fifoExperiment network impl setup schedule]

/-- The measure of actual environment outcomes under the serial FIFO policy. -/
noncomputable def serialLaw (rounds : ℕ) : Measure (Option (Outcome result)) :=
  𝒟[serialExperiment network impl setup rounds]

/-- Token and serial FIFO observations agree at every corresponding finite prefix. -/
theorem serialLaw_eq_tokenLaw (rounds : ℕ) :
    serialLaw network impl setup rounds = tokenLaw network impl setup rounds := by
  simp only [serialLaw, tokenLaw, serialExperiment_eq_tokenExperiment]

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

/-- Node relabeling preserves the actual finite token observation measure. -/
theorem tokenLaw_reindex {Node' : Type} [DecidableEq Node'] (e : Node' ≃ Node) (fuel : ℕ) :
    tokenLaw (network.reindex e) (fun node => impl (e node)) setup fuel =
      tokenLaw network impl setup fuel := by
  simp only [tokenLaw, tokenExperiment_reindex]

/-- Node relabeling preserves FIFO observation measures with the transported schedule. -/
theorem fifoLaw_reindex {Node' : Type} [DecidableEq Node'] (e : Node' ≃ Node)
    (schedule : List (Activation Node)) :
    fifoLaw (network.reindex e) (fun node => impl (e node)) setup
        (schedule.map (Activation.reindex e)) = fifoLaw network impl setup schedule := by
  simp only [fifoLaw, fifoExperiment_reindex]

/-- Runtime graph factorization preserves the finite token observation measure. -/
theorem tokenLaw_factorization {Node' : Type} [DecidableEq Node']
    {network' : Network Node' boundary result} (e : Node' ≃ Node)
    (h : network.reindex e = network') (fuel : ℕ) :
    tokenLaw network' (castHandlers h (fun node => impl (e node))) setup fuel =
      tokenLaw network impl setup fuel := by
  simp only [tokenLaw, tokenExperiment_factorization network impl setup e h]

/-- Runtime graph factorization preserves finite FIFO observation measures with the
corresponding schedule. -/
theorem fifoLaw_factorization {Node' : Type} [DecidableEq Node']
    {network' : Network Node' boundary result} (e : Node' ≃ Node)
    (h : network.reindex e = network') (schedule : List (Activation Node)) :
    fifoLaw network' (castHandlers h (fun node => impl (e node))) setup
        (schedule.map (Activation.reindex e)) = fifoLaw network impl setup schedule := by
  simp only [fifoLaw, fifoExperiment_factorization network impl setup e h]

end Interaction.UC.ReactiveRuntime
