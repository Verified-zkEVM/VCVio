/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import VCVio.Interaction.UC.ReactiveRuntime
public import VCVio.EvalDist.Monad.Measure

/-!
# Local joint-kernel replacement for reactive execution

Equality of the joint response and retained service-state laws lifts to every token or FIFO
prefix and every measurable observation of its complete residual state. Matching only the
immediate response distribution is insufficient when subsequent calls can read the service state.
The measurable structures and discrete interfaces are explicit; no global discrete instance is
installed for arbitrary network configurations.
-/

public section

namespace Interaction.UC.ReactiveKernel

open PFunctor ReactiveProcess ReactiveNetwork OracleComp MeasureTheory

variable {Node result S : Type} {boundary : PortBoundary}
  [DecidableEq Node] {network : Network Node boundary result}
  [MeasurableSpace S]
  [∀ node, ∀ operation : (network.effect node).A,
    MeasurableSpace ((network.effect node).B operation)]
  [∀ node, ∀ operation : (network.effect node).A,
    DiscreteMeasurableSpace ((network.effect node).B operation × S)]

/-- Every local call preserves the complete joint law of its response and retained service state. -/
@[expose] def JointHandlerLawEq
    (left right : (node : Node) → Handler (StateT S ProbComp) (network.effect node)) : Prop :=
  ∀ node operation state, 𝒟[(left node operation).run state] = 𝒟[(right node operation).run state]

variable [MeasurableSpace (State network S)]

attribute [local implicit_reducible] signature Response

/-- Joint local-kernel equality preserves one actual network activation under either policy. -/
theorem activate_congr
    {left right : (node : Node) → Handler (StateT S ProbComp) (network.effect node)}
    (h : JointHandlerLawEq left right) (discipline : Discipline) (node : Node)
    (state : State network S) :
    𝒟[activate left discipline node state] = 𝒟[activate right discipline node state] := by
  rcases hv : (network.component node).view (state.localState node) with value | ⟨action, next⟩
  · simp only [activate, hv]
  · cases action with
    | effect operation =>
      simp only [activate, hv, bind_pure_comp]
      rw [evalDist_map_of_discrete, evalDist_map_of_discrete, h]
    | receive => simp only [activate, hv]
    | send packet => simp only [activate, hv]
    | tick => simp only [activate, hv]
    | yield => simp only [activate, hv]

/-- One FIFO schedule action preserves its joint residual-state law. -/
theorem fifoStep_congr
    {left right : (node : Node) → Handler (StateT S ProbComp) (network.effect node)}
    (h : JointHandlerLawEq left right) (activation : Activation Node) (state : State network S) :
    𝒟[fifoStep left activation state] = 𝒟[fifoStep right activation state] := by
  cases activation with
  | node node => exact activate_congr h .fifo node state
  | deliver => rfl

variable [DiscreteMeasurableSpace (State network S)]

/-- Every complete residual-state law is preserved at every finite token horizon. -/
theorem runToken_congr
    {left right : (node : Node) → Handler (StateT S ProbComp) (network.effect node)}
    (h : JointHandlerLawEq left right) (fuel : ℕ) (state : State network S) :
    𝒟[runToken left fuel state] = 𝒟[runToken right fuel state] := by
  induction fuel generalizing state with
  | zero => rfl
  | succ fuel ih =>
    simp only [runToken, evalDist_bind_of_discrete]
    rw [activate_congr h]
    apply Measure.bind_congr_right
    filter_upwards [] with state
    exact ih state

/-- Every fixed FIFO schedule preserves residual queues, machines, and service-state laws. -/
theorem runFIFO_congr
    {left right : (node : Node) → Handler (StateT S ProbComp) (network.effect node)}
    (h : JointHandlerLawEq left right) (schedule : List (Activation Node))
    (state : State network S) :
    𝒟[runFIFO left schedule state] = 𝒟[runFIFO right schedule state] := by
  induction schedule generalizing state with
  | nil => rfl
  | cons activation rest ih =>
    simp only [runFIFO, evalDist_bind_of_discrete]
    rw [fifoStep_congr h]
    apply Measure.bind_congr_right
    filter_upwards [] with state
    exact ih state

/-- Any observation of the complete token residual state respects joint local replacement. -/
theorem runToken_observe_congr {Observation : Type} [MeasurableSpace Observation]
    {left right : (node : Node) → Handler (StateT S ProbComp) (network.effect node)}
    (h : JointHandlerLawEq left right) (fuel : ℕ) (state : State network S)
    (observe : State network S → Observation) :
    𝒟[observe <$> runToken left fuel state] = 𝒟[observe <$> runToken right fuel state] := by
  rw [evalDist_map_of_discrete, evalDist_map_of_discrete, runToken_congr h]

/-- FIFO observation replacement retains the actual fixed schedule and all pending packets. -/
theorem runFIFO_observe_congr {Observation : Type} [MeasurableSpace Observation]
    {left right : (node : Node) → Handler (StateT S ProbComp) (network.effect node)}
    (h : JointHandlerLawEq left right) (schedule : List (Activation Node))
    (state : State network S) (observe : State network S → Observation) :
    𝒟[observe <$> runFIFO left schedule state] =
      𝒟[observe <$> runFIFO right schedule state] := by
  rw [evalDist_map_of_discrete, evalDist_map_of_discrete, runFIFO_congr h]

end ReactiveKernel

namespace ReactiveRuntime

open PFunctor ReactiveProcess ReactiveNetwork OracleComp MeasureTheory ReactiveKernel

variable {Node result S : Type} {boundary : PortBoundary}
  [DecidableEq Node] {network : Network Node boundary result}
  [MeasurableSpace S] [DiscreteMeasurableSpace S]
  [∀ node, ∀ operation : (network.effect node).A,
    MeasurableSpace ((network.effect node).B operation)]
  [∀ node, ∀ operation : (network.effect node).A,
    DiscreteMeasurableSpace ((network.effect node).B operation × S)]
  [MeasurableSpace (Option (Outcome result))]

/-- Actual setup-sampled token observations respect joint local-handler laws. -/
theorem tokenLaw_congr
    {left right : (node : Node) → Handler (StateT S ProbComp) (network.effect node)}
    (h : JointHandlerLawEq left right) (setup : ProbComp S) (fuel : ℕ) :
    tokenLaw network left setup fuel = tokenLaw network right setup fuel := by
  let : MeasurableSpace (State network S) := ⊤
  let : DiscreteMeasurableSpace (State network S) := ⟨fun _ => trivial⟩
  rw [tokenLaw_eq_evalDist, tokenLaw_eq_evalDist]
  simp only [tokenExperiment, evalDist_bind_of_discrete]
  apply Measure.bind_congr_right
  filter_upwards [] with state
  rw [runToken_congr (network := network) h]

/-- Actual setup-sampled FIFO observations respect joint local-handler laws. -/
theorem fifoLaw_congr
    {left right : (node : Node) → Handler (StateT S ProbComp) (network.effect node)}
    (h : JointHandlerLawEq left right) (setup : ProbComp S)
    (schedule : List (Activation Node)) :
    fifoLaw network left setup schedule = fifoLaw network right setup schedule := by
  let : MeasurableSpace (State network S) := ⊤
  let : DiscreteMeasurableSpace (State network S) := ⟨fun _ => trivial⟩
  rw [fifoLaw_eq_evalDist, fifoLaw_eq_evalDist]
  simp only [fifoExperiment, evalDist_bind_of_discrete]
  apply Measure.bind_congr_right
  filter_upwards [] with state
  rw [runFIFO_congr (network := network) h]

end ReactiveRuntime

end Interaction.UC
