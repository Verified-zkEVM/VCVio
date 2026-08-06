/-
Copyright (c) 2026 Galois Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ben Hamlin
-/
import VCVio.CryptoFoundations.SecExp
import VCVio.OracleComp.SimSemantics.Append
import VCVio.OracleComp.SimSemantics.SimulateQ

/-!
# UAKE Scheme Party Definitions

This module defines a party for use in the UAKE security notion from DF'17. In
the paper, a party is an ITM. We instead model it as a Mealy machine with a
step function that outputs a protocol message and a new state. The output
function takes the party's state and produces its final output (in UAKE, this
is the key). It is up to the protocol realization to ensure that the output
function produces output only at the end.
-/

open OracleSpec OracleComp

namespace AKE.UAKE

namespace Party

/-- Result of a party's init function -/
inductive InitResult (State W : Type)
  | speakFirst (state : State) (msg : W) : InitResult State W
  | waitForMsg (state : State) : InitResult State W

namespace InitResult

@[simp] def state {State W : Type} : InitResult State W → State
  | .speakFirst st _ => st
  | .waitForMsg st => st

@[simp] def opening {State W : Type} : InitResult State W → Option W
  | .speakFirst _ msg => some msg
  | .waitForMsg _ => none

end InitResult

/-- Result of a party's step function -/
inductive StepResult (State W : Type)
  | acceptAndSend (state : State) (msg : W) (done : Bool) : StepResult State W
  | complete (state : State) : StepResult State W
  | reject : StepResult State W

end Party

/-- A party, structured as a Mealy machine with a final output function. -/
structure Party (m : Type → Type) (In W Out : Type) where
  State : Type
  init : In → m (Party.InitResult State W)
  step : State → W → m (Party.StepResult State W)
  output : State → m (Option Out)

namespace Party

variable {m : Type → Type} {In W Out : Type}

/-- True if a party is well-formed, i.e., if it outputs iff the state is
  the result of an execution of the step function that returns `done = true`
  or `.complete` (assuming the state is reachable). -/
def OutputsOnlyAtCompletion [MonadLiftT m SetM] (P : Party m In W Out) : Prop :=
  let init_output := ∀ i r, r ∈ support (P.init i) →
    ∀ out ∈ support (P.output r.state), out = none;
  let complete_output := ∀ st w st', .complete st' ∈ support (P.step st w) →
    ∀ out ∈ support (P.output st'), out ≠ none;
  let accept_output := ∀ st w st' w' (done : Bool),
    .acceptAndSend st' w' done ∈ support (P.step st w) →
      ∀ out ∈ support (P.output st'), out ≠ none ↔ done;
  init_output ∧ complete_output ∧ accept_output

/-- Helper function for runHonest. Run the two parties against each other. The
  messages sent are returned in chronological order, along with P's and Q's
  states.
  * The `fuel` argument is an upper bound on the number of party step functions
    that may be run before the protocol completes.
  * The Boolean indicates whether this is Q's (true) or P's (false) turn.
  * The `sent` list contains the messages sent in the protocol so far. Note
    that the `sent` list must be passed to this function in *reverse*
    chronological order. This is to support easy cons-ing of new messages. -/
def runHonestLoop [Monad m] {InP OutP InQ OutQ : Type}
    (P : Party m InP W OutP) (Q : Party m InQ W OutQ) :
    ℕ → P.State → Q.State → W → Bool → List W → m (P.State × Q.State × List W)
  | 0, pState, qState, _, _, sent => pure (pState, qState, sent.reverse)
  | fuel + 1, pState, qState, w, true, sent => do
      match ← Q.step qState w with
      | .acceptAndSend qState' w' _ =>
          runHonestLoop P Q fuel pState qState' w' false (w' :: sent)
      | .complete qState' => pure (pState, qState', sent.reverse)
      | .reject => pure (pState, qState, sent.reverse)
  | fuel + 1, pState, qState, w, false, sent => do
      match ← P.step pState w with
      | .acceptAndSend pState' w' _ =>
          runHonestLoop P Q fuel pState' qState w' true (w' :: sent)
      | .complete pState' => pure (pState', qState, sent.reverse)
      | .reject => pure (pState, qState, sent.reverse)

/-- Start an honest run of the protocol, initiating the loop function based on
  which party opens. -/
def runHonestStart [Monad m] {InP OutP InQ OutQ : Type}
    (P : Party m InP W OutP) (Q : Party m InQ W OutQ) (fuel : ℕ)
    (pInit : InitResult P.State W) (qInit : InitResult Q.State W) :
    m (P.State × Q.State × List W) :=
  match pInit.opening, qInit.opening with
  | some w, _ => runHonestLoop P Q fuel pInit.state qInit.state w true [w]
  | none, some w => runHonestLoop P Q fuel pInit.state qInit.state w false [w]
  | none, none => pure (pInit.state, qInit.state, [])

/-- Execute an honest run of the protocol. The result is a triple of P's
  output, Q's output, and the message list. The `fuel` argument is an upper
  bound on how many party step functions may be run in the execution of the
  protocol. -/
def runHonest [Monad m] {InP OutP InQ OutQ : Type}
    (P : Party m InP W OutP) (Q : Party m InQ W OutQ) (inP : InP) (inQ : InQ) (fuel : ℕ) :
    m (Option OutP × Option OutQ × List W) := do
  let pInit ← P.init inP
  let qInit ← Q.init inQ
  let (pState', qState', ms) ← runHonestStart P Q fuel pInit qInit
  let pOut ← P.output pState'
  let qOut ← Q.output qState'
  pure (pOut, qOut, ms)

end Party

end AKE.UAKE
