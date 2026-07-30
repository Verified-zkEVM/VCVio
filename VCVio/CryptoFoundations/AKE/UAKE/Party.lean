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

def runHonestLoop [Monad m] {InP OutP InQ OutQ : Type}
    (P : Party m InP W OutP) (Q : Party m InQ W OutQ) :
    ℕ → P.State → Q.State → W → Bool → m (P.State × Q.State × List W)
  | 0, pState, qState, _, _ => pure (pState, qState, [])
  | fuel + 1, pState, qState, w, true => do
      match ← Q.step qState w with
      | .acceptAndSend qState' w' _ => do
          let (pFinal, qFinal, ms) ← runHonestLoop P Q fuel pState qState' w' false
          pure (pFinal, qFinal, w' :: ms)
      | .complete qState' => pure (pState, qState', [])
      | .reject => pure (pState, qState, [])
  | fuel + 1, pState, qState, w, false => do
      match ← P.step pState w with
      | .acceptAndSend pState' w' _ => do
          let (pFinal, qFinal, ms) ← runHonestLoop P Q fuel pState' qState w' true
          pure (pFinal, qFinal, w' :: ms)
      | .complete pState' => pure (pState', qState, [])
      | .reject => pure (pState, qState, [])

def runHonest [Monad m] {InP OutP InQ OutQ : Type}
    (P : Party m InP W OutP) (Q : Party m InQ W OutQ) (inP : InP) (inQ : InQ) (fuel : ℕ) :
    m (Option OutP × Option OutQ × List W) := do
  let pInit ← P.init inP
  let qInit ← Q.init inQ
  let (pState', qState', ms) ← match pInit.opening, qInit.opening with
    | some w, _ => do
        let (pState', qState', ms) ← runHonestLoop P Q fuel pInit.state qInit.state w true
        pure (pState', qState', w :: ms)
    | none, some w => do
        let (pState', qState', ms) ← runHonestLoop P Q fuel pInit.state qInit.state w false
        pure (pState', qState', w :: ms)
    | none, none => pure (pInit.state, qInit.state, [])
  let pOut ← P.output pState'
  let qOut ← Q.output qState'
  pure (pOut, qOut, ms)

end Party

end AKE.UAKE
