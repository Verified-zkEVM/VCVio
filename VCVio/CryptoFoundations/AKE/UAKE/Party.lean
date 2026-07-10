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

/-- True if the final output message of a party is deterministic given the
   state. I.e., all non-determinism is in the init and step functions. -/
def RecoveryDeterministic [Monad m] (P : Party m In W Out) : Prop :=
  ∀ st : P.State, ∃ out, P.output st = pure out

/-- True if a party outputs a final message only once the protocol is complete. -/
def OutputsAtCompletion [MonadLiftT m SetM] (P : Party m In W Out) : Prop :=
  (∀ i r, r ∈ support (P.init i) → ∀ out ∈ support (P.output r.state), out = none) ∧
    (∀ st w st' w', StepResult.acceptAndSend st' w' false ∈ support (P.step st w) →
      ∀ out ∈ support (P.output st'), out = none)

def runHonestLoop [Monad m] {InP OutP InQ OutQ : Type}
    (P : Party m InP W OutP) (Q : Party m InQ W OutQ) :
    ℕ → P.State → Q.State → W → Bool → m (P.State × Q.State)
  | 0, pState, qState, _, _ => pure (pState, qState)
  | fuel + 1, pState, qState, w, true => do
      match ← Q.step qState w with
      | .acceptAndSend qState' w' _ => runHonestLoop P Q fuel pState qState' w' false
      | .complete qState' => pure (pState, qState')
      | .reject => pure (pState, qState)
  | fuel + 1, pState, qState, w, false => do
      match ← P.step pState w with
      | .acceptAndSend pState' w' _ => runHonestLoop P Q fuel pState' qState w' true
      | .complete pState' => pure (pState', qState)
      | .reject => pure (pState, qState)

def runHonest [Monad m] {InP OutP InQ OutQ : Type}
    (P : Party m InP W OutP) (Q : Party m InQ W OutQ) (inP : InP) (inQ : InQ) (fuel : ℕ) :
    m (Option OutP × Option OutQ) := do
  let pInit ← P.init inP
  let qInit ← Q.init inQ
  let (pState', qState') ← match pInit.opening, qInit.opening with
    | some w, _ => runHonestLoop P Q fuel pInit.state qInit.state w true
    | none, some w => runHonestLoop P Q fuel pInit.state qInit.state w false
    | none, none => pure (pInit.state, qInit.state)
  let pOut ← P.output pState'
  let qOut ← Q.output qState'
  pure (pOut, qOut)

end Party

end AKE.UAKE
