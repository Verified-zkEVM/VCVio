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

namespace AKE

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

/-- A party, structured as a Mealy machine with a final output function. -/
structure Party (m : Type → Type) (In W Out : Type) where
  State : Type
  init : In → m (InitResult State W)
  step : State → W → m (StepResult State W)
  output : State → m (Option Out)

namespace Party

/-- True if the final output message of a party is deterministic given the
   state. I.e., all non-determinism is in the init and step functions. -/
def RecoveryDeterministic {In W Out : Type} (P : Party ProbComp In W Out) : Prop :=
  ∀ st : P.State, ∃ m, P.output st = pure m

-- TODO: Fix this
/-- True if a party outputs a final message only once the protocol is complete. -/
def OutputsAtCompletion {In W Out : Type} (P : Party ProbComp In W Out) : Prop :=
  (∀ i r, r ∈ support (P.init i) → ∀ m ∈ support (P.output r.state), m = none) ∧
    (∀ st w st' w' b, StepResult.acceptAndSend st' w' b ∈ support (P.step st w) →
      ∀ m ∈ support (P.output st'), m = none)

end Party

end AKE
