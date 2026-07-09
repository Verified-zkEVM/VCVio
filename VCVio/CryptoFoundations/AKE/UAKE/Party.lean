/-
Copyright (c) 2026 Galois Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ben Hamlin
-/
import VCVio.CryptoFoundations.SecExp
import VCVio.OracleComp.SimSemantics.Append
import VCVio.OracleComp.SimSemantics.SimulateQ

open OracleSpec OracleComp

namespace AKE

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

inductive StepResult (State W : Type)
  | acceptAndSend (state : State) (msg : W) (done : Bool) : StepResult State W
  | complete (state : State) : StepResult State W
  | reject : StepResult State W

structure Party (m : Type → Type) (In W Out : Type) where
  State : Type
  init : In → m (InitResult State W)
  step : State → W → m (StepResult State W)
  output : State → m (Option Out)

namespace Party

def RecoveryDeterministic {In W Out : Type} (P : Party ProbComp In W Out) : Prop :=
  ∀ st : P.State, ∃ m, P.output st = pure m

def OutputsAtCompletion {In W Out : Type} (P : Party ProbComp In W Out) : Prop :=
  (∀ i r, r ∈ support (P.init i) → ∀ m ∈ support (P.output r.state), m = none) ∧
    (∀ st w st' w' b, StepResult.acceptAndSend st' w' b ∈ support (P.step st w) →
      ∀ m ∈ support (P.output st'), m = none)

end Party

end AKE
