/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Examples.OneTimePad.Separated

/-!
# Execution of separated authenticated transmission

The token runner executes all six actors, including private key distribution, a public
ciphertext/advice backchannel, and the receiver's optional delivery. Both delivery branches
retain their explicitly charged activations.
-/

public section

namespace OneTimePad.Separated

open PFunctor Interaction Interaction.Open Interaction.UC Interaction.Execution.ReactiveProcess
  Interaction.Execution.ReactiveNetwork DynSystem

variable {Message Cipher Random SendKey ReceiveKey Memory Advice : Type}

attribute [local implicit_reducible] effects ports envAnswer port signature Response
  diagram assembly DynComputation.ofFreeM PFunctor.Idx
  HandledDiagram.network Diagram.withEnvironment HandledAssembly.ofDiagram

-- The constructor pattern makes simplification wait for a concrete state before
-- unfolding the next activation inside an effectful continuation.
private theorem runToken_succ_mk
    {network : Network Node PortBoundary.empty Bool}
    (impl : (id : Node) → Handler (StateT Unit ProbComp) (network.effect id))
    (fuel : ℕ) (localState : (id : Node) → (network.component id).State)
    (inbox : (id : Node) → List (Interface.Packet (network.ports id).In))
    (service : Unit) (pending : List (Destination network))
    (output : List (Interface.Packet PortBoundary.empty.Out)) (focus : Node) (elapsed : ℕ) :
    runToken impl (fuel + 1) ⟨localState, inbox, service, pending, output, focus, elapsed⟩ =
      (activate impl .token focus ⟨localState, inbox, service, pending, output, focus, elapsed⟩ >>=
        runToken impl fuel) := rfl

private theorem runToken_zero
    {network : Network Node PortBoundary.empty Bool}
    (impl : (id : Node) → Handler (StateT Unit ProbComp) (network.effect id))
    (state : State network Unit) : runToken impl 0 state = pure state := rfl

/-- Twenty-nine token activations execute the complete six-actor conversation. -/
theorem experiment_eq (encoding : Encoding Message Cipher Random SendKey ReceiveKey)
    (draw : ProbComp Random) (env : Environment Message Cipher Memory Advice)
    (adversary : Adversary Cipher Advice) :
    experiment encoding draw env adversary 29 =
      (fun verdict => some (some verdict)) <$> conversation encoding draw env adversary := by
  simp only [experiment, assembly, HandledAssembly.ofDiagram, HandledAssembly.tokenObservation,
    HandledDiagram.tokenObservation, HandledDiagram.handlers, HandledDiagram.network,
    Diagram.withEnvironment, diagram, environmentProgram, setupProgram, senderProgram,
    channelProgram, adversaryProgram, receiverProgram, FreeM.pure_eq_pure,
    runToken_succ_mk, activate, initial, DynComputation.ofFreeM_init,
    DynComputation.view_ofFreeM_liftBind,
    DynComputation.ofFreeM_state, StateT.run, zero_add, bind_pure_comp,
    Functor.map_map, dispatch, bind_map_left, Function.update, ↓reduceDIte,
    Function.update_idem, List.nil_append, Nat.reduceAdd, pure_bind, reduceCtorEq,
    Function.update_eq_self, outcome, map_bind, conversation, ReactiveSecurity.observe]
  apply bind_congr
  rintro ⟨message, memory⟩
  apply bind_congr
  intro random
  apply bind_congr
  intro advice
  apply bind_congr
  intro permitted
  cases permitted <;>
    simp only [Bool.false_eq_true, ↓reduceIte, runToken_succ_mk, runToken_zero,
      activate, dispatch, StateT.run, HandledDiagram.handlers, bind_pure_comp, bind_map_left,
      DynComputation.view_ofFreeM_liftBind,
      DynComputation.ofFreeM_state, pure_bind, Function.update, ↓reduceDIte,
      Function.update_idem, Nat.reduceAdd, List.nil_append, reduceCtorEq,
      Function.update_eq_self, Functor.map_map, DynComputation.view_ofFreeM_pure] <;> rfl

end OneTimePad.Separated
