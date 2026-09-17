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

open PFunctor Interaction.UC ReactiveProcess ReactiveNetwork DynSystem

variable {Message Cipher Random SendKey ReceiveKey Memory Advice : Type}

attribute [local implicit_reducible] effects ports envAnswer port signature Response
  diagram assembly DynComputation.ofFreeM PFunctor.Idx
  HandledDiagram.network Diagram.withEnvironment HandledAssembly.ofDiagram

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
    runToken, activate, initial, DynComputation.ofFreeM_init,
    DynComputation.view_ofFreeM_liftBind,
    DynComputation.ofFreeM_State, StateT.run, zero_add, bind_pure_comp,
    Functor.map_map, dispatch, bind_pure, bind_map_left, Function.update, ↓reduceDIte,
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
    simp only [Bool.false_eq_true, ↓reduceIte, DynComputation.view_ofFreeM_liftBind,
      DynComputation.ofFreeM_State, pure_bind, Function.update, ↓reduceDIte,
      Function.update_idem, Nat.reduceAdd, List.nil_append, reduceCtorEq,
      Function.update_eq_self, Functor.map_map, DynComputation.view_ofFreeM_pure] <;> rfl

end OneTimePad.Separated
