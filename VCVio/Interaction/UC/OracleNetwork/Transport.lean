/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import VCVio.Interaction.UC.OracleNetwork

/-!
# Transporting FIFO executions along component identities

A bijection of static component identities transports the complete runtime, including waiting
clients, queued requests and responses, and delivered transcripts. Transporting the schedule
along the same bijection commutes with actual execution in any lawful surface monad. Sampling
effects are preserved by this monadic equality; no reassociation of nested scheduler choices is
assumed.
-/

public section

namespace Interaction.UC.OracleNetwork

-- Delivery constructs dependent packets explicitly before applying their public transport laws.
attribute [local implicit_reducible] PFunctor.Idx

variable {Client Client' ι α S : Type} {spec : OracleSpec ι}

/-- Transport both kinds of queued traffic while retaining their unique tickets. -/
@[expose] def Envelope.rename (e : Client ≃ Client') :
    Envelope Client spec → Envelope Client' spec
  | .request id ticket a => .request (e id) ticket a
  | .response ticket reply => .response ticket (reply.mapSender e)

/-- Relabel a schedule without changing its ordering or delivery fuel. -/
@[expose] def Activation.rename (e : Client ≃ Client') : Activation Client → Activation Client'
  | .client id => .client (e id)
  | .deliver => .deliver

/-- Transport the complete state; private service state and ticket allocation are shared. -/
@[expose] def State.rename (e : Client ≃ Client') (state : State Client spec α S) :
    State Client' spec α S where
  clients := fun id => state.clients (e.symm id)
  service := state.service
  queue := state.queue.map (Envelope.rename e)
  nextTicket := state.nextTicket
  transcript := state.transcript.map (Interface.RoutedPacket.mapSender e)

variable [DecidableEq Client] [DecidableEq Client'] [DecidableEq ι]

omit [DecidableEq ι] in
private theorem update_rename (e : Client ≃ Client') (clients : Client → ClientState spec α)
    (id : Client) (next : ClientState spec α) :
    Function.update (fun id => clients (e.symm id)) (e id) next =
      fun id' => Function.update clients id next (e.symm id') := by
  funext id'
  by_cases h : id' = e id
  · subst id'; simp
  · have h' : e.symm id' ≠ id := fun heq => h (by simpa using congrArg e heq)
    simp [Function.update_of_ne h, Function.update_of_ne h']

omit [DecidableEq ι] in
/-- Emission commutes with relabeling, including the client's waiting continuation. -/
theorem emit_rename (e : Client ≃ Client') (id : Client) (state : State Client spec α S) :
    emit (e id) (state.rename e) = (emit id state).rename e := by
  cases h : state.clients id with
  | waiting ticket a next => simp [emit, State.rename, h]
  | ready program =>
      cases program using OracleComp.casesOn with
      | pure value => simp [emit, State.rename, h]
      | queryBind a next =>
          simp [emit, State.rename, h, Envelope.rename, update_rename]

/-- Accepting a typed response commutes with relabeling its destination client. -/
theorem accept_rename (e : Client ≃ Client') (ticket : ℕ)
    (reply : Interface.RoutedPacket spec.toPFunctor Client) (state : State Client spec α S) :
    accept ticket (reply.mapSender e) (state.rename e) = (accept ticket reply state).rename e := by
  rcases reply with ⟨sender, packet⟩
  rw [Interface.RoutedPacket.mapSender_mk]
  cases h : state.clients sender with
  | ready program => simp [accept, State.rename, h]
  | waiting expected a next =>
      by_cases ht : ticket = expected <;> by_cases ha : packet.1 = a <;>
        simp [accept, State.rename, h, ht, ha, update_rename,
          Interface.RoutedPacket.mapSender_mk]

variable {m : Type → Type} [Monad m] [LawfulMonad m]

/-- Actual FIFO delivery preserves the service's effects when component identities are renamed. -/
theorem deliver_rename (impl : QueryImpl spec (StateT S m)) (e : Client ≃ Client')
    (state : State Client spec α S) :
    deliver impl (state.rename e) = State.rename e <$> deliver impl state := by
  cases h : state.queue with
  | nil => simp [deliver, State.rename, h]
  | cons packet rest =>
      cases packet with
      | request id ticket a =>
          simp [deliver, State.rename, h, Envelope.rename]
      | response ticket reply =>
          simpa only [deliver, State.rename, h, List.map_cons, Envelope.rename, map_pure] using
            congrArg (pure (f := m)) (accept_rename e ticket reply { state with queue := rest })

/-- The same relabeling applies to client activations and packet-delivery activations. -/
theorem step_rename (impl : QueryImpl spec (StateT S m)) (e : Client ≃ Client')
    (activation : Activation Client) (state : State Client spec α S) :
    step impl (activation.rename e) (state.rename e) =
      State.rename e <$> step impl activation state := by
  cases activation with
  | client id => simp [step, Activation.rename, emit_rename]
  | deliver => exact deliver_rename impl e state

/-- Renaming an explicit schedule transports all pending traffic and its sampled execution. -/
theorem run_rename (impl : QueryImpl spec (StateT S m)) (e : Client ≃ Client')
    (schedule : List (Activation Client)) (state : State Client spec α S) :
    run impl (schedule.map (Activation.rename e)) (state.rename e) =
      State.rename e <$> run impl schedule state := by
  induction schedule generalizing state with
  | nil => simp [run]
  | cons action rest ih =>
      simp only [List.map_cons, run, step_rename, bind_map_left, map_bind]
      congr 1
      funext next
      exact ih next

end Interaction.UC.OracleNetwork
