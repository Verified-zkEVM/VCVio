/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.Interaction.UC.Interface
public import VCVio.OracleComp.SimSemantics.SimulateQ

/-!
# FIFO execution of oracle clients

Clients have stable identities and at most one outstanding request. A shared service answers
requests in FIFO order; responses travel through the same queue before resuming their client.
Each request carries a fresh ticket, and a response resumes only the matching waiting client.
Schedules explicitly distinguish client activation from packet delivery. One RPC therefore
requires three activations, even when the service computation itself is pure.

The service's monadic effect is atomic at this runtime boundary. Its internal cost is separate
from packet-delivery fuel. No fairness or completion assumption is built into finite execution.
Typed response traffic uses PolyFun's `Interface.RoutedPacket` vocabulary.
-/

public section

namespace Interaction.UC.OracleNetwork

open OracleComp PFunctor

variable {Client ι α S : Type} {spec : OracleSpec ι}

/-- A client either has executable code or awaits one particular response. -/
inductive ClientState (spec : OracleSpec ι) (α : Type) where
  | ready (program : OracleComp spec α)
  | waiting (ticket : ℕ) (query : ι) (next : spec query → OracleComp spec α)

/-- Requests and typed responses share one FIFO queue. -/
inductive Envelope (Client : Type) (spec : OracleSpec ι) where
  | request (client : Client) (ticket : ℕ) (query : ι)
  | response (ticket : ℕ) (reply : Interface.RoutedPacket spec.toPFunctor Client)

/-- The complete runtime state, including pending traffic and delivered responses. -/
structure State (Client : Type) (spec : OracleSpec ι) (α S : Type) where
  /-- Residual code or the single pending continuation of each static client. -/
  clients : Client → ClientState spec α
  /-- Private state shared by all calls to the service. -/
  service : S
  /-- Outstanding requests and responses, oldest packet first. -/
  queue : List (Envelope Client spec)
  /-- Fresh ticket reserved for the next emitted request. -/
  nextTicket : ℕ
  /-- Responses actually delivered to matching clients, in delivery order. -/
  transcript : List (Interface.RoutedPacket spec.toPFunctor Client)

/-- A schedule either activates a client or delivers the oldest queued packet. -/
inductive Activation (Client : Type) where
  | client (id : Client)
  | deliver
  deriving DecidableEq

variable [DecidableEq Client] [DecidableEq ι]

/-- Emit one request and suspend its client. Waiting and returned clients emit nothing. -/
@[expose] def emit (id : Client) (state : State Client spec α S) : State Client spec α S :=
  match state.clients id with
  | .ready (.liftBind a next) =>
      { state with
        clients := Function.update state.clients id (.waiting state.nextTicket a next)
        queue := state.queue ++ [.request id state.nextTicket a]
        nextTicket := state.nextTicket + 1 }
  | _ => state

/-- Resume a waiting client only when both ticket and dependent query tag match. -/
@[expose] def accept (ticket : ℕ) (reply : Interface.RoutedPacket spec.toPFunctor Client)
    (state : State Client spec α S) : State Client spec α S :=
  match state.clients reply.sender with
  | .waiting expected a next =>
      if ticket = expected then
        if ha : reply.packet.1 = a then
          { state with
            clients := Function.update state.clients reply.sender
              (.ready (next (ha ▸ reply.packet.2)))
            transcript := state.transcript ++ [reply] }
        else state
      else state
  | _ => state

variable {m : Type → Type} [Monad m]

/-- Deliver the oldest packet. Servicing a request appends its response at the queue's tail. -/
@[expose] def deliver (impl : QueryImpl spec (StateT S m))
    (state : State Client spec α S) : m (State Client spec α S) :=
  match state.queue with
  | [] => pure state
  | .request id ticket a :: rest => do
      let (answer, service) ← (impl a).run state.service
      pure { state with service, queue := rest ++ [.response ticket ⟨id, ⟨a, answer⟩⟩] }
  | .response ticket reply :: rest =>
      pure (accept ticket reply { state with queue := rest })

/-- Execute one scheduled activation, including a no-op activation in its fuel count. -/
@[expose] def step (impl : QueryImpl spec (StateT S m))
    (activation : Activation Client) (state : State Client spec α S) :
    m (State Client spec α S) :=
  match activation with
  | .client id => pure (emit id state)
  | .deliver => deliver impl state

/-- Execute an explicit finite schedule. Unserviced packets remain in the returned state. -/
@[expose] def run (impl : QueryImpl spec (StateT S m)) :
    List (Activation Client) → State Client spec α S → m (State Client spec α S)
  | [], state => pure state
  | action :: rest, state => step impl action state >>= run impl rest

variable [LawfulMonad m]

/-- Splitting a schedule retains all pending traffic, tickets, and private service state. -/
theorem run_append (impl : QueryImpl spec (StateT S m))
    (first second : List (Activation Client)) (state : State Client spec α S) :
    run impl (first ++ second) state =
      (run impl first state >>= run impl second) := by
  induction first generalizing state with
  | nil => simp [run]
  | cons action rest ih =>
      simp only [List.cons_append, run, bind_assoc]
      congr 1
      funext next
      exact ih next

omit [DecidableEq ι] in
/-- A suspended client cannot enqueue a second request. -/
theorem emit_waiting (id : Client) (state : State Client spec α S)
    (ticket : ℕ) (a : ι) (next : spec a → OracleComp spec α)
    (h : state.clients id = .waiting ticket a next) : emit id state = state := by
  simp [emit, h]

/-- A stale ticket cannot resume a waiting client or enter its delivered transcript. -/
theorem accept_wrong_ticket (ticket expected : ℕ)
    (reply : Interface.RoutedPacket spec.toPFunctor Client) (state : State Client spec α S)
    (a : ι) (next : spec a → OracleComp spec α)
    (h : state.clients reply.sender = .waiting expected a next) (hne : ticket ≠ expected) :
    accept ticket reply state = state := by
  simp [accept, h, hne]

/-- Three activations complete one query when the queue starts empty. The continuation sees the
actual service answer, and the final transcript records that answer with its stable client id. -/
theorem run_roundtrip (impl : QueryImpl spec (StateT S m)) (id : Client)
    (state : State Client spec α S) (a : ι) (next : spec a → OracleComp spec α)
    (hclient : state.clients id = .ready (.liftBind a next)) (hqueue : state.queue = []) :
    run impl [.client id, .deliver, .deliver] state = (do
      let (answer, service) ← (impl a).run state.service
      pure { state with
        clients := Function.update state.clients id (.ready (next answer))
        service
        queue := []
        nextTicket := state.nextTicket + 1
        transcript := state.transcript ++ [⟨id, ⟨a, answer⟩⟩] }) := by
  simp [run, step, emit, hclient, deliver, hqueue, accept]

end Interaction.UC.OracleNetwork
