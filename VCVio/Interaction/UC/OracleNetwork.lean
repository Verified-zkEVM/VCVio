/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.Interaction.UC.RequestNetwork
public import VCVio.OracleComp.SimSemantics.SimulateQ

/-!
# FIFO execution of oracle clients

Oracle-specific names for the generic polynomial request network. Stable clients issue
at most one outstanding request, a shared stateful service responds, and ticketed replies
resume the matching continuation. Delivery and local activation consume separate steps.

The implementation and exact transport laws are owned by `Interaction.UC.RequestNetwork`.
This facade specializes the polynomial to `OracleSpec.toPFunctor`.
-/

public section

namespace Interaction.UC.OracleNetwork

variable {ι : Type}

/-- Residual oracle code or a continuation awaiting a ticketed response. -/
abbrev ClientState (spec : OracleSpec ι) (α : Type) :=
  RequestNetwork.ClientState spec.toPFunctor α

/-- A queued oracle request or typed ticketed response. -/
abbrev Envelope (Client : Type) (spec : OracleSpec ι) :=
  RequestNetwork.Envelope Client spec.toPFunctor

/-- Complete residual oracle network state, including its single shared service. -/
abbrev State (Client : Type) (spec : OracleSpec ι) (α S : Type) :=
  RequestNetwork.State Client spec.toPFunctor α S

/-- Client activation or delivery of the oldest queued packet. -/
abbrev Activation := RequestNetwork.Activation

variable {Client α S : Type} {spec : OracleSpec ι} [DecidableEq Client] [DecidableEq ι]

/-- Emit an oracle request and suspend its client until the matching response arrives. -/
abbrev emit (id : Client) (state : State Client spec α S) := RequestNetwork.emit id state

/-- Accept a response only at its matching ticket and dependent oracle query tag. -/
abbrev accept (ticket : ℕ) (reply : Interface.RoutedPacket spec.toPFunctor Client)
    (state : State Client spec α S) := RequestNetwork.accept ticket reply state

variable {m : Type → Type} [Monad m]

/-- Deliver the oldest request or response, threading the single shared service state. -/
abbrev deliver (impl : QueryImpl spec (StateT S m)) (state : State Client spec α S) :=
  RequestNetwork.deliver impl state

/-- Execute one explicitly selected client or delivery activation. -/
abbrev step (impl : QueryImpl spec (StateT S m)) (activation : Activation Client)
    (state : State Client spec α S) := RequestNetwork.step impl activation state

/-- Run a finite schedule, preserving all residual clients and pending packets. -/
abbrev run (impl : QueryImpl spec (StateT S m)) (schedule : List (Activation Client))
    (state : State Client spec α S) := RequestNetwork.run impl schedule state

export RequestNetwork (run_append emit_waiting accept_wrong_ticket run_roundtrip)

end Interaction.UC.OracleNetwork
