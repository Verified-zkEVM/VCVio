/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import VCVio.Interaction.UC.OracleNetwork.Serial

/-!
# FIFO runtime regression examples

These examples distinguish service execution from response delivery, exercise FIFO ordering
between two stable clients, and check that a resumed continuation uses its actual answer.
-/

public section

open OracleComp PFunctor Interaction.UC.OracleNetwork

namespace VCVioTest.OracleNetwork

/-- Integer-valued test operations. -/
abbrev spec : OracleSpec Nat := fun _ => Nat

/-- A deterministic service that charges one state increment per request. -/
def service : QueryImpl spec (StateT Nat Id) := fun query state =>
  (query + state, state + 1)

/-- A client whose second input depends on its first response. -/
def adaptive : OracleComp spec Nat := do
  let first ← FreeM.lift (P := spec.toPFunctor) 10
  FreeM.lift (P := spec.toPFunctor) (first + 1)

/-- The second query depends on the answer delivered to the first one. -/
theorem adaptive_result : (serialObservation service 2 adaptive 0).run.1.1 = some 12 := by rfl

example : (serialObservation service 2 adaptive 0).run.2 = 2 := by rfl

-- A full first round leaves the adaptive second query unexecuted.
example : (serialObservation service 1 adaptive 0).run.1.1 = none := by rfl

-- Service execution alone has changed private state, but the response remains pending.
private def afterService :=
  (run service [.client (), .deliver] (initial adaptive 0)).run

example : afterService.service = 1 := by rfl
example : result () afterService = none := by rfl
example : afterService.queue.length = 1 := by rfl
example : afterService.transcript.length = 0 := by rfl

-- Activating an already waiting client cannot emit another request.
example : (emit () afterService).nextTicket = 1 := by rfl
example : (emit () afterService).queue.length = 1 := by rfl

private def pair : State Bool spec Nat Nat :=
  ⟨fun id => .ready (FreeM.lift (P := spec.toPFunctor) (if id then 20 else 10)),
    0, [], 0, []⟩

private def pairServiced :=
  (run service [.client false, .client true, .deliver, .deliver] pair).run

-- Both requests have executed before either queued response is delivered.
example : pairServiced.service = 2 := by rfl
example : result false pairServiced = none := by rfl
example : result true pairServiced = none := by rfl
example : pairServiced.transcript = [] := by rfl

private def pairDelivered := (run service [.deliver, .deliver] pairServiced).run

example : result false pairDelivered = some 10 := by rfl
example : result true pairDelivered = some 21 := by rfl
example : pairDelivered.transcript.map (·.sender) = [false, true] := by rfl
example : pairDelivered.queue = [] := by rfl

-- A stale ticket and a mismatched query tag cannot wake a suspended client.
example : result () (accept 7 ⟨(), ⟨10, 99⟩⟩ afterService) = none := by rfl
example : result () (accept 0 ⟨(), ⟨11, 99⟩⟩ afterService) = none := by rfl

end VCVioTest.OracleNetwork
