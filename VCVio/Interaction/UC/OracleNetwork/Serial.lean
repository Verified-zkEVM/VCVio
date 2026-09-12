/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import VCVio.Interaction.UC.OracleNetwork
public import VCVio.OracleComp.QueryTracking.Tracing
public import VCVio.OracleComp.QueryTracking.QueryBound.Basic

/-!
# Bounded adaptive clients over FIFO delivery

A serial schedule allocates three activations per permitted client query. The resulting
runtime state agrees with ordinary oracle interpretation instrumented by the existing trace
handler: it has the same verdict, private service state, and ordered response transcript.
The query bound ranges over every adaptive answer branch. Extra schedule rounds after a
client has returned are harmless, while a shorter schedule may leave that client unfinished.
-/

public section

namespace Interaction.UC.OracleNetwork

open OracleComp PFunctor

variable {Client ι α S : Type} {spec : OracleSpec ι}

/-- Allocate a complete request/service/response cycle for each query budget unit. -/
@[expose] def serialSchedule (id : Client) : ℕ → List (Activation Client)
  | 0 => []
  | n + 1 => [.client id, .deliver, .deliver] ++ serialSchedule id n

/-- The schedule charges all three administrative activations of each allocated RPC. -/
@[simp] theorem serialSchedule_length (id : Client) (n : ℕ) :
    (serialSchedule id n).length = 3 * n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [serialSchedule, ih, Nat.mul_add]

variable [DecidableEq Client] [DecidableEq ι]
  {m : Type → Type} [Monad m] [LawfulMonad m]

/-- Interpret a client with the standard response-dependent trace instrumentation. -/
@[expose] def loggedRun (impl : QueryImpl spec (StateT S m)) (id : Client)
    (program : OracleComp spec α) (service : S) :
    m ((α × List (Interface.RoutedPacket spec.toPFunctor Client)) × S) :=
  (simulateQ (impl.withTraceAppend fun a answer => [⟨id, ⟨a, answer⟩⟩]) program).run.run service

omit [DecidableEq Client] [DecidableEq ι] [LawfulMonad m] in
/-- Returning produces no response traffic and retains the private service state. -/
@[simp] theorem loggedRun_pure (impl : QueryImpl spec (StateT S m)) (id : Client)
    (value : α) (service : S) :
    loggedRun impl id (pure value) service = pure ((value, []), service) := by
  rfl

omit [DecidableEq Client] [DecidableEq ι] in
/-- Logged oracle interpretation prepends the current response to the continuation's traffic. -/
theorem loggedRun_liftBind (impl : QueryImpl spec (StateT S m)) (id : Client)
    (a : ι) (next : spec a → OracleComp spec α) (service : S) :
    loggedRun impl id (.liftBind a next) service = (do
      let (answer, service') ← (impl a).run service
      let (out, service'') ← loggedRun impl id (next answer) service'
      pure ((out.1, ⟨id, ⟨a, answer⟩⟩ :: out.2), service'')) := by
  change ((impl.withTraceAppend _ a >>= fun answer =>
    simulateQ (impl.withTraceAppend _) (next answer)).run).run service = _
  simp [loggedRun, bind_assoc]

/-- A returned client and an empty queue remain fixed through all further serial rounds. -/
theorem run_serialSchedule_return (impl : QueryImpl spec (StateT S m)) (id : Client)
    (n : ℕ) (state : State Client spec α S) (value : α)
    (hclient : state.clients id = .ready (pure value)) (hqueue : state.queue = []) :
    run impl (serialSchedule id n) state = pure state := by
  induction n with
  | zero => rfl
  | succ n ih => simp [serialSchedule, run, step, emit, hclient, deliver, hqueue, ih]

/-- A bounded adaptive client completes within its allocated FIFO schedule. The full returned
state agrees with the traced oracle game, including the number of fresh tickets actually used. -/
theorem run_serialSchedule (impl : QueryImpl spec (StateT S m)) (id : Client)
    (n : ℕ) (program : OracleComp spec α) (hbound : IsTotalQueryBound program n)
    (state : State Client spec α S) (hclient : state.clients id = .ready program)
    (hqueue : state.queue = []) :
    run impl (serialSchedule id n) state = (do
      let (out, service) ← loggedRun impl id program state.service
      pure { state with
        clients := Function.update state.clients id (.ready (pure out.1))
        service
        queue := []
        nextTicket := state.nextTicket + out.2.length
        transcript := state.transcript ++ out.2 }) := by
  induction program using OracleComp.inductionOn generalizing n state with
  | pure value =>
      rw [run_serialSchedule_return impl id n state value hclient hqueue]
      simp only [loggedRun_pure, pure_bind, List.length_nil, Nat.add_zero, List.append_nil]
      congr 1
      rw [← hclient, Function.update_eq_self]
      cases state
      simp_all
  | query_bind a next ih =>
      rw [isTotalQueryBound_query_bind_iff] at hbound
      cases n with
      | zero => exact False.elim (Nat.lt_irrefl 0 hbound.1)
      | succ n =>
          rw [serialSchedule, run_append, run_roundtrip impl id state a next hclient hqueue]
          change _ = (do
            let out ← loggedRun impl id (.liftBind a next) state.service
            pure { state with
              clients := Function.update state.clients id (.ready (pure out.1.1))
              service := out.2
              queue := []
              nextTicket := state.nextTicket + out.1.2.length
              transcript := state.transcript ++ out.1.2 })
          rw [loggedRun_liftBind]
          simp only [bind_assoc, pure_bind]
          congr 1
          funext answer
          rcases answer with ⟨answer, service⟩
          rw [ih answer n (by simpa using hbound.2 answer) _ (by simp) rfl]
          simp [List.length_cons, List.append_assoc, Nat.add_assoc, Nat.add_comm,
            Function.update_idem]

/-- Start a single adaptive client with no pending traffic or prior transcript. -/
@[expose] def initial (program : OracleComp spec α) (service : S) : State Unit spec α S :=
  ⟨fun _ => .ready program, service, [], 0, []⟩

/-- Read a returned result without treating fuel exhaustion as successful termination. -/
@[expose] def result (id : Client) (state : State Client spec α S) : Option α :=
  match state.clients id with
  | .ready (.pure value) => some value
  | _ => none

/-- Observe a bounded run's optional result, response transcript, and private service state. -/
@[expose] def serialObservation (impl : QueryImpl spec (StateT S m))
    (n : ℕ) (program : OracleComp spec α) (service : S) :
    m ((Option α × List (Interface.RoutedPacket spec.toPFunctor Unit)) × S) :=
  (fun state => ((result () state, state.transcript), state.service)) <$>
    run impl (serialSchedule () n) (initial program service)

omit [DecidableEq Client] in
/-- The network's complete transcript and result coincide with traced oracle interpretation. -/
theorem serialObservation_eq_loggedRun (impl : QueryImpl spec (StateT S m))
    (n : ℕ) (program : OracleComp spec α) (hbound : IsTotalQueryBound program n)
    (service : S) :
    serialObservation impl n program service =
      (fun out => ((some out.1.1, out.1.2), out.2)) <$> loggedRun impl () program service := by
  rw [serialObservation, run_serialSchedule impl () n program hbound _ rfl rfl]
  simp [initial, result, bind_pure_comp, ← FreeM.pure_eq_pure]

omit [DecidableEq Client] [DecidableEq ι] in
/-- Erasing the standard trace instrumentation recovers the original stateful oracle game. -/
theorem map_loggedRun (impl : QueryImpl spec (StateT S m))
    (id : Client) (program : OracleComp spec α) (service : S) :
    (fun out => (out.1.1, out.2)) <$> loggedRun impl id program service =
      (simulateQ impl program).run service := by
  have h := congrArg (fun action : StateT S m α => action.run service)
    (QueryImpl.fst_map_run_withTraceAppend impl
      (fun a answer => ([⟨id, ⟨a, answer⟩⟩] :
        List (Interface.RoutedPacket spec.toPFunctor Client))) program)
  simpa [loggedRun] using h

omit [DecidableEq Client] in
/-- The result and private state of a completed FIFO run are those of the original oracle game. -/
theorem map_serialObservation (impl : QueryImpl spec (StateT S m))
    (n : ℕ) (program : OracleComp spec α) (hbound : IsTotalQueryBound program n)
    (service : S) :
    (fun out => (out.1.1, out.2)) <$> serialObservation impl n program service =
      (fun out => (some out.1, out.2)) <$> (simulateQ impl program).run service := by
  rw [serialObservation_eq_loggedRun impl n program hbound service,
    ← map_loggedRun impl () program service]
  simp only [Functor.map_map]

end Interaction.UC.OracleNetwork
