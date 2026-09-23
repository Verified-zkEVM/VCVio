/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import VCVio.Interaction.UC.OracleNetwork
public import PolyFun.Interaction.UC.RequestNetwork.Serial
public import VCVio.OracleComp.QueryTracking.QueryBound.Basic

/-!
# Bounded oracle clients over FIFO delivery

The generic serial-completion theorem specializes to oracle programs through the
polynomial free monad. Every permitted query receives three activations, and the final
result, service state, and transcript agree with the ordinary traced oracle fold.
`IsTotalQueryBound` is the oracle facade of the same polynomial roll bound.
-/

public section

namespace Interaction.UC.OracleNetwork

export RequestNetwork (serialSchedule serialSchedule_length loggedRun loggedRun_pure
  loggedRun_liftBind run_serialSchedule_return run_serialSchedule initial result
  serialObservation serialObservation_eq_loggedRun)

open OracleComp PFunctor

variable {Client ι α S : Type} {spec : OracleSpec ι}
  {m : Type → Type} [Monad m] [LawfulMonad m]

/-- Erasing the standard trace instrumentation recovers the original stateful oracle game. -/
theorem map_loggedRun (impl : QueryImpl spec (StateT S m))
    (id : Client) (program : OracleComp spec α) (service : S) :
    (fun out => (out.1.1, out.2)) <$> loggedRun impl id program service =
      (simulateQ impl program).run service := by
  simpa only [simulateQ_def, FreeM.liftMHom_toFun_eq] using
    RequestNetwork.map_loggedRun impl id program service

variable [DecidableEq ι]

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
