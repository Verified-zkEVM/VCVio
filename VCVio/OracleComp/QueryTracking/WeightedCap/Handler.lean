/-
Copyright (c) 2026 VCVio Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: VCVio Contributors
-/

module

public import VCVio.OracleComp.QueryTracking.WeightedCap
public import VCVio.OracleComp.SimSemantics.OptionT.Basic

/-!
# A query handler for a weighted cap

The handler tests the remaining budget before issuing each query.
Its state records the remainder at a normal return or a refusal.
Forgetting that remainder recovers the syntactically capped caller under any interpretation.
-/

public section
namespace OracleComp.WeightedCap

open OracleSpec

variable {ι α : Type} {spec : OracleSpec ι} {m : Type → Type} [Monad m] [LawfulMonad m]

/-- Stop before an unaffordable query, keeping all earlier effects. -/
@[expose] def guard (weight : ι → Nat) (impl : QueryImpl spec m) :
    QueryImpl spec (OptionT (StateT Nat m)) := fun t => OptionT.mk (StateT.mk fun remaining =>
  if weight t ≤ remaining then (fun a => (some a, remaining - weight t)) <$> impl t
  else pure (none, remaining))

/-- Forgetting the remaining budget recovers the syntactically capped source. -/
theorem run_guard (weight : ι → Nat) (impl : QueryImpl spec m) (oa : OracleComp spec α)
    (remaining : Nat) :
    Prod.fst <$> ((simulateQ (guard weight impl) oa).run).run remaining =
      simulateQ impl (capCompOpt weight remaining oa) := by
  induction oa using OracleComp.inductionOn generalizing remaining with
  | pure a => simp [capCompOpt_pure]
  | query_bind t k ih =>
    rw [capCompOpt_query_bind]
    by_cases fits : weight t ≤ remaining
    · simp only [ite_eq_left fits, simulateQ_bind, simulateQ_spec_query, OptionT.run_bind,
        Option.elimM,
        StateT.run_bind, guard, OptionT.run_mk, StateT.run_mk, map_bind, bind_map_left]
      exact bind_congr (fun a => ih a _)
    · simp [fits, guard, OptionT.run_bind, Option.elimM]

end OracleComp.WeightedCap
