/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module

public import ForwardingBudgetGuard
public import VCVio.OracleComp.SimSemantics.StateT.Basic
public import VCVio.OracleComp.SimSemantics.StateT.StateProjection

/-! # Interpreting a guarded free program

A weighted guard can be applied before or after a stateful interpretation. The joint law
retains raw output, physical cache, both counters and the absorbing abort flag. Only the
free forwarder's unit state is erased by the explicit tuple permutation.
-/

@[expose] public section

open OracleComp OracleSpec

universe v

namespace QueryImpl

/-- Interpreting the free guarded program preserves the complete guarded state and output. -/
theorem map_run_simulateQ_guardQueryBudget_free_eq
    {ι α Cache : Type} {spec : OracleSpec.{0, 0} ι}
    {m : Type → Type v} [Monad m] [LawfulMonad m]
    (caps : Nat × Nat) (cost : spec.Domain → Nat × Nat)
    (handler : QueryImpl spec (StateT Cache m))
    (fallback : (input : spec.Domain) → spec.Range input)
    (program : OracleComp spec α)
    (initialCache : Cache) (initialCounts : Nat × Nat) (initialAborted : Bool) :
    let forwarder : QueryImpl spec (StateT PUnit (OracleComp spec)) :=
      (QueryImpl.id' spec).liftTarget (StateT PUnit (OracleComp spec))
    let freeGuarded : OracleComp spec (α × (PUnit × ((Nat × Nat) × Bool))) :=
      (simulateQ (guardQueryBudget caps cost forwarder fallback) program).run
        (PUnit.unit, (initialCounts, initialAborted))
    (fun result : (α × (PUnit × ((Nat × Nat) × Bool))) × Cache =>
      (result.1.1, (result.2, result.1.2.2))) <$>
      (simulateQ handler freeGuarded).run initialCache =
        (simulateQ (guardQueryBudget caps cost handler fallback) program).run
          (initialCache, (initialCounts, initialAborted)) := by
  dsimp only
  let forwarder : QueryImpl spec (StateT PUnit (OracleComp spec)) :=
    (QueryImpl.id' spec).liftTarget (StateT PUnit (OracleComp spec))
  let inner := guardQueryBudget caps cost forwarder fallback
  let project : ((PUnit × ((Nat × Nat) × Bool)) × Cache) →
      Cache × ((Nat × Nat) × Bool) := fun state => (state.2, state.1.2)
  have hstep : ∀ input state,
      Prod.map id project <$>
        (((handler.mapStateTBase inner).flattenStateT input).run state) =
        (guardQueryBudget caps cost handler fallback input).run (project state) := by
    intro input state
    rcases state with ⟨⟨token, counts, flag⟩, cache⟩
    cases flag with
    | false =>
      by_cases hcap : counts.1 + (cost input).1 ≤ caps.1 ∧
          counts.2 + (cost input).2 ≤ caps.2
      · simp [flattenStateT_mapStateTBase_apply_run, inner, guardQueryBudget, project,
          hcap, forwarder, id'_apply, Functor.map_map]
      · simp [flattenStateT_mapStateTBase_apply_run, inner, guardQueryBudget, project, hcap]
    | true =>
      simp [flattenStateT_mapStateTBase_apply_run, inner, guardQueryBudget, project]
  have hfold := map_run_simulateQ_eq_of_query_map_eq
    (handler.mapStateTBase inner).flattenStateT
    (guardQueryBudget caps cost handler fallback) project hstep program
    ((PUnit.unit, (initialCounts, initialAborted)), initialCache)
  change (fun result : (α × (PUnit × ((Nat × Nat) × Bool))) × Cache =>
      (result.1.1, (result.2, result.1.2.2))) <$>
      (simulateQ handler ((simulateQ inner program).run
        (PUnit.unit, (initialCounts, initialAborted)))).run initialCache = _
  rw [simulateQ_mapStateTBase_run_eq_map_flattenStateT]
  have hproject : Prod.map id project =
      (fun result : α × ((PUnit × ((Nat × Nat) × Bool)) × Cache) =>
        (result.1, (result.2.2, result.2.1.2))) := by
    funext result
    rfl
  rw [hproject] at hfold
  simpa only [Functor.map_map, Function.comp_def] using hfold

#check @map_run_simulateQ_guardQueryBudget_free_eq
#print axioms map_run_simulateQ_guardQueryBudget_free_eq

end QueryImpl
