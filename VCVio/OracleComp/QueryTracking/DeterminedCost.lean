/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module

public import VCVio.OracleComp.QueryTracking.CostModel

/-!
# Complete-path costs with determined responses

When a deterministic handler gives the only inhabitant of every response type, the free
instrumented computation has exactly one completed path: the one `PFunctor.FreeM.Path.ofHandler`
picks, whose output and charge the handler records (`QueryImpl.run_simulateQ_withAddCost_id`).
Its worst-case cost bound is then the cost recorded by running that handler once. Certified
instruction sets, whose response types are singleton subtypes, have this property. Without it, a
worst-case bound still bounds the cost recorded by any deterministic handler, since that execution
is one path.

A bound on declared query costs does not account for computation inside the handler.
-/

public section

open OracleComp OracleSpec

namespace OracleComp

variable {ι ω A : Type} {spec : OracleSpec ι} [AddCommMonoid ω]

/-- A deterministic handler's execution, with its recorded cost, is one path of the instrumented
computation: the path `PFunctor.FreeM.Path.ofHandler` picks. -/
theorem run_withAddCost_mem_support_costDist (answer : QueryImpl spec Id)
    (oa : OracleComp spec A) (cm : CostModel spec ω) :
    (simulateQ (answer.withAddCost cm.queryCost) oa).run ∈ support (costDist oa cm) := by
  rw [support_costDist_eq_range_path, QueryImpl.run_simulateQ_withAddCost_id]
  exact ⟨_, rfl⟩

/-- A worst-case cost bound bounds the cost recorded by any deterministic handler. -/
theorem worstCaseCostBound_runAdd_withAddCost_le [Preorder ω] {oa : OracleComp spec A}
    {cm : CostModel spec ω} {B : ω} (h : WorstCaseCostBound oa cm B)
    (answer : QueryImpl spec Id) :
    (simulateQ (answer.withAddCost cm.queryCost) oa).runAdd.2 ≤ B :=
  (worstCaseCostBound_iff_support_bound oa cm B).mp h _
    (run_withAddCost_mem_support_costDist answer oa cm)

/-- If every response equals the handler's answer, the instrumented computation has the handler's
execution as its only path. -/
theorem support_costDist_of_forall_eq_answer (answer : QueryImpl spec Id)
    (hanswer : ∀ t (u : spec.Range t), u = answer t) (oa : OracleComp spec A)
    (cm : CostModel spec ω) :
    support (costDist oa cm) = {(simulateQ (answer.withAddCost cm.queryCost) oa).run} := by
  have : ∀ t, Subsingleton (spec.toPFunctor.B t) :=
    fun t => ⟨fun u v => (hanswer t u).trans (hanswer t v).symm⟩
  let _ : Unique (PFunctor.FreeM.Path oa) :=
    { default := PFunctor.FreeM.Path.ofHandler (fun t => (answer t).run) oa
      uniq := fun _ => Subsingleton.elim _ _ }
  rw [support_costDist_eq_range_path, QueryImpl.run_simulateQ_withAddCost_id]
  exact Set.range_unique

/-- If every response equals the handler's answer, a worst-case cost bound is exactly a bound on
the cost of the handler's execution. -/
theorem worstCaseCostBound_iff_of_forall_eq_answer [Preorder ω] (answer : QueryImpl spec Id)
    (hanswer : ∀ t (u : spec.Range t), u = answer t) (oa : OracleComp spec A)
    (cm : CostModel spec ω) (B : ω) :
    WorstCaseCostBound oa cm B ↔
      (simulateQ (answer.withAddCost cm.queryCost) oa).runAdd.2 ≤ B := by
  have : ∀ t, Subsingleton (spec.toPFunctor.B t) :=
    fun t => ⟨fun u v => (hanswer t u).trans (hanswer t v).symm⟩
  rw [worstCaseCostBound_iff_forall_charge_le,
    PFunctor.FreeM.Path.forall_charge_le_iff_ofHandler (fun t => (answer t).run),
    AddWriterT.runAdd, QueryImpl.run_simulateQ_withAddCost_id]
  rfl

end OracleComp
