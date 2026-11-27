/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module
public import VCVio.OracleComp.QueryTracking.QueryBound.Exact.Sequence
public import VCVio.OracleComp.QueryTracking.QueryBound.Exact.Cost

/-!
# Ordinary clients of exact structural query counts

Independent universe roles, repeated query inputs and a larger runtime exercise the public
counting API. Empty-response and nonempty-Boolean examples distinguish structural certificates
from the costs of an interpreter's reachable executions.
-/

public section
open OracleComp.QueryBound (ExactQueryCount)
open scoped BigOperators
universe i a r

namespace VCVioTest.QueryTracking.Exact

/-- Returning a value needs no identification of index, reply and result universes. -/
theorem pure_at_independent_universes {ι : Type i} {spec : OracleSpec.{i, a} ι}
    {α : Type r} (value : α) : ExactQueryCount (pure value : OracleComp spec α) 0 :=
  ExactQueryCount.pure value

/-- A reply-dependent second query changes the returned value's universe. -/
theorem bind_at_independent_universes :
    let spec : OracleSpec.{1, 2} (ULift.{1} Nat) := fun _ => ULift.{2} Nat
    let program : OracleComp spec (ULift.{3} Nat) :=
      OracleComp.ofFreeM (PFunctor.FreeM.liftBind (P := spec.toPFunctor) (ULift.up 7)
        (fun reply => PFunctor.FreeM.pure (ULift.up (reply.down + 7))))
    let next : ULift.{3} Nat → OracleComp spec (ULift.{4} (Nat × Nat)) :=
      fun value => OracleComp.ofFreeM
        (PFunctor.FreeM.liftBind (P := spec.toPFunctor) (ULift.up value.down)
          (fun reply => PFunctor.FreeM.pure (ULift.up (value.down, reply.down))))
    ExactQueryCount
      (OracleComp.ofFreeM (PFunctor.FreeM.bind (P := spec.toPFunctor)
        (OracleComp.toFreeM program) (fun value => OracleComp.toFreeM (next value)))) 2 := by
  dsimp only
  refine ExactQueryCount.bind.{1, 2, 3, 4} (count := 1) ?_ _ 1 ?_
  · exact ExactQueryCount.query _ _ 0 (fun _ => ExactQueryCount.pure _)
  · intro value
    exact ExactQueryCount.query _ _ 0 (fun _ => ExactQueryCount.pure _)

/-- A nonconstant leaf map changes result universe while preserving the query charge. -/
theorem map_at_independent_universes :
    let spec : OracleSpec.{1, 2} (ULift.{1} Nat) := fun _ => ULift.{2} Nat
    let program : OracleComp spec (ULift.{3} Nat) :=
      OracleComp.ofFreeM (PFunctor.FreeM.liftBind (P := spec.toPFunctor) (ULift.up 7)
        (fun reply => PFunctor.FreeM.pure (ULift.up (reply.down + 7))))
    let f : ULift.{3} Nat → ULift.{4} (Nat × Nat) :=
      fun value => ULift.up (value.down, value.down + 1)
    ExactQueryCount
      (OracleComp.ofFreeM (PFunctor.FreeM.map (P := spec.toPFunctor) f
        (OracleComp.toFreeM program))) 1 := by
  dsimp only
  refine ExactQueryCount.map.{1, 2, 3, 4} (count := 1) ?_ _
  exact ExactQueryCount.query _ _ 0 (fun _ => ExactQueryCount.pure _)

/-- Two computations query the same input and retain two structural query charges. -/
theorem fin_repeated_input :
    let spec : OracleSpec.{1, 2} (ULift.{1} Nat) := fun _ => ULift.{2} Nat
    let f : Fin 2 → OracleComp spec (ULift.{3} Nat) := fun index =>
      OracleComp.ofFreeM (PFunctor.FreeM.liftBind (P := spec.toPFunctor) (ULift.up 7)
        (fun answer => PFunctor.FreeM.pure (ULift.up (answer.down + index.val))))
    ExactQueryCount (Fin.mOfFn 2 f) 2 := by
  let spec : OracleSpec.{1, 2} (ULift.{1} Nat) := fun _ => ULift.{2} Nat
  let f : Fin 2 → OracleComp spec (ULift.{3} Nat) := fun index =>
    OracleComp.ofFreeM (PFunctor.FreeM.liftBind (P := spec.toPFunctor) (ULift.up 7)
      (fun answer => PFunctor.FreeM.pure (ULift.up (answer.down + index.val))))
  change ExactQueryCount (Fin.mOfFn 2 f) 2
  have hcount (index : Fin 2) : ExactQueryCount (f index) 1 :=
    ExactQueryCount.query _ _ 0 (fun answer =>
      ExactQueryCount.pure (ULift.up (answer.down + index.val)))
  simpa only [Fin.sum_univ_succ, Fin.sum_univ_zero, Nat.add_zero] using
    ExactQueryCount.fin_mOfFn.{1, 2, 3} f (fun _ => 1) hcount

/-- Equal items still execute two query steps with independent item and state universes. -/
theorem fold_repeated_item :
    let spec : OracleSpec.{1, 2} (ULift.{1} Nat) := fun _ => ULift.{2} Nat
    let step : ULift.{3} Nat → ULift.{4} Nat → OracleComp spec (ULift.{3} Nat) :=
      fun state item => OracleComp.ofFreeM
        (PFunctor.FreeM.liftBind (P := spec.toPFunctor) (ULift.up 7)
          (fun answer => PFunctor.FreeM.pure
            (ULift.up (state.down + item.down + answer.down))))
    ExactQueryCount
      (([ULift.up 5, ULift.up 5] : List (ULift.{4} Nat)).foldlM step (ULift.up 0)) 2 := by
  let spec : OracleSpec.{1, 2} (ULift.{1} Nat) := fun _ => ULift.{2} Nat
  let step : ULift.{3} Nat → ULift.{4} Nat → OracleComp spec (ULift.{3} Nat) :=
    fun state item => OracleComp.ofFreeM
      (PFunctor.FreeM.liftBind (P := spec.toPFunctor) (ULift.up 7)
        (fun answer => PFunctor.FreeM.pure
          (ULift.up (state.down + item.down + answer.down))))
  change ExactQueryCount
    (([ULift.up 5, ULift.up 5] : List (ULift.{4} Nat)).foldlM step (ULift.up 0)) 2
  have hcount (state : ULift.{3} Nat) (item : ULift.{4} Nat) :
      ExactQueryCount (step state item) 1 :=
    ExactQueryCount.query _ _ 0 (fun answer =>
      ExactQueryCount.pure (ULift.up (state.down + item.down + answer.down)))
  simpa only [List.length_cons, List.length_nil, Nat.add_zero, Nat.mul_one] using
    ExactQueryCount.foldlM.{1, 2, 3, 4}
      ([ULift.up 5, ULift.up 5] : List (ULift.{4} Nat)) step 1 hcount (ULift.up 0)

/-- A large source input delegates to a larger free runtime with nonconstant query replies. -/
theorem unit_cost_index_one_runtime_two :
    let sourceSpec : OracleSpec.{1, 0} (ULift.{1} Nat) := fun _ => Nat
    let runtimeSpec : OracleSpec.{2, 0} (ULift.{2} Nat) := fun _ => Nat
    let impl : QueryImpl sourceSpec (OracleComp runtimeSpec) := fun input =>
      OracleComp.ofFreeM
        (PFunctor.FreeM.liftBind (P := runtimeSpec.toPFunctor) (ULift.up (input.down + 11))
          (fun answer => PFunctor.FreeM.pure (answer + 3)))
    let program : OracleComp sourceSpec Nat :=
      OracleComp.ofFreeM (PFunctor.FreeM.liftBind (P := sourceSpec.toPFunctor) (ULift.up 7)
        (fun answer => PFunctor.FreeM.pure (answer * 2 + 1)))
    AddWriterT.QueryCostExactly (simulateQ impl.withUnitCost program) 1 := by
  dsimp only
  refine ExactQueryCount.queryCostExactly.{1, 2} _ ?_
  exact OracleComp.QueryBound.ExactQueryCount.query _ _ 0
    (fun answer => OracleComp.QueryBound.ExactQueryCount.pure (answer * 2 + 1))


/-- An unanswered query admits distinct structural counts through its empty continuation. -/
theorem empty_reply_counts_not_unique :
    let spec : OracleSpec Unit := fun _ => Empty
    let program : OracleComp spec Unit :=
      OracleComp.ofFreeM (PFunctor.FreeM.liftBind (P := spec.toPFunctor) ()
        (fun answer => nomatch answer))
    ExactQueryCount program 1 ∧ ExactQueryCount program 2 := by
  dsimp only
  constructor
  · exact ExactQueryCount.query (spec := fun (_ : Unit) => Empty)
      () (fun answer => nomatch answer) 0 (fun answer => nomatch answer)
  · exact ExactQueryCount.query (spec := fun (_ : Unit) => Empty)
      () (fun answer => nomatch answer) 1 (fun answer => nomatch answer)

/-- A deterministic Boolean interpreter can have one cost while branch lengths differ. -/
theorem runtime_cost_without_structural_certificate :
    let spec : OracleSpec Unit := fun _ => Bool
    let program : OracleComp spec Unit := do
      let answer ← liftM (spec.query ())
      if answer then do
        let _ ← liftM (spec.query ())
        pure ()
      else pure ()
    let impl : QueryImpl spec Id := fun _ => pure false
    AddWriterT.QueryCostExactly (simulateQ impl.withUnitCost program) 1 ∧
      ¬ ∃ count, ExactQueryCount program count := by
  let spec : OracleSpec Unit := fun _ => Bool
  let program : OracleComp spec Unit := do
    let answer ← liftM (spec.query ())
    if answer then do
      let _ ← liftM (spec.query ())
      pure ()
    else pure ()
  let falseImpl : QueryImpl spec Id := fun _ => pure false
  let trueImpl : QueryImpl spec Id := fun _ => pure true
  change AddWriterT.QueryCostExactly (simulateQ falseImpl.withUnitCost program) 1 ∧
    ¬ ∃ count, ExactQueryCount program count
  have falseRun : (simulateQ falseImpl.withUnitCost program).run =
      ((), Multiplicative.ofAdd 1) := by
    simp [program, falseImpl, simulateQ_bind, QueryImpl.withUnitCost_apply,
      WriterT.run_bind, AddWriterT.run_addTell]
    rfl
  have trueRun : (simulateQ trueImpl.withUnitCost program).run =
      ((), Multiplicative.ofAdd 2) := by
    simp [program, trueImpl, simulateQ_bind, QueryImpl.withUnitCost_apply,
      WriterT.run_bind, AddWriterT.run_addTell]
    rfl
  have falseMem : ((), Multiplicative.ofAdd 1) ∈
      support (simulateQ falseImpl.withUnitCost program).run := by
    rw [falseRun]
    change ((), Multiplicative.ofAdd 1) ∈ support
      (pure ((), Multiplicative.ofAdd 1) : Id (Unit × Multiplicative Nat))
    simp only [support_pure, Set.mem_singleton_iff]
  have trueMem : ((), Multiplicative.ofAdd 2) ∈
      support (simulateQ trueImpl.withUnitCost program).run := by
    rw [trueRun]
    change ((), Multiplicative.ofAdd 2) ∈ support
      (pure ((), Multiplicative.ofAdd 2) : Id (Unit × Multiplicative Nat))
    simp only [support_pure, Set.mem_singleton_iff]
  constructor
  · constructor <;> intro result hresult
    all_goals
      rw [falseRun] at hresult
      change result ∈ support
        (pure ((), Multiplicative.ofAdd 1) : Id (Unit × Multiplicative Nat)) at hresult
      rw [support_pure, Set.mem_singleton_iff] at hresult
      subst result
      exact Nat.le_refl 1
  · rintro ⟨count, hcount⟩
    have falseCost := ExactQueryCount.queryCostExactly falseImpl hcount
    have trueCost := ExactQueryCount.queryCostExactly trueImpl hcount
    have atMostOne : count ≤ 1 := falseCost.toBelow _ falseMem
    have atLeastTwo : 2 ≤ count := trueCost.toAbove _ trueMem
    omega

end VCVioTest.QueryTracking.Exact
