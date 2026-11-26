/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module

public import PolyFun.PFunctor.Free.Cost.Measured
public import VCVio.OracleComp.QueryTracking.DeterminedCost

/-!
# Measured programs as oracle computations

`PFunctor.FreeM.MeasuredProgram` computes a function by running a free program on an uncharged view
of its input. Deterministic answers resolve the program's operations, and each operation has a
price in a cost type. Its interface at a view is an `OracleSpec`, and its program is an
`OracleComp`. This file relates that structure to the oracle-cost API.

* `queryImpl`: the answers of a view as a `QueryImpl` into `Id`.
* `run_eq_evalWithAnswerFn`: the run is `evalWithAnswerFn` of the view's answers.
* `costAtMost_iff_worstCaseCostBound` and `CostAtMost.worstCaseCostBound`: the all-path budget is
  `WorstCaseCostBound` on every view.
* `runAdd_fst_eq_run` and `CostAtMost.runAdd_le`: the `QueryImpl.withAddCost` run of the answers
  returns the run's result, and a budget bounds the charge it records.
* `costAtMost_of_runAdd_le`: if the answers are the only responses, the recorded charge
  bounds every path.
* `simulateQ_withAddCost_comp`: the instrumented run of a composite is the instrumented run of the
  inner program, then of the outer program on its actual result.

Only the operations are charged. Computing the view, the size and encoding of the view,
evaluating the answers, the pure code between operations and the bit complexity of values are not.
Each instance must state what its view and its answers leave uncharged. The prices and the cost
order form the declared accounting model. A budget bounds the declared charges. It is not a
running-time bound.
Signed prices may cancel, and a reversed order makes an upper bound a lower bound. Idempotent or
saturating addition may collapse repeated positive charges, so a canonically ordered monoid alone is
not a counter. An operation count needs counting arithmetic and a charge table, such as natural
number vectors with unit charges. With infinitely many coordinates, a pointwise budget can permit
arbitrarily many charges of distinct kinds. A uniform scalar total then needs a fixed finite
coordinate set, or a separately proved bounded or summable budget. Finite support of each run is not
enough.
-/

public section

open OracleSpec OracleComp

namespace PFunctor.FreeM.MeasuredProgram

variable {Input Result ω : Type} (M : MeasuredProgram Input Result ω)

/-- The answers of view `v` as a deterministic query implementation. -/
@[expose] def queryImpl (v : M.View) : QueryImpl (M.spec v) Id :=
  QueryImpl.ofFn (M.answer v)

/-- The query implementation of view `v` returns `M.answer v op` on operation `op`. -/
@[simp]
theorem queryImpl_apply (v : M.View) (op : M.Op) : M.queryImpl v op = pure (M.answer v op) :=
  rfl

/-- The run is the evaluation of the view's program with the view's answers. -/
theorem run_eq_evalWithAnswerFn (input : Input) :
    M.run input = evalWithAnswerFn (M.queryImpl (M.view input)) (M.program (M.view input)) :=
  rfl

/-- The all-path budget is a worst-case cost bound on the program of every view. -/
theorem costAtMost_iff_worstCaseCostBound [AddCommMonoid ω] [Preorder ω] (budget : ω) :
    M.CostAtMost budget ↔ ∀ v, WorstCaseCostBound (M.program v) ⟨M.cost⟩ budget := by
  simp only [worstCaseCostBound_iff_forall_charge_le]
  rfl

/-- The additively instrumented run of the answers returns the run's result. No cost order is
needed. -/
theorem runAdd_fst_eq_run [AddMonoid ω] (input : Input) :
    (simulateQ ((M.queryImpl (M.view input)).withAddCost M.cost)
      (M.program (M.view input))).runAdd.1 = M.run input :=
  congrArg Id.run (QueryImpl.fst_map_run_withCost (M.queryImpl (M.view input))
    (fun op => Multiplicative.ofAdd (M.cost op)) (M.program (M.view input)))

variable {M} in
/-- A budget is a worst-case cost bound on the program of each view. -/
theorem CostAtMost.worstCaseCostBound [AddCommMonoid ω] [Preorder ω] {budget : ω}
    (h : M.CostAtMost budget) (v : M.View) :
    WorstCaseCostBound (M.program v) ⟨M.cost⟩ budget :=
  (M.costAtMost_iff_worstCaseCostBound budget).mp h v

variable {M} in
/-- A budget bounds the charge that the instrumented run of any view's answers records. -/
theorem CostAtMost.runAdd_le [AddCommMonoid ω] [Preorder ω] {budget : ω}
    (h : M.CostAtMost budget) (v : M.View) :
    (simulateQ ((M.queryImpl v).withAddCost M.cost) (M.program v)).runAdd.2 ≤ budget :=
  worstCaseCostBound_runAdd_withAddCost_le (h.worstCaseCostBound v) (M.queryImpl v)

/-- If the answers are the only responses, the charge that the instrumented run records on every
view bounds every path. -/
theorem costAtMost_of_runAdd_le [AddCommMonoid ω] [Preorder ω] (budget : ω)
    (hanswer : ∀ v op (u : M.spec v op), u = M.answer v op)
    (hcost : ∀ v, (simulateQ ((M.queryImpl v).withAddCost M.cost) (M.program v)).runAdd.2 ≤
      budget) :
    M.CostAtMost budget :=
  (M.costAtMost_iff_worstCaseCostBound budget).mpr fun v ↦
    (worstCaseCostBound_iff_of_forall_eq_answer (M.queryImpl v) (hanswer v) (M.program v)
      ⟨M.cost⟩ budget).mpr (hcost v)

/-- The instrumented run of a composite runs the instrumented inner program, then the
instrumented outer program on the view of its actual result. Both price lists are kept. -/
theorem simulateQ_withAddCost_comp {A B C : Type} [AddMonoid ω]
    (outer : MeasuredProgram B C ω) (inner : MeasuredProgram A B ω) (v : inner.View) :
    simulateQ (((outer.comp inner).queryImpl v).withAddCost (outer.comp inner).cost)
      ((outer.comp inner).program v) = (do
        let result ← simulateQ ((inner.queryImpl v).withAddCost inner.cost) (inner.program v)
        simulateQ ((outer.queryImpl (outer.view result)).withAddCost outer.cost)
          (outer.program (outer.view result))) := by
  simp only [comp, simulateQ, FreeM.liftM_bind, FreeM.liftM_mapLens]
  congr 1
  · congr 1
    funext op
    simp only [innerLens, QueryImpl.withAddCost_apply]
    exact id_map' _
  · funext result
    congr 1
    funext op
    simp only [outerLens, QueryImpl.withAddCost_apply]
    exact id_map' _

end PFunctor.FreeM.MeasuredProgram
