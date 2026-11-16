/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module

public import VCVio.OracleComp.QueryTracking.MeasuredProgram
public import VCVio.OracleComp.QueryTracking.CostModel.Simulation

/-!
# Composition of measured programs

Composing two measured programs executes the inner instruction program and then the outer
instruction program on its actual result. Their queries are embedded in disjoint indexed
specifications, retaining each instruction's view and charge. Neither program is executed while
constructing the input view. The outer view is computed, uncharged, on the actual intermediate
result during execution. Their worst-case weighted budgets add, uniformly over all permitted
responses; this is not a complete execution-cost or expected-cost composition theorem.

Input precomposition changes only the uncharged view. The accounting boundary remains that of
`MeasuredProgram`: view construction, handler evaluation and pure computation are not charged.
-/

public section

open OracleSpec

namespace OracleComp

namespace MeasuredProgram

variable {A B C I ω : Type}

/-- Precompose the input through the program's uncharged view. -/
@[expose] def contramap (M : MeasuredProgram A B ω) (f : I → A) : MeasuredProgram I B ω where
  View := M.View
  view := M.view ∘ f
  Op := M.Op
  spec := M.spec
  program := M.program
  answer := M.answer
  cost := M.cost

/-- Input precomposition runs the original program at the transformed input. -/
theorem run_contramap (M : MeasuredProgram A B ω) (f : I → A) (input : I) :
    (M.contramap f).run input = M.run (f input) := rfl

/-- Input precomposition preserves realization of the corresponding composed function. -/
theorem Realizes.contramap {M : MeasuredProgram A B ω} {g : A → B}
    (h : M.Realizes g) (f : I → A) : (M.contramap f).Realizes (g ∘ f) :=
  fun input => h (f input)

/-- Input precomposition preserves the bound on every program view. -/
theorem CostAtMost.contramap [AddCommMonoid ω] [Preorder ω]
    {M : MeasuredProgram A B ω} {budget : ω} (h : M.CostAtMost budget) (f : I → A) :
    (M.contramap f).CostAtMost budget := h

/-- Execute the inner program and then the outer program on its result, retaining both programs'
instruction charges. The outer view is computed without charge from the inner result. The order
agrees with function composition. -/
@[expose] def comp (outer : MeasuredProgram B C ω) (inner : MeasuredProgram A B ω) :
    MeasuredProgram A C ω where
  View := inner.View
  view := inner.view
  Op := ((v : inner.View) × (inner.spec v).Domain) ⊕
    ((v : outer.View) × (outer.spec v).Domain)
  spec _ := OracleSpec.sigma inner.spec + OracleSpec.sigma outer.spec
  program v := do
    let result ← simulateQ
      (fun query => liftM ((OracleSpec.sigma inner.spec + OracleSpec.sigma outer.spec).query
        (.inl ⟨v, query⟩))) (inner.program v)
    simulateQ
      (fun query => liftM ((OracleSpec.sigma inner.spec + OracleSpec.sigma outer.spec).query
        (.inr ⟨outer.view result, query⟩))) (outer.program (outer.view result))
  answer _
    | .inl ⟨v, query⟩ => inner.answer v query
    | .inr ⟨v, query⟩ => outer.answer v query
  cost
    | .inl ⟨_, query⟩ => inner.cost query
    | .inr ⟨_, query⟩ => outer.cost query

/-- Running the composed instruction program is composition of the two deterministic runs. -/
theorem run_comp (outer : MeasuredProgram B C ω) (inner : MeasuredProgram A B ω) (input : A) :
    (outer.comp inner).run input = outer.run (inner.run input) := by
  unfold run comp evalWithAnswerFn
  simp only [simulateQ_bind]
  have first : ∀ v : inner.View, simulateQ
      ((fun t => match t with
        | .inl ⟨v, query⟩ => inner.answer v query
        | .inr ⟨v, query⟩ => outer.answer v query) :
        QueryImpl (OracleSpec.sigma inner.spec + OracleSpec.sigma outer.spec) Id)
      (simulateQ
        (fun query => liftM ((OracleSpec.sigma inner.spec + OracleSpec.sigma outer.spec).query
          (.inl ⟨v, query⟩))) (inner.program v)) =
      simulateQ (inner.answer v) (inner.program v) := by
    intro v
    exact QueryImpl.simulateQ_simulateQ_eq_of_apply (fun _ => rfl) _
  rw [first]
  exact QueryImpl.simulateQ_simulateQ_eq_of_apply (fun _ => rfl) _

/-- The writer-instrumented composition executes both original instrumented programs, including
all their declared charges, and passes the actual inner result to the outer program. -/
theorem simulateQ_withAddCost_comp [AddCommMonoid ω]
    (outer : MeasuredProgram B C ω) (inner : MeasuredProgram A B ω) (v : inner.View) :
    simulateQ (((outer.comp inner).answer v).withAddCost (outer.comp inner).cost)
      ((outer.comp inner).program v) = (do
        let result ← simulateQ ((inner.answer v).withAddCost inner.cost) (inner.program v)
        simulateQ ((outer.answer (outer.view result)).withAddCost outer.cost)
          (outer.program (outer.view result))) := by
  let handler := ((outer.comp inner).answer v).withAddCost (outer.comp inner).cost
  let left (view : inner.View) :
      QueryImpl (inner.spec view) (OracleComp ((outer.comp inner).spec v)) :=
    fun query => liftM ((outer.comp inner).spec v |>.query (.inl ⟨view, query⟩))
  let right (result : B) :
      QueryImpl (outer.spec (outer.view result)) (OracleComp ((outer.comp inner).spec v)) :=
    fun query => liftM ((outer.comp inner).spec v |>.query (.inr ⟨outer.view result, query⟩))
  have first : simulateQ handler (simulateQ (left v) (inner.program v)) =
      simulateQ ((inner.answer v).withAddCost inner.cost) (inner.program v) :=
    QueryImpl.simulateQ_simulateQ_eq_of_apply (fun query =>
      (simulateQ_spec_query handler (.inl ⟨v, query⟩)).trans
        ((QueryImpl.withAddCost_apply _ _ _).trans
          (QueryImpl.withAddCost_apply (inner.answer v) inner.cost query).symm)) _
  have second (result : B) :
      simulateQ handler (simulateQ (right result) (outer.program (outer.view result))) =
      simulateQ ((outer.answer (outer.view result)).withAddCost outer.cost)
        (outer.program (outer.view result)) :=
    QueryImpl.simulateQ_simulateQ_eq_of_apply (fun query =>
      (simulateQ_spec_query handler (.inr ⟨outer.view result, query⟩)).trans
        ((QueryImpl.withAddCost_apply _ _ _).trans
          (QueryImpl.withAddCost_apply
            (outer.answer (outer.view result)) outer.cost query).symm)) _
  exact (simulateQ_bind handler (simulateQ (left v) (inner.program v))
    (fun result => simulateQ (right result) (outer.program (outer.view result)))).trans
      ((congrArg (fun program => program >>= fun result =>
        simulateQ handler (simulateQ (right result) (outer.program (outer.view result))))
          first).trans (bind_congr second))

/-- Composition realizes composition of the functions computed by its two programs. -/
theorem Realizes.comp {outer : MeasuredProgram B C ω} {inner : MeasuredProgram A B ω}
    {f : A → B} {g : B → C} (hg : outer.Realizes g) (hf : inner.Realizes f) :
    (outer.comp inner).Realizes (g ∘ f) := by
  intro input
  rw [run_comp, ← hf input]
  exact hg (f input)

/-- Uniform bounds for the two instruction programs add under their actual composition. -/
theorem CostAtMost.comp [AddCommMonoid ω] [Preorder ω] [IsOrderedAddMonoid ω]
    {outer : MeasuredProgram B C ω} {inner : MeasuredProgram A B ω}
    {outerBudget innerBudget : ω} (ho : outer.CostAtMost outerBudget)
    (hi : inner.CostAtMost innerBudget) :
    (outer.comp inner).CostAtMost (innerBudget + outerBudget) := by
  intro v
  apply WorstCaseCostBound.bind
  · exact (hi v).simulateQ _ fun _ => worstCaseCostBound_query _ _
  · intro result
    exact (ho (outer.view result)).simulateQ _ fun _ => worstCaseCostBound_query _ _

end MeasuredProgram

namespace BudgetedProgram

variable {A B C I ω : Type} [AddCommMonoid ω]

/-- Precompose a budgeted program through its uncharged input view. -/
@[expose] def contramap [Preorder ω] {f : A → B} (M : BudgetedProgram f ω) (g : I → A) :
    BudgetedProgram (f ∘ g) ω where
  program := M.program.contramap g
  budget := M.budget
  realizes := M.realizes.contramap g
  costAtMost := M.costAtMost.contramap g

/-- Compose budgeted instruction programs, adding their declared bounds. -/
@[expose] def comp [Preorder ω] [IsOrderedAddMonoid ω] {f : A → B} {g : B → C}
    (outer : BudgetedProgram g ω) (inner : BudgetedProgram f ω) :
    BudgetedProgram (g ∘ f) ω where
  program := outer.program.comp inner.program
  budget := inner.budget + outer.budget
  realizes := outer.realizes.comp inner.realizes
  costAtMost := outer.costAtMost.comp inner.costAtMost

end BudgetedProgram

end OracleComp
