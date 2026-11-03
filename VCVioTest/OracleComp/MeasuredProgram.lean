/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module

public import VCVio.OracleComp.QueryTracking.MeasuredProgram.Composition

/-!
# Measured program composition

The programs below have the same original instruction tag but distinct views and profile
coordinates. Composition must execute the first instruction before preparing the second view,
retain both charges and pass the first result to the second program. A separate nondeterministic
example shows that a cheap deterministic handler does not establish a worst-case bound. Abstract
preorders, signed refunds and reversed orders exercise the generic weighted scope, and empty
carriers require no chosen witness.
-/

public section

open OracleComp OracleSpec

namespace VCVioTest.OracleComp.MeasuredProgram

/-- Two separately observed instruction coordinates. -/
abbrev Profile := Bool → Nat

/-- A certified addition instruction on two input values. -/
@[expose] def addSpec (values : Nat × Nat) : OracleSpec Unit :=
  fun _ => {result : Nat // result = values.1 + values.2}

/-- One addition charged to the selected profile coordinate. -/
@[expose] def addProgram {Input : Type} (view : Input → Nat × Nat) (coordinate : Bool) :
    MeasuredProgram Input Nat Profile where
  View := Nat × Nat
  view := view
  Op := Unit
  spec := addSpec
  program values := do
    let result ← liftM ((addSpec values).query ())
    return result.val
  answer values := fun _ => pure ⟨values.1 + values.2, rfl⟩
  cost _ kind := if kind = coordinate then 1 else 0

/-- The program returns the sum of the two values supplied by its view. -/
theorem addProgram_realizes {Input : Type} (view : Input → Nat × Nat) (coordinate : Bool) :
    (addProgram view coordinate).Realizes (fun input => (view input).1 + (view input).2) :=
  fun _ => rfl

/-- The one certified addition has one unit in its selected coordinate. -/
theorem addProgram_costAtMost {Input : Type} (view : Input → Nat × Nat) (coordinate : Bool) :
    (addProgram view coordinate).CostAtMost (fun kind => if kind = coordinate then 1 else 0) :=
  MeasuredProgram.costAtMost_of_forall_eq_answer _ _ (fun _ _ result => Subtype.ext result.2)
    (fun _ => by
      simp [addProgram, QueryImpl.withAddCost_apply]
      rfl)

/-- The inner program increments its input. -/
@[expose] def increment : MeasuredProgram Nat Nat Profile :=
  addProgram (fun input => (input, 1)) false

/-- The outer program doubles its actual input. -/
@[expose] def double : MeasuredProgram Nat Nat Profile :=
  addProgram (fun input => (input, input)) true

/-- Execute the increment and then double its result. -/
@[expose] def composed : MeasuredProgram Nat Nat Profile := double.comp increment

example : composed.Realizes (fun input => (input + 1) + (input + 1)) :=
  (addProgram_realizes _ _).comp (addProgram_realizes _ _)

example : composed.CostAtMost (fun _ => 1) := by
  apply (MeasuredProgram.CostAtMost.comp
    (addProgram_costAtMost _ _) (addProgram_costAtMost _ _)).mono
  intro coordinate
  cases coordinate <;> exact le_rfl

/-- Observe the actual deterministic run and both instruction charges. -/
def observations (input : Nat) : Nat × Nat × Nat :=
  let view := composed.view input
  let result := (simulateQ ((composed.answer view).withAddCost composed.cost)
    (composed.program view)).runAdd.run
  (result.1, result.2 false, result.2 true)

example (input : Nat) : observations input = ((input + 1) + (input + 1), 1, 1) := by
  dsimp only [observations, composed]
  rw [MeasuredProgram.simulateQ_withAddCost_comp double increment
    ((double.comp increment).view input)]
  simp [increment, double, addProgram, QueryImpl.withAddCost_apply]
  rfl

example (input : Nat × Bool) :
    (composed.contramap Prod.fst).run input = composed.run input.1 := rfl

example {Input Result : Type} (f : Input → Result) :
    (BudgetedProgram.ofFun (ω := Nat) f).budget = 0 := rfl

/-- Weighted composition needs monotone addition, but not antisymmetry of the cost order. -/
example {A B C ω : Type} [AddCommMonoid ω] [Preorder ω] [IsOrderedAddMonoid ω]
    {inner : MeasuredProgram A B ω} {outer : MeasuredProgram B C ω}
    {innerBudget outerBudget : ω} (hi : inner.CostAtMost innerBudget)
    (ho : outer.CostAtMost outerBudget) :
    (outer.comp inner).CostAtMost (innerBudget + outerBudget) := ho.comp hi

example {A B C ω : Type} [AddCommMonoid ω] [Preorder ω] [IsOrderedAddMonoid ω]
    {f : A → B} {g : B → C} (inner : BudgetedProgram f ω) (outer : BudgetedProgram g ω) :
    (outer.comp inner).budget = inner.budget + outer.budget := rfl

/-- Writer instrumentation retains the result even with signed weights and arbitrary responses. -/
example {Input Result ω : Type} [AddMonoid ω] (program : MeasuredProgram Input Result ω)
    (input : Input) :
    (simulateQ ((program.answer (program.view input)).withAddCost program.cost)
      (program.program (program.view input))).runAdd.1 = program.run input :=
  program.runAdd_fst_eq_run input

/-- Empty result carriers need no chosen witness when the input is empty too. -/
example : ((BudgetedProgram.ofFun (ω := Nat) (id : Empty → Empty)).comp
    (BudgetedProgram.ofFun (ω := Nat) (id : Empty → Empty))).budget = 0 := rfl

/-- An instruction with a single response. -/
abbrev unitSignature : OracleSpec Unit := fun _ => Unit

/-- One instruction with an arbitrary weight; its handler returns the only possible response. -/
@[expose] def weightedInstruction {ω : Type} (weight : ω) : MeasuredProgram Unit Unit ω where
  View := Unit
  view := id
  Op := Unit
  spec _ := unitSignature
  program _ := liftM (unitSignature.query ())
  answer _ _ := pure ()
  cost _ := weight

/-- The one instruction has its declared weight in any cost preorder. -/
theorem weightedInstruction_costAtMost {ω : Type} [AddCommMonoid ω] [Preorder ω] (weight : ω) :
    (weightedInstruction weight).CostAtMost weight :=
  MeasuredProgram.costAtMost_of_forall_eq_answer _ _
    (fun _ _ result => Subsingleton.elim (α := Unit) result ())
    (fun _ => by
      simp [weightedInstruction, QueryImpl.withAddCost_apply]
      rfl)

/-- Signed weights may refund an earlier charge; a zero weighted budget need not mean no work. -/
example : ((weightedInstruction (-1 : Int)).comp (weightedInstruction 1)).CostAtMost 0 := by
  simpa using (weightedInstruction_costAtMost (-1 : Int)).comp
    (weightedInstruction_costAtMost 1)

/-- Reversing the cost order turns an upper bound into a lower bound on natural counts. -/
example : (weightedInstruction (1 : Natᵒᵈ)).CostAtMost 0 :=
  (weightedInstruction_costAtMost (1 : Natᵒᵈ)).mono (Nat.zero_le 1)

/-- A response may choose whether the program requests a second instruction. -/
abbrev choiceSpec : OracleSpec Unit := fun _ => Bool

/-- One instruction on one response branch and two on the other. -/
def choiceProgram : OracleComp choiceSpec Unit := do
  let choice ← choiceSpec.query ()
  if choice then
    let _ ← choiceSpec.query ()
    pure ()
  else
    pure ()

/-- A deterministic handler selecting the shorter response branch. -/
def shortBranch : QueryImpl choiceSpec Id := fun _ => pure false

/-- A deterministic handler selecting the longer response branch. -/
def longBranch : QueryImpl choiceSpec Id := fun _ => pure true

example :
    (simulateQ (shortBranch.withAddCost (fun _ => (1 : Nat)))
      choiceProgram).runAdd.2 = 1 := by
  simp [choiceProgram, shortBranch, QueryImpl.withAddCost_apply]
  rfl

example : ¬ WorstCaseCostBound choiceProgram (⟨fun _ => 1⟩ : CostModel choiceSpec Nat) 1 := by
  intro bound
  have recorded := worstCaseCostBound_runAdd_withAddCost_le bound
    longBranch
  have cost :
      (simulateQ (longBranch.withAddCost (fun _ => (1 : Nat))) choiceProgram).runAdd.2 = 2 := by
    simp [choiceProgram, longBranch, QueryImpl.withAddCost_apply]
    rfl
  rw [cost] at recorded
  exact Nat.not_succ_le_self 1 recorded

/-- Run the composed programs and observe both charges and response-dependent instruction counts. -/
def run : IO Unit := do
  for input in [0, 3, 19] do
    let result := observations input
    unless result == ((input + 1) + (input + 1), 1, 1) do
      throw (IO.userError s!"Unexpected measured composition result at {input}: {result}")
  let choiceCost := fun answer : QueryImpl choiceSpec Id =>
    (simulateQ (answer.withAddCost (fun _ => (1 : Nat))) choiceProgram).runAdd.2
  unless choiceCost shortBranch == 1 && choiceCost longBranch == 2 do
    throw (IO.userError "Measured instruction counts lost the response-dependent branch")
  IO.println "Measured composition preserves intermediate results and both instruction profiles."

end VCVioTest.OracleComp.MeasuredProgram
