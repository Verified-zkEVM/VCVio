/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module
public import ToMathlib.MeasureTheory.Measure.UniformTable.Adaptive
public import Mathlib.Data.ZMod.Basic

/-!
# Adaptive table-programming regressions

A second address can depend on the first value read. The full table-and-label exchange still
permutes the uniform experiment, including on repeated inputs. Repeated reads need a collision
condition to identify the final auxiliary labels with actual oracle outputs.

When two writes select different components of the same response, reverse programming must
retain the current response tail. A separate counterexample shows that computing addresses
from the mutable table can destroy involutivity.
-/

public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace VCVioTest.AdaptiveProgramming

abbrev Bit := ZMod 2
abbrev Word := Bit × Bit
abbrev Labels := Bool → Bit
abbrev State := (Bit → Word) × Labels

/-- The first input is zero; the second is the first label read. -/
@[expose, reducible]
def adaptiveInput (v : Bool) (l : Labels) : Bit := if v then l false else 0

/-- Updating a label leaves its own selected address unchanged. -/
theorem adaptiveInput_update (v : Bool) (l : Labels) (a : Bit) :
    adaptiveInput v (Function.update l v a) = adaptiveInput v l := by
  cases v <;> simp [adaptiveInput]

/-- Both reads expose the first component while retaining the other response bit. -/
@[expose, reducible]
def leftSplit (_v : Bool) : Word ≃ Bit × Bit := Equiv.refl _

/-- Two causal adaptive reads, with every displaced value retained. -/
@[expose, reducible]
def adaptiveExchange : State ≃ State :=
  Equiv.tableLabelExchangeList adaptiveInput leftSplit adaptiveInput_update [false, true]

/-- The adaptive experiment has exactly 64 possible complete states. -/
private theorem card_state : Fintype.card State = 64 := by
  norm_num [State, Labels, Word, Bit, Fintype.card_prod, Fintype.card_fun, ZMod.card]

/-- Every complete state has a different image, without enumerating the table values. -/
example : (Finset.univ.image adaptiveExchange).card = 64 := by
  rw [Finset.card_image_of_injective _ adaptiveExchange.injective, Finset.card_univ, card_state]

/-- Distinct adaptive inputs recover the values of the original oracle, independently of
the initial auxiliary labels. -/
example (H : Bit → Word) (l : Labels) (h : (H 0).1 = 1) :
    (adaptiveExchange (H, l)).2 false = (H 0).1 ∧
      (adaptiveExchange (H, l)).2 true = (H 1).1 := by
  simp [adaptiveExchange, Equiv.tableLabelExchangeList, Equiv.tableLabelExchangeStep,
    adaptiveInput, leftSplit, h]

/-- The response tail survives both adaptive reads. -/
example (H : Bit → Word) (l : Labels) (x : Bit) :
    ((adaptiveExchange (H, l)).1 x).2 = (H x).2 := by
  simp only [adaptiveExchange, Equiv.tableLabelExchangeList_cons_apply,
    Equiv.tableLabelExchangeList_nil, Equiv.refl_apply,
    Equiv.tableLabelExchangeStep, leftSplit, Equiv.refl_apply]
  simp only [Function.update_apply]
  split_ifs <;> simp_all

private def collisionTable (x : Bit) : Word := if x = 0 then (0, 0) else (1, 0)
private def collisionLabels (v : Bool) : Bit := if v then 0 else 1

/-- A repeated input can replace the second auxiliary label by displaced randomness instead
of the value that the original oracle would return on a second read. -/
example :
    (adaptiveExchange (collisionTable, collisionLabels)).2 false = 0 ∧
      (adaptiveExchange (collisionTable, collisionLabels)).2 true = 1 ∧
      (collisionTable (collisionTable 0).1).1 = 0 := by
  norm_num [adaptiveExchange, Equiv.tableLabelExchangeList, Equiv.tableLabelExchangeStep,
    adaptiveInput, leftSplit, collisionTable, collisionLabels]

/-- The complete uniform joint observer retains both the table and all labels, with its
half-mass weight unchanged by the adaptive permutation. -/
example :
    letI : MeasurableSpace State := ⊤
    (uniformOn Set.univ : Measure State).bind (fun p ↦ (1 / 2 : ℝ≥0∞) • Measure.dirac p) =
      (uniformOn Set.univ : Measure State).bind
        (fun p ↦ (1 / 2 : ℝ≥0∞) • Measure.dirac (adaptiveExchange.symm p)) := by
  let : MeasurableSpace State := ⊤
  exact uniformOn_univ_bind_tableLabelExchangeList_symm adaptiveInput leftSplit
    adaptiveInput_update [false, true] (fun p ↦ (1 / 2 : ℝ≥0∞) • Measure.dirac p)

/-! ## Repeated cells with different response projections -/

/-- One node projects the left response bit and the other projects the right bit. -/
@[expose, reducible]
def componentSplit (v : Bool) : Word ≃ Bit × Bit :=
  if v then Equiv.prodComm _ _ else Equiv.refl _

/-- The first reverse write changes the tail that the second reverse write must retain. -/
example :
    Equiv.tableLabelProgram (fun _ (_ : Labels) ↦ ()) componentSplit [false, true]
      (fun _ : Unit ↦ (1, 1)) (fun _ ↦ 0) () = (0, 0) := by
  simp [Equiv.tableLabelProgram, componentSplit]

/-- Reusing tails from the original base table loses the earlier restored response bit. -/
example :
    let base : Unit → Word := fun _ ↦ (1, 1)
    let afterRight := Function.update base () ((componentSplit true).symm
      (0, (componentSplit true (base ())).2))
    Function.update afterRight () ((componentSplit false).symm
      (0, (componentSplit false (base ())).2)) () = (0, 1) := by
  simp [componentSplit]

/-- A response outside the exchanged input remains exactly the original full raw word. -/
example (H : Fin 3 → Word) (l : Labels) :
    (Equiv.tableLabelExchange false (fun _ : Labels ↦ (0 : Fin 3)) (Equiv.refl Word)
      (fun _ _ ↦ rfl) (H, l)).1 2 = H 2 := by
  simp [Equiv.tableLabelExchangeStep]

/-! ## Mutable-table addresses need not be reversible -/

/-- An exchange that computes its address from the table it changes. -/
@[expose, reducible]
def tableDependentStep (p : (Bool → Bool) × Bool) : (Bool → Bool) × Bool :=
  let t := p.1 false
  (Function.update p.1 t p.2, p.1 t)

/-- Two such exchanges need not restore the original table. -/
example :
    (tableDependentStep (tableDependentStep (id, true))).1 false = true ∧
      (id false : Bool) = false := by decide

end VCVioTest.AdaptiveProgramming
