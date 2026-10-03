/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import VCVio.ProgramLogic.Tactics.PrVCGen

/-!
# The normal form of an expectation

`simp only [expect_norm]` writes an expectation as nested expectations of its draws, with no
`bind`, `map`, `pure`, branch or sequence combinator left at the head of a drawn computation;
`expect_eval` continues past the normal form into the value of a draw or the unfolding of a loop.
The examples state the normal form of each shape, that the normal form is a fixed point, that
the two sets commute, and pin the members of the three sets, so that a change to them is a
change to this file.
-/

public section

open OracleSpec OracleComp ENNReal

namespace VCVioTest.EvalDist.ExpectNormalForm

variable {α β : Type} (oa : ProbComp α) (ob : ProbComp β) (f : α → ProbComp β) (g : β → ℝ≥0∞)
  (h : α → ℝ≥0∞) (k : α → β) (c : Prop) [Decidable c]

/-! ## Normal forms -/

/-- A bind is the expectation of the continuation's expectation. -/
example : wp⟦oa >>= f⟧ g = wp⟦oa⟧ fun x => wp⟦f x⟧ g := by
  simp only [expect_norm]

/-- A map composes the observation. -/
example : wp⟦k <$> oa⟧ g = wp⟦oa⟧ fun x => g (k x) := by
  simp only [expect_norm]

/-- A return is the observation's value. -/
example (a : α) : wp⟦(pure a : ProbComp α)⟧ h = h a := by
  simp only [expect_norm]

/-- A branch is a branch of expectations. -/
example : wp⟦if c then oa else oa⟧ h = if c then wp⟦oa⟧ h else wp⟦oa⟧ h := by
  simp only [expect_norm]

/-- A dependent branch is a dependent branch of expectations. -/
example (oc : c → ProbComp α) (od : ¬ c → ProbComp α) :
    wp⟦if hc : c then oc hc else od hc⟧ h = if hc : c then wp⟦oc hc⟧ h else wp⟦od hc⟧ h := by
  simp only [expect_norm]

/-- An applied function is the expectation of the function's draw, then the argument's. -/
example (of : ProbComp (α → β)) : wp⟦of <*> oa⟧ g = wp⟦of⟧ fun F => wp⟦oa⟧ fun x => g (F x) := by
  simp only [expect_norm]

/-- A discarded second draw is still drawn. -/
example : wp⟦oa <* ob⟧ h = wp⟦oa⟧ fun x => wp⟦ob⟧ fun _ => h x := by
  simp only [expect_norm]

/-- A discarded first draw is still drawn. -/
example : wp⟦oa *> ob⟧ g = wp⟦oa⟧ fun _ => wp⟦ob⟧ g := by
  simp only [expect_norm]

/-- An event is the expectation of its indicator. -/
example (p : α → Prop) : Pr{let x ← oa}[p x] = wp⟦oa⟧ fun x => propInd (p x) := by
  simp only [expect_norm]

/-- An event after a bind is the expectation of the event after each continuation. -/
example (p : β → Prop) :
    Pr{let x ← oa; let y ← f x}[p y] = wp⟦oa⟧ fun x => Pr{let y ← f x}[p y] := by
  simp only [expect_norm]

/-- A case split on an option is a case split of expectations. -/
example (o : Option β) (ob' : β → ProbComp α) :
    wp⟦o.elim oa ob'⟧ h = o.elim (wp⟦oa⟧ h) fun b => wp⟦ob' b⟧ h := by
  simp only [expect_norm]

/-- A case split on a sum is a case split of expectations. -/
example (s : α ⊕ β) (oa' : α → ProbComp α) (ob' : β → ProbComp α) :
    wp⟦s.elim oa' ob'⟧ h = s.elim (fun a => wp⟦oa' a⟧ h) fun b => wp⟦ob' b⟧ h := by
  simp only [expect_norm]

/-! ## The normal form is a fixed point -/

/-- Nested expectations of draws are left alone. -/
example (c : ℝ≥0∞) (hc : wp⟦oa⟧ (fun x => wp⟦f x⟧ g) = c) :
    wp⟦oa⟧ (fun x => wp⟦f x⟧ g) = c := by
  fail_if_success simp only [expect_norm]
  exact hc

/-- A draw's expectation is left alone. -/
example (c : ℝ≥0∞) (hc : wp⟦oa⟧ h = c) : wp⟦oa⟧ h = c := by
  fail_if_success simp only [expect_norm]
  exact hc

/-! ## Evaluation continues past the normal form, in either order -/

/-- A replicated draw unfolds one step at a time. -/
example : wp⟦oa.replicate 1⟧ (fun xs => (xs.map h).sum) = wp⟦oa⟧ h := by
  simp only [expect_norm, expect_eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    add_zero]

/-- The same, with the sets in the other order. -/
example : wp⟦oa.replicate 1⟧ (fun xs => (xs.map h).sum) = wp⟦oa⟧ h := by
  simp only [expect_eval, expect_norm, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    add_zero]

/-- A mapped list unfolds one element at a time. -/
example (a : α) : wp⟦[a].mapM f⟧ (fun ys => (ys.map g).sum) = wp⟦f a⟧ g := by
  simp only [expect_norm, expect_eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    add_zero]

/-! ## The members of the sets -/

open Lean Meta in
/-- info: ExactWPMonad.wp_bind
ExactWPMonad.wp_dite
ExactWPMonad.wp_ite
ExactWPMonad.wp_map
ExactWPMonad.wp_option_elim
ExactWPMonad.wp_pure
ExactWPMonad.wp_seq
ExactWPMonad.wp_seqLeft
ExactWPMonad.wp_seqRight
ExactWPMonad.wp_sum_elim
predInd_apply -/
#guard_msgs in
#eval show MetaM Unit from do
  let some ext ← getSimpExtension? `expect_norm | throwError "no simp set expect_norm"
  let names := (← ext.getTheorems).lemmaNames.toList.filterMap fun o => match o with
    | .decl n _ _ => some n.toString
    | _ => none
  logInfo (String.intercalate "\n" (names.toArray.qsort (· < ·)).toList)

open Lean Meta in
/-- info: Function.comp_def
List.foldlM_cons
List.foldlM_nil
List.mapM_cons
List.mapM_nil
OracleComp.ProgramLogic.wp_HasQuery_query
OracleComp.ProgramLogic.wp_liftComp
OracleComp.ProgramLogic.wp_liftM_query
OracleComp.ProgramLogic.wp_list_foldlM_cons
OracleComp.ProgramLogic.wp_list_foldlM_nil
OracleComp.ProgramLogic.wp_list_mapM_cons
OracleComp.ProgramLogic.wp_list_mapM_nil
OracleComp.ProgramLogic.wp_query
OracleComp.ProgramLogic.wp_replicate_succ
OracleComp.ProgramLogic.wp_replicate_zero
OracleComp.ProgramLogic.wp_simulateQ_eq
OracleComp.ProgramLogic.wp_simulateQ_run'_eq
OracleComp.ProgramLogic.wp_uniformSample
OracleComp.replicate_succ_bind
OracleComp.replicate_zero
evalDist_pure
le_refl
simulateQ_bind
simulateQ_pure
simulateQ_query -/
#guard_msgs in
#eval show MetaM Unit from do
  let some ext ← getSimpExtension? `expect_eval | throwError "no simp set expect_eval"
  let names := (← ext.getTheorems).lemmaNames.toList.filterMap fun o => match o with
    | .decl n _ _ => some n.toString
    | _ => none
  logInfo (String.intercalate "\n" (names.toArray.qsort (· < ·)).toList)

open Lean Meta in
/-- info: ExpectationWP.wp_add
ExpectationWP.wp_const_mul -/
#guard_msgs in
#eval show MetaM Unit from do
  let some ext ← getSimpExtension? `expect_arith | throwError "no simp set expect_arith"
  let names := (← ext.getTheorems).lemmaNames.toList.filterMap fun o => match o with
    | .decl n _ _ => some n.toString
    | _ => none
  logInfo (String.intercalate "\n" (names.toArray.qsort (· < ·)).toList)

end VCVioTest.EvalDist.ExpectNormalForm
