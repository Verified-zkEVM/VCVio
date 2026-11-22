/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Interop.Squirrel.Indist

/-!
# Checks of the constructions and the closure fields

For each closure field of `AdvClass`, a machine built by its construction from input projections
and constants, what it computes (its `run` lemma at that machine), and its membership in
`AdvClass.all` through the field:

* `Machine.swapInput` (`Machine.rename`, `AdvClass.rename_mem`) returns its second input;
* `Machine.appInput` (`Machine.app`, `AdvClass.app_mem`) applies its first input to its second;
* `Machine.fnInput` (`Machine.fn`, `AdvClass.fn_mem`) returns an honest symbol;
* `Machine.substInput` (`Machine.subst`, `AdvClass.subst_mem`) answers its first input by running
  a second machine, which returns the remaining input;
* `Machine.branchInput` (`Machine.branch`, `Machine.const`, `AdvClass.branch_mem`,
  `AdvClass.const_mem`) returns its Boolean input.

`Machine.app` makes two input queries per query (`Machine.QueryBound.app`), so `Machine.appInput`
meets the bound `2`. A branch makes one query before its branches (`Machine.QueryBound.branch`):
`Machine.branchInput`, whose branches are constants, meets the bound `1` and not `0`. A constant
makes no query and reads nothing of the tape.
-/

public section

namespace Interop.Squirrel

open IPFunctor IPFunctor.ScopedSignature OracleComp

variable {B : Type} {D : Decl B} {M : Model D} {η : ℕ} {ρa : M.TapeA η}

namespace Machine

/-- The second of two Boolean inputs, by relabelling the input projection. -/
@[expose] def swapInput : Machine M [.bool, .bool] .bool :=
  (input .zero Ty.isGround_bool).rename (Env.cons (.succ .zero) Env.empty)

/-- The first input, a Boolean function, applied to the second, a Boolean. -/
@[expose] def appInput : Machine M [.arrow .bool .bool, .bool] .bool :=
  (input .zero Ty.isGround_bool : Machine M [.bool] .bool).app Ty.isGround_bool

/-- The honest symbol `f`, by answering the input projection with it. -/
@[expose] def fnInput (f : D.Fn .bool) : Machine M [] .bool :=
  (input .zero Ty.isGround_bool).fn f

/-- The input projection, with its input answered by the machine returning the remaining
input. -/
@[expose] def substInput : Machine M [.bool] .bool :=
  subst (as := []) (ρ := .bool) (input .zero Ty.isGround_bool) (input .zero Ty.isGround_bool)

/-- The Boolean input, by branching on it between two constants. -/
@[expose] def branchInput : Machine M [.bool] .bool := branch (const true) (const false)

theorem run_swapInput (e : Vals M η [.bool, .bool]) :
    (swapInput : Machine M _ _).run η ρa e = e _ (.succ .zero) := by
  rw [swapInput, run_rename, run_input]
  rfl

theorem run_appInput (e : Vals M η [.arrow .bool .bool, .bool]) :
    (appInput : Machine M _ _).run η ρa e = e _ .zero (e _ (.succ .zero)) := by
  rw [appInput, run_app, run_input]
  rfl

theorem run_fnInput (f : D.Fn .bool) (e : Vals M η []) :
    (fnInput f : Machine M _ _).run η ρa e = M.fn η f := by
  rw [fnInput, run_fn, run_input]
  rfl

theorem run_substInput (e : Vals M η [.bool]) :
    (substInput : Machine M _ _).run η ρa e = e _ .zero := by
  rw [substInput, run_subst]
  exact (run_input _ _ _).trans
    (run_input (ρa := ρa) (τs := [.bool]) .zero Ty.isGround_bool (Env.append Env.empty e))

theorem run_branchInput (e : Vals M η [.bool]) :
    (branchInput : Machine M _ _).run η ρa e = e _ .zero := by
  rw [branchInput, run_branch, run_const, run_const]
  cases e _ .zero <;> rfl

/-- `Machine.app` makes two input queries per query: the application of an input to an input
meets the bound `2`. -/
theorem queryBound_appInput : (appInput : Machine M _ _).QueryBound fun _ => 2 :=
  ((queryBound_input _ _).app Ty.isGround_bool).mono fun _ => le_rfl

/-- A branch between constants makes one query. -/
theorem queryBound_branchInput : (branchInput : Machine M _ _).QueryBound fun _ => 1 :=
  ((queryBound_const (q := fun _ => 0) true).branch (queryBound_const (q := fun _ => 0) false)).mono
    fun _ => le_rfl

/-- The bound `1` is tight: a branch queries its condition. -/
theorem not_queryBound_branchInput_zero :
    ¬ (branchInput : Machine M _ _).QueryBound fun _ => 0 := fun h => by
  have h0 := h 0
  rw [branchInput, branch, ask, isQueryBoundP_query_bind_iff] at h0
  exact absurd (h0.1.resolve_left (not_not.2 rfl)) (lt_irrefl 0)

/-- A constant makes no query and reads nothing of the tape. -/
theorem queryBound_const_zero (c : Bool) :
    (const c : Machine M [] .bool).QueryBound (fun _ => 0) ∧
      (const c : Machine M [] .bool).ReadsBelow (fun _ => 0) :=
  ⟨queryBound_const c, readsBelow_const c⟩

end Machine

namespace AdvClass

/-- `AdvClass.all` meets `rename_mem` at `Machine.swapInput`. -/
theorem all_mem_swapInput : (all M).mem Machine.swapInput :=
  (all M).rename_mem _ (all_mem_input _ _)

/-- `AdvClass.all` meets `app_mem` at `Machine.appInput`. -/
theorem all_mem_appInput : (all M).mem Machine.appInput :=
  (all M).app_mem _ (all_mem_input _ _)

/-- `AdvClass.all` meets `fn_mem` at `Machine.fnInput`. -/
theorem all_mem_fnInput (f : D.Fn .bool) : (all M).mem (Machine.fnInput f) :=
  (all M).fn_mem f (all_mem_input _ _)

/-- `AdvClass.all` meets `subst_mem` at `Machine.substInput`. -/
theorem all_mem_substInput : (all M).mem Machine.substInput :=
  (all M).subst_mem (all_mem_input _ _) (all_mem_input _ _)

/-- `AdvClass.all` meets `branch_mem` and `const_mem` at `Machine.branchInput`. -/
theorem all_mem_branchInput : (all M).mem Machine.branchInput :=
  (all M).branch_mem ((all M).const_mem _) ((all M).const_mem _)

end AdvClass

end Interop.Squirrel
