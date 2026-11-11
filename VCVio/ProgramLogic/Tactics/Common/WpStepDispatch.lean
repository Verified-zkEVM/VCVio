/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public meta import Lean.Elab.Tactic.Basic
public meta import VCVio.ProgramLogic.Tactics.Common.Core
public import VCVio.ProgramLogic.Unary.SimulateQ

/-!
# `runWpStepRules` Dispatch

Dispatch tactic for raw `wp`-shaped goals. One step rewrites the goal with a single equation of
`wpStepRules`:

* PolyFun's `ExactWPMonad` equations for `pure`, `>>=`, `<$>`, `ite` and `dite`, which hold for
  every exact core `Std.WP` interpretation;
* VCVio's equations for the oracle primitives (`query`, `HasQuery.query`, `$ᵗ`), the iterators
  (`replicate`, `List.mapM`, `List.foldlM`) and the simulations (`simulateQ`, `liftComp`) from
  `VCVio/ProgramLogic/Unary/HoareTriple.lean` and `VCVio/ProgramLogic/Unary/SimulateQ.lean`.

A rule is a candidate when the head constant of the computation on its left-hand side is the head
of the goal's computation, first as written and then after reducible `whnf`.
-/

public meta section

open Lean Elab Tactic Meta

namespace OracleComp.ProgramLogic

/-! ## Rules -/

/-- The equations `wp comp post … = …` of one `runWpStepRules` step, in the order they are tried.
The monad structure uses PolyFun's `ExactWPMonad` laws; the remaining rules are specific to
oracle computations. -/
def wpStepRules : Array Name := #[
  ``ExactWPMonad.wp_pure,
  ``ExactWPMonad.wp_bind,
  ``ExactWPMonad.wp_map,
  ``ExactWPMonad.wp_ite,
  ``ExactWPMonad.wp_dite,
  ``wp_replicate_zero,
  ``wp_replicate_succ,
  ``wp_list_mapM_nil,
  ``wp_list_mapM_cons,
  ``wp_list_foldlM_nil,
  ``wp_list_foldlM_cons,
  ``wp_query,
  ``wp_HasQuery_query,
  ``wp_uniformSample,
  ``wp_simulateQ_eq,
  ``wp_simulateQ_run'_eq,
  ``wp_liftComp]

/-- The computation of an application of VCVio's `wp` or of core `Std.WP.wp`. -/
private def wpAppComp? (e : Expr) : Option Expr :=
  let e := e.consumeMData
  let n := e.getAppNumArgs
  if e.getAppFn.isConstOf ``OracleComp.ProgramLogic.wp && n ≥ 2 then
    some (e.getArg! (n - 2))
  else if e.getAppFn.isConstOf ``Std.WP.wp && n ≥ 3 then
    some (e.getArg! (n - 3))
  else
    none

/-- Head constant of the computation on the left-hand side of the `wp` equation `declName`. -/
private def wpRuleCompHead? (declName : Name) : MetaM (Option Name) := do
  let info ← getConstInfo declName
  forallTelescopeReducing info.type fun _ body => do
    let_expr Eq _ lhs _ := body.consumeMData | return none
    return (wpAppComp? lhs).bind (·.getAppFn.constName?)

/-- `wpStepRules` paired with the heads of their left-hand computations, computed once. -/
initialize wpStepRuleHeadsCache : IO.Ref (Option (Array (Name × Name))) ← IO.mkRef none

private def getWpStepRuleHeads : MetaM (Array (Name × Name)) := do
  if let some heads ← wpStepRuleHeadsCache.get then
    return heads
  let heads ← wpStepRules.filterMapM fun rule => do
    return (← wpRuleCompHead? rule).map (rule, ·)
  wpStepRuleHeadsCache.set (some heads)
  return heads

/-! ## Dispatch -/

/-- Rewrite the main goal with the equation `declName`, then try `rfl` on what remains. -/
private def runWpStepRule (declName : Name) : TacticM Bool := do
  match ← getGoals with
  | [] => return false
  | goal :: rest =>
      let saved ← saveState
      setGoals [goal]
      try
        evalTactic (← `(tactic| simp only [$(mkCIdent declName):ident]))
      catch _ =>
        saved.restore
        return false
      unless (← getGoals).isEmpty do
        discard <| tryEvalTacticSyntax (← `(tactic| rfl))
      setGoals ((← getGoals) ++ rest)
      return true

/-- Advance a `wp`-shaped goal by one rewrite with the rules of `wpStepRules`.

Locates the first `wp oa post` sub-expression of the main target and tries the rules whose
left-hand computation has the head of `oa`, as written and then after reducible `whnf`.

Returns `false` when no candidate succeeds, or when the goal contains no `wp` application at
all. -/
def runWpStepRules : TacticM Bool := withVCGenWpStepTiming do
  let target ← instantiateMVars (← getMainTarget)
  let some wpApp := findAppWithHead? ``OracleComp.ProgramLogic.wp target | return false
  let some oa := wpAppComp? (← instantiateMVars wpApp) | return false
  let heads ← liftMetaM getWpStepRuleHeads
  let syntactic := oa.consumeMData.getAppFn.constName?
  let normalized := (← whnfR oa).consumeMData.getAppFn.constName?
  let candidates :=
    (heads.filter fun (_, head) => some head == syntactic) ++
      (heads.filter fun (_, head) => some head == normalized && some head != syntactic)
  for (rule, _) in candidates do
    if ← runWpStepRule rule then return true
  return false

end OracleComp.ProgramLogic
