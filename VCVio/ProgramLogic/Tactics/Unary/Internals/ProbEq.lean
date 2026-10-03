/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public meta import VCVio.ProgramLogic.Tactics.Common.Naming
public import VCVio.OracleComp.EvalDist.Measure
public import VCVio.EvalDist.ProbabilityBounds

/-!
# Program-equality steps

The steps behind `prrw`: equalities between the events, expectations or output measures of two
programs that differ by the order of independent draws or agree after a shared prefix. A step
swaps two adjacent independent binds (`OracleComp.wp_swap`, `OracleComp.evalDist_bind_bind_swap`
and their uniform-answer forms), at the top or under shared prefixes, or reduces a shared prefix
by congruence on its support (`wp_congr_of_support`, `OracleComp.evalDist_bind_congr_of_support`).
`runProbEqNormalize` searches bounded sequences of these steps for one that closes the goal.
-/

public meta section

open Lean Elab Tactic Meta

namespace OracleComp.ProgramLogic
namespace TacticInternals
namespace Unary

/-- A probability-equality planner action: close by swapping adjacent independent binds, reduce
by bind congruence with or without support hypotheses, or rewrite one swap at a given depth. -/
inductive ProbEqAction where
  | swap
  | congr
  | congrNoSupport
  | rewrite
  | rewriteUnder (depth : Nat)

/-- Bring both sides into the bind shape the swap and congruence laws match: events and
expectations into the normal form of `Pr{…}[…]` and `𝔼{…}[…]`, output measures into plain bind
chains. -/
private def normalizeProbEqGoal : TacticM Unit := do
  if ((← instantiateMVars (← getMainTarget)).find? isExpectationExpr).isSome then
    discard <| tryEvalTacticSyntax (← `(tactic| simp only [expect_norm]))
  else
    discard <| tryEvalTacticSyntax (← `(tactic|
      simp only [map_eq_bind_pure_comp, bind_assoc]))

/-- Normalize a probability equality and try swapping adjacent independent binds. -/
def runProbEqSwap : TacticM Bool := do
  normalizeProbEqGoal
  tryEvalTacticSyntax (← `(tactic| (
    try simp only [bind_assoc]
    first
      | (rw [OracleComp.wp_swap]; done)
      | (rw [OracleComp.wp_swap_of_uniform]; done)
      | (rw [OracleComp.evalDist_bind_bind_swap]; done)
      | (rw [OracleComp.evalDist_bind_bind_swap_of_uniform]; done))))

/-- Reduce an equality of composed event masses, or of composed output measures, to the
continuations on the support of the shared prefix. The goal left behind quantifies over a
possible output of the prefix and its support hypothesis. -/
private def runProbEqCongrCore : TacticM Bool := do
  tryEvalTacticSyntax (← `(tactic|
    first
      | refine wp_congr_of_support (m := OracleComp _) _ ?_
      | (refine OracleComp.evalDist_bind_apply_congr_of_support _ _ _ ?_ ?_
         · first
             | exact measurableSet_singleton _
             | exact MeasurableSet.of_discrete)
      | refine OracleComp.evalDist_bind_congr_of_support _ _ _ ?_))

/-- Apply probability bind congruence without support hypotheses and introduce named values. -/
def runProbEqCongrNoSupportWithNames (names : Array Name) : TacticM Bool := do
  normalizeProbEqGoal
  if ← runProbEqCongrCore then
    discard <| introMainGoalNames names
    discard <| tryEvalTacticSyntax (← `(tactic| intro _))
    return true
  return false

/-- Apply probability bind congruence using fresh names without support hypotheses. -/
def runProbEqCongrNoSupport : TacticM Bool := do
  let names ← getProbCongrNames false
  runProbEqCongrNoSupportWithNames names

/-- Try to decompose a `Pr{let x ← mx; …}[…] = Pr{let x ← mx; …}[…]` goal, or an equality of output
measures of binds, by congruence, then auto-intro the bound variable and support hypothesis. -/
def runProbEqCongrWithNames (names : Array Name) : TacticM Bool := do
  normalizeProbEqGoal
  if ← runProbEqCongrCore then
    discard <| introMainGoalNames names
    return true
  return false

/-- Try support-sensitive probability congruence, then its unconditional variant. -/
def runProbEqCongr : TacticM Bool := do
  let names ← getProbCongrNames true
  if ← runProbEqCongrWithNames names then
    return true
  runProbEqCongrNoSupport

private def chunkNameArray
    (names : Array Name) (width : Nat) : Option (Array (Array Name)) := Id.run do
  if width = 0 || names.isEmpty then
    return none
  if names.size % width != 0 then
    return none
  let mut chunks : Array (Array Name) := #[]
  let mut i := 0
  while i < names.size do
    chunks := chunks.push (names.extract i (i + width))
    i := i + width
  return some chunks

/-- Apply successive congruence steps, grouping names by whether support hypotheses are
introduced. -/
def runProbEqCongrChainWithNames
    (supportSensitive : Bool) (names : Array Name) : TacticM Bool := do
  let width := if supportSensitive then 2 else 1
  let some chunks := chunkNameArray names width | return false
  let saved ← saveState
  for chunk in chunks do
    let ok ←
      if supportSensitive then
        runProbEqCongrWithNames chunk
      else
        runProbEqCongrNoSupportWithNames chunk
    if !ok then
      saved.restore
      return false
  return true

/-- Build an output-measure theorem that swaps adjacent binds under `depth` shared prefixes;
`uniform` selects the swap law that derives countable responses from a uniform specification. -/
partial def mkEvalDistSwapUnderProof (uniform : Bool) (depth : Nat) : TacticM (TSyntax `term) := do
  match depth with
  | 0 =>
      if uniform then `(term| OracleComp.evalDist_bind_bind_swap_of_uniform _ _ _)
      else `(term| OracleComp.evalDist_bind_bind_swap _ _ _)
  | depth + 1 =>
      let inner ← mkEvalDistSwapUnderProof uniform depth
      `(term| OracleComp.evalDist_bind_congr_of_support _ _ _ fun _ _ => $inner)

/-- A conversion that descends through `depth` shared expectations `wp⟦a⟧ fun x => …` of an
event or expectation in normal form and then rewrites with `swap`. -/
partial def mkWpSwapUnderConv (swap : Ident) (depth : Nat) : TacticM (TSyntax `conv) := do
  match depth with
  | 0 => `(conv| rw [$swap:ident])
  | depth + 1 =>
      let inner ← mkWpSwapUnderConv swap depth
      `(conv| (arg 2; ext; $inner))

/-- Try to rewrite one top-level bind-swap without closing the goal. -/
def runProbEqRewrite : TacticM Bool := do
  normalizeProbEqGoal
  tryEvalTacticSyntax (← `(tactic| (
    first
      | rw [OracleComp.wp_swap]
      | rw [OracleComp.wp_swap_of_uniform]
      | rw [OracleComp.evalDist_bind_bind_swap]
      | rw [OracleComp.evalDist_bind_bind_swap_of_uniform])))

/-- Try to rewrite one bind-swap under `depth` shared prefixes on either side. -/
def runProbEqRewriteUnder (depth : Nat) : TacticM Bool := do
  normalizeProbEqGoal
  let measure ← mkEvalDistSwapUnderProof false depth
  let measureUniform ← mkEvalDistSwapUnderProof true depth
  let expectation ← mkWpSwapUnderConv (mkIdent ``OracleComp.wp_swap) depth
  let expectationUniform ← mkWpSwapUnderConv (mkIdent ``OracleComp.wp_swap_of_uniform) depth
  tryEvalTacticSyntax (← `(tactic| (
    first
      | (conv_lhs => $expectation:conv)
      | (conv_rhs => $expectation:conv)
      | (conv_lhs => $expectationUniform:conv)
      | (conv_rhs => $expectationUniform:conv)
      | (conv_lhs => rw [show _ from $measure])
      | (conv_rhs => rw [show _ from $measure])
      | (conv_lhs => rw [show _ from $measureUniform])
      | (conv_rhs => rw [show _ from $measureUniform]))))

/-- The side of a probability equality a rewrite is confined to. -/
inductive ProbEqSide where
  | lhs
  | rhs

/-- Try to rewrite one bind-swap under `depth` shared prefixes on one side only. -/
def runProbEqRewriteAt (side : ProbEqSide) (depth : Nat) : TacticM Bool := do
  normalizeProbEqGoal
  let measure ← mkEvalDistSwapUnderProof false depth
  let measureUniform ← mkEvalDistSwapUnderProof true depth
  let expectation ← mkWpSwapUnderConv (mkIdent ``OracleComp.wp_swap) depth
  let expectationUniform ← mkWpSwapUnderConv (mkIdent ``OracleComp.wp_swap_of_uniform) depth
  match side with
  | .lhs =>
      tryEvalTacticSyntax (← `(tactic| (
        first
          | (conv_lhs => $expectation:conv)
          | (conv_lhs => $expectationUniform:conv)
          | (conv_lhs => rw [show _ from $measure])
          | (conv_lhs => rw [show _ from $measureUniform]))))
  | .rhs =>
      tryEvalTacticSyntax (← `(tactic| (
        first
          | (conv_rhs => $expectation:conv)
          | (conv_rhs => $expectationUniform:conv)
          | (conv_rhs => rw [show _ from $measure])
          | (conv_rhs => rw [show _ from $measureUniform]))))

/-- Move the draw at depth `i` of the left-hand side to depth `j` by adjacent swaps of
independent draws: sinking it through the draws below it when `i < j`, lifting it through the
draws above it when `j < i`. Stops early when a swap makes the equality reflexive. -/
def runProbEqMove (i j : Nat) : TacticM Bool := do
  if i = j then return false
  let depths := if i < j then (List.range (j - i)).map (i + ·)
    else ((List.range (i - j)).map (j + ·)).reverse
  let saved ← saveState
  for depth in depths do
    if (← getGoals).isEmpty then return true
    unless ← runProbEqRewriteAt .lhs depth do
      saved.restore
      return false
  return true

/-- Execute a probability-equality planner action. -/
def runProbEqAction : ProbEqAction → TacticM Bool
  | .swap => runProbEqSwap
  | .congr => runProbEqCongr
  | .congrNoSupport => runProbEqCongrNoSupport
  | .rewrite => runProbEqRewrite
  | .rewriteUnder depth =>
      if depth = 0 then
        runProbEqRewrite
      else
        runProbEqRewriteUnder depth

/-- Try a small backtracking-free sequence of probability-equality steps. -/
def tryProbEqActions (steps : List ProbEqAction) : TacticM Bool := do
  let saved ← saveState
  for step in steps do
    if (← getGoals).isEmpty then
      return true
    if !(← runProbEqAction step) then
      saved.restore
      return false
  return true

private def mkRewriteChain (depth : Nat) : List ProbEqAction :=
  ((List.range depth).reverse.map fun idx => ProbEqAction.rewriteUnder (idx + 1)) ++
    [ProbEqAction.rewrite]

private def probEqCongrPlans (maxDepth : Nat) : List (List ProbEqAction) :=
  let layers := (List.range maxDepth).map fun idx =>
    let depth := idx + 1
    [List.replicate depth ProbEqAction.congr,
      List.replicate depth ProbEqAction.congrNoSupport]
  layers.foldr List.append []

private def probEqRewritePlans (maxDepth : Nat) : List (List ProbEqAction) :=
  let layers := ((List.range (maxDepth + 1)).reverse.map fun depth =>
    let chain := mkRewriteChain depth
    [chain ++ [ProbEqAction.congr], chain ++ [ProbEqAction.congrNoSupport], chain])
  layers.foldr List.append []

private def probEqPlannerActionPlans : List (List ProbEqAction) :=
  probEqRewritePlans 4 ++ probEqCongrPlans 3 ++
    [ [.congr]
    , [.congrNoSupport]
    , [.congr, .swap]
    , [.congrNoSupport, .swap]
    , [.swap]
    ]

/-- The observed computation of an output measure `𝒟[p <$> comp]` is `comp`, also when unfolded to
`comp >>= fun x => pure (p x)`; its bind depth is that of `comp`. -/
private def stripEventObservation (comp : Expr) : Expr :=
  let comp := comp.consumeMData
  if comp.isAppOfArity ``Functor.map 6 then comp.appArg!
  else if isBindExpr comp then
    let args := comp.getAppArgs
    match args.back?, args[args.size - 2]? with
    | some (.lam _ _ body _), some inner =>
        if body.consumeMData.getAppFn.isConstOf ``Pure.pure then inner else comp
    | _, _ => comp
  else
    comp

private def probExprComp? (expr : Expr) : Option Expr :=
  stripEventObservation <$> evalDistComp? expr

private partial def topBindDepth (expr : Expr) : Nat :=
  let expr := expr.consumeMData
  if isBindExpr expr then
    let args := expr.getAppArgs
    if h : 0 < args.size then
      let k := args[args.size - 1]
      match k.consumeMData with
      | .lam _ _ body _ => topBindDepth body + 1
      | _ => 1
    else
      1
  else
    0

/-- The number of draws before the last one in a measure expression: the nested expectations of an
event or expectation, or the binds of an output measure's computation. -/
private partial def probExprDepth? (expr : Expr) : Option Nat :=
  let expr := expr.consumeMData
  if isExpectationExpr expr then
    match (expr.getArg! 8).consumeMData with
    | .lam _ _ body _ => some ((probExprDepth? body).getD 0 + 1)
    | _ => some 1
  else
    topBindDepth <$> probExprComp? expr

private def probEqBindDepth? (target : Expr) : Option Nat := do
  let target := target.consumeMData
  guard <| target.isAppOfArity ``Eq 3
  some (Nat.min (← probExprDepth? (target.getArg! 1)) (← probExprDepth? (target.getArg! 2)))

private def probEqPlannerActionPlansForDepth (bindDepth : Nat) : List (List ProbEqAction) :=
  let maxRewriteDepth := Nat.min 4 (bindDepth - 2)
  let maxCongrDepth := Nat.min 3 bindDepth
  probEqRewritePlans maxRewriteDepth ++ probEqCongrPlans maxCongrDepth ++
    [ [.congr]
    , [.congrNoSupport]
    , [.congr, .swap]
    , [.congrNoSupport, .swap]
    , [.swap]
    ]

private def probEqPlannerActionPlansForGoal : TacticM (List (List ProbEqAction)) := do
  let target ← instantiateMVars (← getMainTarget)
  match probEqBindDepth? target with
  | some depth => return probEqPlannerActionPlansForDepth depth
  | none => return probEqPlannerActionPlans

/-- Bring the goal to normal form, then search the bounded sequences of bind-swap rewrites and
congruence steps, sized by its bind depth, for one that closes the equality, and run it. -/
def runProbEqNormalize : TacticM Bool := withVCGenProbPlannerTiming do
  normalizeProbEqGoal
  for plan in ← probEqPlannerActionPlansForGoal do
    let preview ← previewActionWithGoals (tryProbEqActions plan)
    if preview.ok && preview.goalCount = 0 then
      return (← tryProbEqActions plan)
  return false

/-- Explain why a bind-swap rewrite at the requested prefix depth failed. -/
def throwPrrwError (depth : Nat) : TacticM Unit := withMainContext do
  let target ← instantiateMVars (← getMainTarget)
  if depth = 0 then
    throwError
      "prrw: expected a probability-equality goal where one top-level\n\
      bind-swap rewrite applies.\n\
      Goal:{indentExpr target}"
  else
    throwError
      "prrw under {depth}: expected a probability-equality goal where one\n\
      bind-swap rewrite applies under {depth} shared bind prefix(es).\n\
      Goal:{indentExpr target}"

/-- Explain why moving a draw of the left-hand side failed. -/
def throwPrrwMoveError (i j : Nat) : TacticM Unit := withMainContext do
  let target ← instantiateMVars (← getMainTarget)
  if i = j then
    throwError "prrw move {i} {j}: the source and target depths are equal."
  throwError
    "prrw move {i} {j}: expected a probability-equality goal whose left-hand side has a\n\
    draw at depth {i} that adjacent swaps of independent draws take to depth {j}.\n\
    Goal:{indentExpr target}"

/-- Explain a failed combined bind-swap and congruence step. -/
def throwPrrwCongrError (supportSensitive : Bool) : TacticM Unit := withMainContext do
  let target ← instantiateMVars (← getMainTarget)
  if supportSensitive then
    throwError
      "prrw congr: expected a probability-equality goal with a shared outer\n\
      bind, leaving the bound variable and a support hypothesis.\n\
      Goal:{indentExpr target}"
  else
    throwError
      "prrw congr': expected a probability-equality goal with a shared outer\n\
      bind, leaving only the bound variable.\n\
      Goal:{indentExpr target}"

/-- Explain why the bounded probability-equality normalization search failed. -/
def throwPrrwNormalizeError : TacticM Unit := withMainContext do
  let target ← instantiateMVars (← getMainTarget)
  throwError
    "prrw normalize: expected a probability-equality goal where the bounded\n\
    probability-equality planner can close the goal by bind-swap and congruence steps.\n\
    Goal:{indentExpr target}"

end Unary
end TacticInternals
end OracleComp.ProgramLogic
