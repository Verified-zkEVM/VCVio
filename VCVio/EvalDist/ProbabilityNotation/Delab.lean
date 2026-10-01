/-
Copyright (c) 2026 VCVio Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module
public import VCVio.EvalDist.ProbabilityNotation.Elab
public meta import Lean.PrettyPrinter.Delaborator.Basic

/-!
# Display of events and expectations

An expectation, core's `wp` at `ℝ≥0∞` with no exception postcondition under the measure
interpretation of its monad, displays as the notation that elaborates to it: each draw
`wp⟦a⟧ fun x => …` is a statement `let x ← a`, a continuation that is again an expectation, of
any monad, continues the sequence, and the innermost observation is the event `[t]` of an
indicator `predInd p` or `propInd t`, or the value `[b]` otherwise. The display inverts the
translation of `VCVio.EvalDist.ProbabilityNotation.Elab`, so what is displayed elaborates back to
the term displayed; a draw whose display carries no monad, such as `pure a`, needs an ascription
or `pp.analyze` to be read back.
-/

public meta section Delaboration

open Lean Meta PrettyPrinter Delaborator SubExpr

namespace ProbabilityNotation

/-- Whether an ordered algebra is the expectation algebra of successful-output measures. -/
partial def isMeasureAlgebra (a : Expr) : MetaM Bool := do
  let a := a.cleanupAnnotations
  if a.isAppOf ``MeasureProgramLogic.toMAlgOrdered then return true
  match ← withReducibleAndInstances (unfoldDefinition? a) with
  | some a' => isMeasureAlgebra a'
  | none => return false

/-- Whether a weakest-precondition interpretation is the measure interpretation. -/
partial def isMeasureInterpretation (w : Expr) : MetaM Bool := do
  let w := w.cleanupAnnotations
  if w.isAppOf ``MeasureProgramLogic.measureWP then return true
  if w.isAppOfArity ``MAlgOrdered.toWPMonad 6 then return ← isMeasureAlgebra (w.getArg! 4)
  match ← withReducibleAndInstances (unfoldDefinition? w) with
  | some w' => isMeasureInterpretation w'
  | none => return false

/-- The monadic interpretation behind a `WP` instance on programs: `w` when the instance is
`w.toWP α`, seen through reducible and instance definitions. -/
partial def wpMonadOf? (inst : Expr) : MetaM (Option Expr) := do
  let inst := inst.cleanupAnnotations
  if inst.isAppOfArity ``Std.WP.WPMonad.toWP 8 then return some (inst.getArg! 6)
  match ← withReducibleAndInstances (unfoldDefinition? inst) with
  | some inst' => wpMonadOf? inst'
  | none => return none

/-- Whether `e` is an expectation: core's `wp` at `ℝ≥0∞` with no exception postcondition, under
the measure interpretation of its monad. -/
def isExpectation (e : Expr) : MetaM Bool := do
  unless e.isAppOfArity ``Std.WP.WP.wp 10 do return false
  unless (e.getArg! 2).isConstOf ``ENNReal do return false
  unless (e.getArg! 9).isAppOf ``Lean.Order.bot do return false
  let some w ← wpMonadOf? (e.getArg! 6) | return false
  isMeasureInterpretation w

/-- The statement `let x ← a` for a draw bound by the `fun` `f`, or `let _ ← a` when `f` ignores
its argument. -/
def drawItem (f : Expr) (x : Syntax) (a : Term) (sep : Bool) :
    DelabM (TSyntax ``Lean.Parser.Term.doSeqItem) := do
  let x : Term ← if f.bindingBody!.hasLooseBVars then pure ⟨x⟩ else `(_)
  if sep then `(Lean.Parser.Term.doSeqItem| let $x:term ← $a:term;)
  else `(Lean.Parser.Term.doSeqItem| let $x:term ← $a:term)

/-- The last draw `let x ← a` of a sequence observed by `f` when `f` is not a `fun`: the
observation is displayed applied to the first of `x`, `y`, `z`, `w` that no enclosing draw binds. -/
def applyDraw (a : Term) : DelabM (TSyntax ``Lean.Parser.Term.doSeqItem × Term) := do
  let f ← getExpr
  let .forallE _ dom _ _ ← whnf (← inferType f) | failure
  let lctx ← getLCtx
  let name := ([`x, `y, `z, `w].find? fun n => (lctx.findFromUserName? n).isNone).getD
    (lctx.getUnusedName `x)
  withLocalDeclD name dom fun x => do
    let t ← withTheReader SubExpr (fun sub => { sub with expr := mkApp f x }) delab
    return (← `(Lean.Parser.Term.doSeqItem| let $(mkIdent name):ident ← $a:term), t)

/-- The value after the draws: the event `t` of an indicator `propInd t`, or the value itself. -/
def delabValue : DelabM (Term × Bool) := do
  let b ← getExpr
  if b.isAppOfArity ``propInd 1 then return (← withNaryArg 0 delab, true)
  return (← delab, false)

/-- The draws of an expectation, as `let x ← a` statements, the value after them, and whether
the last observation is an event's indicator. -/
partial def delabDraws :
    DelabM (Array (TSyntax ``Lean.Parser.Term.doSeqItem) × Term × Bool) := do
  let a ← withNaryArg 7 delab
  withNaryArg 8 do
    let g := (← getExpr).cleanupAnnotations
    if g.isAppOfArity ``predInd 2 then
      return ← withNaryArg 1 do
        let p ← getExpr
        if p.isLambda then
          return ← withBindingBodyUnusedName fun x => do
            return (#[← drawItem p x a false], ← delab, true)
        let (item, t) ← applyDraw a
        return (#[item], t, true)
    unless g.isLambda do
      let (item, t) ← applyDraw a
      return (#[item], t, false)
    withBindingBodyUnusedName fun x => do
      let body := (← getExpr).cleanupAnnotations
      if ← isExpectation body then
        let (draws, t, event) ← delabDraws
        return (#[← drawItem g x a true] ++ draws, t, event)
      let (t, event) ← delabValue
      return (#[← drawItem g x a false], t, event)

/-- Display an expectation as the notation it elaborates from: `Pr{…}[…]` when its innermost
observation is an indicator and `𝔼{…}[…]` otherwise. -/
@[delab app.Std.WP.WP.wp]
def delabExpectation : Delab := whenPPOption getPPNotation <| withOverApp 10 do
  unless ← isExpectation (← getExpr) do failure
  let (draws, t, event) ← delabDraws
  if event then `(Pr{$draws*}[$t]) else `(𝔼{$draws*}[$t])

end ProbabilityNotation

end Delaboration
