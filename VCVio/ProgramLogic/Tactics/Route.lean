/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public meta import VCVio.ProgramLogic.Tactics.Common.Route
public meta import VCVio.ProgramLogic.Tactics.Unary

/-!
# Route diagnostics

* `#route_decl n`: the route of the statement of `n`, and its key;
* `route?`: the route of the main goal, and its key;
* `#guard_route t => "tag"`: check that the proposition `t` routes to `tag` (for tests).

It also puts the classifier in front of `vcgen`. An explicit core triple (`Std.WP.Triple` or
`⊑ wp`) with a known reading goes straight to core `vcgen`, as the caller wrote it; VCVio's
pipeline would otherwise send it through its `ℝ≥0∞`-specific steps, whatever its carrier. If core
fails, the pipeline takes the goal. Every other goal falls through (`throwUnsupportedSyntax`) to
that pipeline unchanged. `set_option vcvio.route.trace
true` reports each goal's route.
-/

public meta section

open Lean Elab Command Term Meta Tactic

namespace OracleComp.ProgramLogic.Route

/-- The route of a statement, with its key. -/
def describe (k : RouteKey) : MessageData :=
  m!"route {k.tag}: {repr k}"

/-- `#route_decl n` reports the route of the statement of `n`. -/
syntax (name := routeDecl) "#route_decl " ident : command

elab_rules : command
  | `(#route_decl $id) => liftTermElabM do
    let n ← realizeGlobalConstNoOverloadWithInfo id
    logInfo (describe (← classify (← getConstInfo n).type))

/-- `route?` reports the route of the main goal. -/
syntax (name := routeQuery) "route?" : tactic

elab_rules : tactic
  | `(tactic| route?) => do logInfo (describe (← classifyGoal (← getMainGoal)))

/-- `#guard_route t => "tag"` fails unless the proposition `t` routes to `tag`. -/
syntax (name := guardRoute) "#guard_route " term " => " str : command

elab_rules : command
  | `(#guard_route $t => $tag) => liftTermElabM do
    let e ← elabType t
    Term.synthesizeSyntheticMVarsNoPostponing
    let e ← instantiateMVars e
    let k ← classify e
    unless k.tag == tag.getString do
      throwError "expected route {tag.getString}, got {describe k}"

register_option vcvio.route.enabled : Bool := {
  defValue := true
  descr := "Route `vcgen` goals through the classifier (`false`: VCVio's pipeline only)."
}

register_option vcvio.route.trace : Bool := {
  defValue := false
  descr := "Report the route of each `vcgen` goal."
}

elab_rules (kind := OracleComp.ProgramLogic.vcgenBasic) : tactic
  | `(tactic| vcgen) => do
    if (← getGoals).isEmpty || !vcvio.route.enabled.get (← getOptions) then throwUnsupportedSyntax
    let k ← classifyGoal (← getMainGoal)
    if vcvio.route.trace.get (← getOptions) then logInfo (describe k)
    match k.route with
    | .coreVCGen _ =>
      -- An explicit core triple: core `vcgen`, with its default configuration, under the
      -- caller's scope and options. If core fails, VCVio's pipeline takes the goal.
      let saved ← saveState
      try evalTactic (← `(tactic| vcgen (errorOnMissingSpec := true)))
      catch _ =>
        saved.restore
        throwUnsupportedSyntax
    | _ => throwUnsupportedSyntax

end OracleComp.ProgramLogic.Route
