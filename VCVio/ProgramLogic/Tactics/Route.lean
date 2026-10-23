/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public meta import VCVio.ProgramLogic.Tactics.Common.Route

/-!
# Route diagnostics

* `#route_decl n`: the route of the statement of `n`, and its key;
* `route?`: the route of the main goal, and its key;
* `#guard_route t => "tag"`: check that the proposition `t` routes to `tag` (for tests).
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

end OracleComp.ProgramLogic.Route
