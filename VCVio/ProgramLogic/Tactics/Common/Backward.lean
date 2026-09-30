/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public meta import Lean.Meta.Sym.Apply
public meta import VCVio.ProgramLogic.Tactics.Common.Registry

/-!
# Backward application for VCSpec entries

Shared native application helpers for `@[vcspec]` entries.
-/

public meta section

open Lean Elab Tactic Meta

namespace OracleComp.ProgramLogic

/-- Cached VCVio wrapper around Lean's symbolic backward rule. The source
entry is kept for diagnostics and replay text. -/
structure VCSpecBackwardRule where
  source : VCSpecEntry
  rawGoal : Bool
  proof : AbstractMVarsResult
  declName : Name
  rule : Lean.Meta.Sym.BackwardRule

/-- Cache key for global `@[vcspec]` backward rules.

Local hypotheses and raw syntax proofs are intentionally not cached here.
For global declarations, the declaration name fixes the theorem body while the
raw/folded mode and normalized `VCSpecKind` select the consequence wrapper shape.
Carrier, WP/RWP instance, exception-post, and state arguments remain abstracted
in the cached proof and are reopened freshly at each application. If future local
or structurally specialized entries are cached, this key should be widened
rather than reused. -/
private abbrev VCSpecBackwardRuleCacheKey := Name × Bool × Nat

private def VCSpecKind.cacheKey : VCSpecKind → Nat
  | .relTriple => 0
  | .relWP => 1

private def VCSpecKind.traceLabel : VCSpecKind → String
  | .relTriple => "relTriple"
  | .relWP => "relWP"

private def rawGoalTraceLabel (rawGoal : Bool) : String :=
  if rawGoal then "raw" else "folded"

private initialize vcSpecBackwardRuleCache :
    IO.Ref (Std.HashMap VCSpecBackwardRuleCacheKey VCSpecBackwardRule) ←
  IO.mkRef {}

private def traceVCSpecCacheEvent (event : String) (entry : VCSpecEntry)
    (rawGoal : Bool) : MetaM Unit := do
  if vcvio.vcgen.traceCachedRules.get (← getOptions) then
    let source := entry.declName?.map Name.toString |>.getD "<local>"
    logInfo m!"[vcspec cache] {event} `{source}` \
      ({rawGoalTraceLabel rawGoal}, {entry.kind.traceLabel})"

/-- Extract the predicate carrier from a raw order relation. -/
private def rawOrderCarrier? (type : Expr) : MetaM (Option Expr) := do
  let type ← whnfR type
  if type.isAppOfArity ``Lean.Order.PartialOrder.rel 4 ||
      type.isAppOfArity ``LE.le 4 then
    return some (type.getArg! 0)
  return none

/-- If a raw order goal fixes the predicate carrier, push that information into
a universe-polymorphic `⊑` / `≤` proof before `Meta.apply`. -/
private def fixPredFromGoal? (prfTy goalTy : Expr) : MetaM Unit := do
  let some prfPred ← rawOrderCarrier? prfTy | return
  let some goalPred ← rawOrderCarrier? goalTy | return
  _ ← isDefEq prfPred goalPred

/-- A goal whose target is already in `≤`/`⊑` weakest-precondition form. -/
private def isRawBackwardGoal (target : Expr) : MetaM Bool := do
  let target ← whnfR target
  return target.isAppOfArity ``LE.le 4 ||
    target.isAppOfArity ``Lean.Order.PartialOrder.rel 4

private def rawRelParts? (type : Expr) : MetaM (Option (Expr × Expr)) := do
  let type ← whnfR type
  if type.isAppOfArity ``Lean.Order.PartialOrder.rel 4 ||
      type.isAppOfArity ``LE.le 4 then
    return some (type.getArg! 2, type.getArg! 3)
  return none

private def stdDoRelWpParts? (rhs : Expr) : Option (Expr × Expr × Expr × Expr × Expr) := do
  let rhs := rhs.consumeMData
  unless rhs.getAppFn.isConstOf ``VCVio.ProgramLogic.rwp do none
  let args := rhs.getAppArgs
  unless args.size ≥ 5 do none
  let oa := args[args.size - 5]!
  let ob := args[args.size - 4]!
  let post := args[args.size - 3]!
  let epost₁ := args[args.size - 2]!
  let epost₂ := args[args.size - 1]!
  some (oa, ob, post, epost₁, epost₂)

private def mkOrderRel (lhs rhs : Expr) : MetaM Expr := do
  let pred ← inferType lhs
  mkAppOptM ``Lean.Order.PartialOrder.rel #[some pred, none, some lhs, some rhs]

private def rawOrderParts? (type : Expr) : MetaM (Option (Expr × Expr × Expr)) := do
  let type ← whnfR type
  if type.isAppOfArity ``Lean.Order.PartialOrder.rel 4 ||
      type.isAppOfArity ``LE.le 4 then
    return some (type.getArg! 0, type.getArg! 2, type.getArg! 3)
  return none

private def mkOrderRelTrans (hxy hyz : Expr) : MetaM Expr := do
  let hxyTy ← instantiateMVars (← inferType hxy)
  let hyzTy ← instantiateMVars (← inferType hyz)
  let some (pred, x, y) ← rawOrderParts? hxyTy
    | mkAppM ``Lean.Order.PartialOrder.rel_trans #[hxy, hyz]
  let some (_, _, z) ← rawOrderParts? hyzTy
    | mkAppM ``Lean.Order.PartialOrder.rel_trans #[hxy, hyz]
  mkAppOptM ``Lean.Order.PartialOrder.rel_trans
    #[some pred, none, some x, some y, some z, some hxy, some hyz]

/-- Build the pointwise relational-postcondition premise used when a concrete
relational post from a spec theorem is generalized to the goal's postcondition. -/
private def mkRelPostPointwisePremise (postSpec postTarget postTy : Expr) :
    MetaM Expr := do
  let .forallE _ α body _ := postTy.consumeMData
    | throwError "expected a relational postcondition, got:{indentExpr postTy}"
  let .forallE _ β _ _ := body.consumeMData
    | throwError "expected a binary relational postcondition, got:{indentExpr postTy}"
  withLocalDeclD `a α fun a => do
    withLocalDeclD `b β fun b => do
      let lhs := mkApp2 postSpec a b
      let rhs := mkApp2 postTarget a b
      let rel ← mkOrderRel lhs rhs
      mkForallFVars #[a, b] rel

/-- Generalize a raw relational `pre ⊑ rwp left right post epost₁ epost₂`
proof into a reusable backward rule source by abstracting concrete `post` and always abstracting
`pre` through transitivity; qualitative and quantitative carriers share this path once they are
expressed as `VCVio.ProgramLogic.RelTriple` / raw `VCVio.ProgramLogic.rwp`. -/
private def mkRelSpecBackwardProof (pre rhs specProof : Expr) : MetaM Expr := do
  let some (oa, ob, postSpec, epost₁, epost₂) := stdDoRelWpParts? rhs
    | throwError "expected a VCVio.ProgramLogic.rwp RHS, got:{indentExpr rhs}"
  let mut postAbstract := postSpec.consumeMData
  let mut specApplied := specProof
  unless postAbstract.isMVar do
    let postTy ← inferType postSpec
    postAbstract ← mkFreshExprMVar (userName := `post) postTy
    let hpostTy ← mkRelPostPointwisePremise postSpec postAbstract postTy
    let hpost ← mkFreshExprMVar (userName := `postImpl) hpostTy
    specApplied ←
      mkAppM ``VCVio.ProgramLogic.RelWP.rwp_consequence_rel
        #[oa, ob, postSpec, postAbstract, epost₁, epost₂, hpost, specApplied]
  let preTy ← inferType pre
  let preAbstract ← mkFreshExprMVar (userName := `pre) preTy
  let hpreTy ← mkOrderRel preAbstract pre
  let hpre ← mkFreshExprMVar (userName := `vc) hpreTy
  mkOrderRelTrans hpre specApplied

private def mkBackwardRuleFromProofExpr (prf : Expr) :
    MetaM (AbstractMVarsResult × Name × Lean.Meta.Sym.BackwardRule) := do
  let prf ← instantiateMVars prf
  let res ← abstractMVars prf
  let type ← instantiateMVars (← inferType res.expr)
  let decl ← mkAuxLemma res.paramNames.toList type res.expr
  let rule ← Lean.Meta.Sym.mkBackwardRuleFromDecl decl
  return (res, decl, rule)

/-- Normalize a `pre ⊑ rhs` / `pre ≤ rhs` proof into a reusable backward-rule
source when `rhs` is a raw `VCVio.ProgramLogic.rwp` (through `mkRelSpecBackwardProof`); anything
else is returned unchanged. -/
private def normalizeRawRelProof (prf type : Expr) : MetaM Expr := do
  match ← rawRelParts? type with
  | some (pre, rhs) =>
      if (stdDoRelWpParts? rhs).isSome then
        mkRelSpecBackwardProof pre rhs prf
      else
        pure prf
  | none => pure prf

private def mkVCSpecBackwardRule (entry : VCSpecEntry) (rawGoal : Bool) :
    MetaM VCSpecBackwardRule := do
  let (_xs, _bis, prf, type) ← entry.proof.instantiate
  let prf ← normalizeRawRelProof prf type
  let (proof, declName, rule) ← mkBackwardRuleFromProofExpr prf
  return { source := entry, rawGoal, proof, declName, rule }

private def mkVCSpecBackwardRuleTimed (entry : VCSpecEntry) (rawGoal : Bool) :
    MetaM VCSpecBackwardRule := do
  if vcvio.vcgen.time.get (← getOptions) then
    let (rule, ns) ← timeNs (mkVCSpecBackwardRule entry rawGoal)
    addCachedRuleBuildTime ns
    return rule
  else
    mkVCSpecBackwardRule entry rawGoal

private def getVCSpecBackwardRuleCached (entry : VCSpecEntry) (rawGoal : Bool) :
    MetaM VCSpecBackwardRule := do
  let some declName := entry.declName?
    | traceVCSpecCacheEvent "uncached-build" entry rawGoal
      mkVCSpecBackwardRuleTimed entry rawGoal
  -- Only global declarations use the shared cache. Local hypotheses and syntax
  -- proofs can share pretty names while carrying different closed-over terms, so
  -- they must build a fresh rule unless the cache key grows expression identity.
  let key : VCSpecBackwardRuleCacheKey := (declName, rawGoal, entry.kind.cacheKey)
  let cache ← vcSpecBackwardRuleCache.get
  match cache[key]? with
  | some rule =>
      addCachedRuleHit
      traceVCSpecCacheEvent "hit" entry rawGoal
      return rule
  | none =>
      addCachedRuleMiss
      traceVCSpecCacheEvent "miss" entry rawGoal
      let rule ← mkVCSpecBackwardRuleTimed entry rawGoal
      vcSpecBackwardRuleCache.modify fun cache => cache.insert key rule
      return rule

/-- Whether applying this registered theorem is expected to leave an ordinary
proof obligation, such as an auxiliary premise. Instance arguments and data
arguments are ignored. -/
def VCSpecEntry.hasProofPremise (entry : VCSpecEntry) : MetaM Bool := do
  let (xs, bis, _prf, _type) ← entry.proof.instantiate
  for x in xs, bi in bis do
    if bi == .default then
      if ← isProp (← inferType x) then
        return true
  return false

/-- Apply a raw relational `@[vcspec]` theorem under consequence, constructing
the consequence proof against the current target directly. This avoids asking
elaboration to infer the target `rwp` shape from an underscore-heavy `refine`
term, which is expensive for premised raw relational rules. -/
def VCSpecEntry.tryApplyRawRelConsequence (entry : VCSpecEntry) (mvarId : MVarId) :
    MetaM (Option (List MVarId)) := do
  let goalTy ← instantiateMVars (← mvarId.getType)
  let some (preTarget, rhsTarget) ← rawRelParts? goalTy
    | return none
  let some (oaTarget, obTarget, postTarget, _epostTarget₁, _epostTarget₂) :=
      stdDoRelWpParts? rhsTarget
    | return none
  let (_xs, _bis, specProof, specType) ← entry.proof.instantiate
  let some (preSpec, rhsSpec) ← rawRelParts? specType
    | return none
  let some (oaSpec, obSpec, postSpec, epostSpec₁, epostSpec₂) :=
      stdDoRelWpParts? rhsSpec
    | return none
  unless (← isDefEq oaSpec oaTarget) && (← isDefEq obSpec obTarget) do
    return none
  let postTy ← inferType postSpec
  let hpostTy ← mkRelPostPointwisePremise postSpec postTarget postTy
  let hpost ← mkFreshExprMVar (userName := `postImpl) hpostTy
  let specApplied ←
    mkAppM ``VCVio.ProgramLogic.RelWP.rwp_consequence_rel
      #[oaSpec, obSpec, postSpec, postTarget, epostSpec₁, epostSpec₂, hpost, specProof]
  let hpreTy ← mkOrderRel preTarget preSpec
  let hpre ← mkFreshExprMVar (userName := `vc) hpreTy
  let prf ← mkOrderRelTrans hpre specApplied
  try
    let subgoals ← mvarId.apply prf
    return some subgoals
  catch _ =>
    return none

/-- Apply a raw relational consequence proof for a `@[vcspec]` entry to the
current main goal, preserving tail goals. -/
def runVCSpecEntryRawRelConsequence (entry : VCSpecEntry) : TacticM Bool := do
  match ← getGoals with
  | [] => return false
  | goal :: rest =>
      match ← liftMetaM <| entry.tryApplyRawRelConsequence goal with
      | none => return false
      | some subgoals =>
          setGoals (subgoals ++ rest)
          return true

private def VCSpecBackwardRule.applyProof (rule : VCSpecBackwardRule) (mvarId : MVarId)
    (goalTy : Expr) : MetaM (Option (List MVarId)) := do
  try
    let (_xs, _bis, prf) ← openAbstractMVarsResult rule.proof
    let prfTy ← instantiateMVars (← inferType prf)
    fixPredFromGoal? prfTy goalTy
    let subgoals ← mvarId.apply prf
    return some subgoals
  catch _ =>
    return none

/-- Try to apply a cached symbolic backward rule for a registered `@[vcspec]`
entry. Rules are normalized through raw `rwp` sources when their theorem statements expose that
form definitionally. -/
def VCSpecEntry.tryApplyCachedBackward (entry : VCSpecEntry) (mvarId : MVarId) :
    MetaM (Option (List MVarId)) := do
  let goalTy ← instantiateMVars (← mvarId.getType)
  let rawGoal ← isRawBackwardGoal goalTy
  let rule ← getVCSpecBackwardRuleCached entry rawGoal
  if rawGoal then
    return (← rule.applyProof mvarId goalTy)
  -- The cache outlives environments: a rule built during a speculative application that was
  -- rolled back, or in an earlier `example`, names an auxiliary lemma the current environment no
  -- longer declares. Its abstracted proof source still applies.
  unless (← getEnv).contains rule.declName do
    return (← rule.applyProof mvarId goalTy)
  let symResult ←
    try
      Lean.Meta.Sym.SymM.run <| rule.rule.apply mvarId
    catch _ =>
      pure .failed
  match symResult with
  | .failed =>
      -- `Sym.BackwardRule` matches against its preprocessed pattern. Some
      -- folded VCVio-facing goals are still better handled by Lean's ordinary
      -- elaborated application, but we still apply the cached abstracted proof
      -- source, not the original theorem entry.
      rule.applyProof mvarId goalTy
  | .goals subgoals => return some subgoals

/-- Try to apply a registered `@[vcspec]` entry directly to a goal metavariable.

This instantiates the stored `SpecProof`, applies with fresh metavariables, and returns the
generated subgoals. Goal-specific close passes remain in the relational planner, which knows
which leaf rules are cheap and valid for its logic. -/
def VCSpecEntry.tryApplyBackward (entry : VCSpecEntry) (mvarId : MVarId) :
    MetaM (Option (List MVarId)) := do
  let (_xs, _bis, prf, type) ← entry.proof.instantiate
  let goalTy ← instantiateMVars (← mvarId.getType)
  fixPredFromGoal? type goalTy
  try
    let subgoals ← mvarId.apply prf
    return some subgoals
  catch _ =>
    return none

/-- Apply a `@[vcspec]` entry to the current main goal, preserving the tail goals.

This helper performs only the theorem application. Callers should run their
existing cheap close pass afterwards. -/
def runVCSpecEntryBackward (entry : VCSpecEntry) : TacticM Bool := do
  match ← getGoals with
  | [] => return false
  | goal :: rest =>
      match ← liftMetaM <| entry.tryApplyBackward goal with
      | none => return false
      | some subgoals =>
          setGoals (subgoals ++ rest)
          return true

/-- Apply a cached symbolic backward rule for a `@[vcspec]` entry to the
current main goal, preserving the tail goals. -/
def runVCSpecEntryCachedBackward (entry : VCSpecEntry) : TacticM Bool := do
  match ← getGoals with
  | [] => return false
  | goal :: rest =>
      match ← liftMetaM <| entry.tryApplyCachedBackward goal with
      | none => return false
      | some subgoals =>
          setGoals (subgoals ++ rest)
          return true

end OracleComp.ProgramLogic
