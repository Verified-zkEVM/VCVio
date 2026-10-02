/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module
public meta import Batteries.Tactic.Lint.Basic

/-!
# Security-statement hygiene

Two environment linters over the security libraries, the modules under `VCVio.CryptoFoundations`,
`LatticeCrypto`, `HashSig` and `Examples`, each reporting a shape under which a security theorem
holds for every scheme:

* `existentialReduction`: a theorem whose conclusion existentially quantifies a reduction,
  simulator, extractor or distinguisher, that is, a function (possibly of no arguments) into an
  oracle computation: an `OracleComp` or `ProbComp`, or one of them under `OptionT`, `ExceptT` or
  `StateT`. Nested existentials are searched through. Such a witness carries no resource bound
  and can be chosen classically, so the statement proves nothing; a security theorem names its
  reduction instead. A witness bundled in a structure is not recognized.
* `unconstrainedRealParameter`: a theorem whose conclusion is an upper bound (`≤`, `<`, `≥` or
  `>`) with a parameter in `ℝ` that reaches the bounding side through `ENNReal.ofReal` or
  `Real.toNNReal` and is bounded by no hypothesis, so a negative value drives the clamped term,
  such as a loss, to zero and the bound becomes trivial. An equality fixes the role of its
  parameters, so the real parameters of a distribution, such as a Gaussian's center, are not
  reported, and a parameter in `ℝ≥0` or `ℝ≥0∞` is nonnegative by type and is not reported.

Definitions are not linted. Exceptions are maintained by the repository's exact `nolints.json`
baseline. The option `linter.securityStatements.everywhere` lints every module, for the linters'
own fixtures.
-/

public meta section

open Lean Meta Batteries.Tactic.Lint

/-- Lint the security-statement shapes in every module rather than in the security libraries
only, for the linters' fixtures. -/
register_option linter.securityStatements.everywhere : Bool := {
  defValue := false
  descr := "lint the security-statement shapes in every module rather than in the security \
    libraries only"
}

namespace ToMathlib.Lint

/-- The module roots whose theorems are security statements. -/
private def securityRoots : Array Name :=
  #[`VCVio.CryptoFoundations, `LatticeCrypto, `HashSig, `Examples]

/-- Whether a declaration is linted: it is in a module under a security root, or the option
`linter.securityStatements.everywhere` is set. -/
private def inScope (declName : Name) : MetaM Bool := do
  if linter.securityStatements.everywhere.get (← getOptions) then return true
  let env ← getEnv
  let some idx := env.getModuleIdxFor? declName | return false
  let module := env.header.moduleNames[idx.toNat]!
  return securityRoots.any (·.isPrefixOf module)

/-- Whether a type is that of a computation: an application of `OracleComp` or `ProbComp`, or of
`OptionT`, `ExceptT` or `StateT` to one. -/
private partial def isComputation (ty : Expr) : Bool :=
  let ty := ty.cleanupAnnotations
  if ty.isAppOf `OracleComp || ty.isAppOf `ProbComp then true
  else if ty.isAppOf `OptionT || ty.isAppOf `ExceptT || ty.isAppOf `StateT then
    ty.getAppArgs.any isComputation
  else false

/-- Whether a type is a reduction's: a function type, possibly of no arguments, into a
computation. -/
private def isReductionType (ty : Expr) : MetaM Bool :=
  forallTelescope ty fun _ cod => return isComputation cod

/-- The names of the reductions a conclusion existentially quantifies, searching through nested
existentials. -/
private partial def existentialReductions (e : Expr) : MetaM (Array Name) := do
  let e := e.cleanupAnnotations
  unless e.isAppOfArity ``Exists 2 do return #[]
  let ty := e.getArg! 0
  let body := e.getArg! 1
  let here ← isReductionType ty
  let name := if body.isLambda then body.bindingName! else `_
  let rest ← lambdaTelescope body fun _ b => existentialReductions b
  return (if here then #[name] else #[]) ++ rest

/-- Report theorems of the security libraries whose conclusion existentially quantifies a
reduction, simulator, extractor or distinguisher: a function into an oracle computation. -/
@[env_linter] def existentialReduction : Linter where
  noErrorsFound := "No security theorem existentially quantifies a reduction."
  errorsFound := "SECURITY THEOREMS EXISTENTIALLY QUANTIFYING A REDUCTION."
  test declName := do
    if ← isAutoDecl declName then return none
    let .thmInfo info ← getConstInfo declName | return none
    unless ← inScope declName do return none
    let names ← forallTelescope info.type fun _ body => existentialReductions body
    if names.isEmpty then return none
    return m!"the conclusion existentially quantifies the reduction(s) {names}; a security \
      theorem names its reduction"

/-- Whether a term clamps a real into `ℝ≥0` or `ℝ≥0∞` through `Real.toNNReal` or
`ENNReal.ofReal`, with the variable `fvar` free in the clamped real. -/
private def clampsFVar (fvar : FVarId) (e : Expr) : Bool :=
  (e.isAppOfArity `ENNReal.ofReal 1 || e.isAppOfArity `Real.toNNReal 1) &&
    (e.getArg! 0).containsFVar fvar

/-- The bounding side of a conclusion that bounds a quantity from above: `b` in `a ≤ b`, `a < b`,
`b ≥ a` and `b > a`. -/
private def upperSide? (body : Expr) : Option Expr :=
  let body := body.cleanupAnnotations
  if body.isAppOfArity ``LE.le 4 || body.isAppOfArity ``LT.lt 4 then some (body.getArg! 3)
  else if body.isAppOfArity ``GE.ge 4 || body.isAppOfArity ``GT.gt 4 then some (body.getArg! 2)
  else none

/-- Report theorems of the security libraries whose conclusion is an upper bound with a parameter
in `ℝ` that reaches the bounding side through `ENNReal.ofReal` or `Real.toNNReal` and is bounded
by no hypothesis. -/
@[env_linter] def unconstrainedRealParameter : Linter where
  noErrorsFound := "No security theorem has an unconstrained real parameter."
  errorsFound := "SECURITY THEOREMS WITH AN UNCONSTRAINED REAL PARAMETER."
  test declName := do
    if ← isAutoDecl declName then return none
    let .thmInfo info ← getConstInfo declName | return none
    unless ← inScope declName do return none
    let flagged ← forallTelescope info.type fun xs body => do
      let some upper := upperSide? body | return #[]
      let mut flagged := #[]
      for x in xs do
        unless (← inferType x).cleanupAnnotations.isConstOf `Real do continue
        let fvar := x.fvarId!
        unless (upper.find? (clampsFVar fvar)).isSome do continue
        let mut constrained := false
        for y in xs do
          if y != x then
            let ty ← inferType y
            if (← isProp ty) && ty.containsFVar fvar then
              constrained := true
        unless constrained do
          flagged := flagged.push (← fvar.getUserName)
      return flagged
    if flagged.isEmpty then return none
    return m!"the real parameter(s) {flagged} are clamped by `ENNReal.ofReal` or \
      `Real.toNNReal` in the conclusion's upper bound and bounded by no hypothesis"

end ToMathlib.Lint
