/-
Copyright (c) 2026 VCVio Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module
public meta import Batteries.Tactic.Lint.Basic

/-!
# Direct uses of `PMF`

VCVio's probability semantics are Mathlib measures. This environment linter reports declarations
whose types or values refer directly to Mathlib's `PMF`, the countably supported distributions,
so that probability stays measure-valued. The repository's exact `nolints.json` baseline holds no
exception for it. `VCVio.Prelude.Core` imports this module, so the linter is available to every
VCVio library.
-/

public meta section

open Lean Meta Batteries.Tactic.Lint

namespace ToMathlib.Lint

private def retiredProbabilityName (name : Name) : Bool :=
  name == `PMF

/-- Report declarations that directly depend on Mathlib's `PMF`. -/
@[env_linter] def usesRetiredProbability : Linter where
  noErrorsFound := "No direct use of `PMF`."
  errorsFound := "DIRECT USE OF `PMF`."
  test declName := do
    if ← isAutoDecl declName then return none
    let info ← getConstInfo declName
    if info.type.getUsedConstants.any retiredProbabilityName then
      return m!"type refers to `PMF`"
    let value? := match info with
      | .defnInfo { value, .. } | .thmInfo { value, .. } => some value
      | _ => none
    if let some value := value? then
      if value.getUsedConstants.any retiredProbabilityName then
        return m!"value refers to `PMF`"
    return none

end ToMathlib.Lint
