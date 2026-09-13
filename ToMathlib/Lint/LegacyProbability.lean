/-
Copyright (c) 2026 VCVio Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module
public meta import Batteries.Tactic.Lint.Basic

/-!
# Retiring probability declarations

This environment linter records declarations whose types or values still refer directly
to the deprecated finite-distribution types or VCVio evaluation functions. Exceptions
are maintained by the repository's exact `nolints.json` baseline.
-/

public meta section

open Lean Meta Batteries.Tactic.Lint

namespace ToMathlib.Lint

private def retiredProbabilityName (name : Name) : Bool :=
  #[`PMF, `SPMF, `evalSPMF, `probOutput, `probEvent, `probFailure].contains name

/-- Report declarations that directly depend on the retiring probability API. -/
@[env_linter] def usesRetiredProbability : Linter where
  noErrorsFound := "No direct use of retiring probability declarations."
  errorsFound := "DIRECT USE OF RETIRING PROBABILITY DECLARATIONS."
  test declName := do
    if ← isAutoDecl declName then return none
    let info ← getConstInfo declName
    if info.type.getUsedConstants.any retiredProbabilityName then
      return m!"type refers to the retiring probability API"
    let value? := match info with
      | .defnInfo { value, .. } | .thmInfo { value, .. } => some value
      | _ => none
    if let some value := value? then
      if value.getUsedConstants.any retiredProbabilityName then
        return m!"value refers to the retiring probability API"
    return none

end ToMathlib.Lint
