/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import ToMathlib.Lint.SecurityStatements
public import Batteries.Tactic.Lint.Frontend
public import VCVio.OracleComp.ProbComp.Basic
public import Mathlib.Basic.Real.Basic

/-!
# Fixtures for the security-statement linters

One flagged and one accepted case per linter, linted in this file under
`linter.securityStatements.everywhere`, since the linters are scoped to the security libraries.
-/

public section

namespace VCVioTest.Lint.SecurityStatements

/-- Flagged: the reduction is existentially quantified. -/
theorem existentialReduction_flagged : ∃ _reduction : ℕ → ProbComp ℕ, True :=
  ⟨fun _ => pure 0, trivial⟩

/-- Flagged: the simulator is quantified under another existential. -/
theorem existentialReduction_nested : ∃ _n : ℕ, ∃ _sim : ProbComp Bool, True :=
  ⟨0, pure true, trivial⟩

/-- Accepted: the existential ranges over a number. -/
theorem existentialReduction_accepted : ∃ _n : ℕ, True := ⟨0, trivial⟩

/-- Flagged: `ε` is clamped in the conclusion and no hypothesis bounds it. -/
theorem unconstrainedRealParameter_flagged (ε : ℝ) : ENNReal.ofReal ε ≤ ENNReal.ofReal ε :=
  le_rfl

/-- Accepted: a hypothesis bounds `ε`. -/
theorem unconstrainedRealParameter_accepted (ε : ℝ) (_hε : 0 ≤ ε) :
    ENNReal.ofReal ε ≤ ENNReal.ofReal ε :=
  le_rfl

/-- Accepted: `ε` is not clamped. -/
theorem unconstrainedRealParameter_unclamped (ε : ℝ) : ε ≤ ε := le_rfl

/-- Accepted: an equality fixes the role of `ε`; only an upper bound is linted. -/
theorem unconstrainedRealParameter_equality (ε : ℝ) : ENNReal.ofReal ε = ENNReal.ofReal ε :=
  rfl

/--
error: -- Found 3 errors in 7 declarations (plus 0 automatically generated ones) in the current
file with 2 linters

/- The `existentialReduction` linter reports:
SECURITY THEOREMS EXISTENTIALLY QUANTIFYING A REDUCTION.
This linter can be disabled with `@[nolint existentialReduction]`. -/
#check existentialReduction_flagged /- the conclusion existentially quantifies the reduction(s)
[_reduction]; a security theorem names its reduction -/
#check existentialReduction_nested /- the conclusion existentially quantifies the reduction(s)
[_sim]; a security theorem names its reduction -/

/- The `unconstrainedRealParameter` linter reports:
SECURITY THEOREMS WITH AN UNCONSTRAINED REAL PARAMETER.
This linter can be disabled with `@[nolint unconstrainedRealParameter]`. -/
#check unconstrainedRealParameter_flagged /- the real parameter(s) [ε] are clamped by
`ENNReal.ofReal` or `Real.toNNReal` in the conclusion's upper bound and bounded by no
hypothesis -/
-/
#guard_msgs (whitespace := lax) in
set_option linter.securityStatements.everywhere true in
#lint only existentialReduction unconstrainedRealParameter

end VCVioTest.Lint.SecurityStatements
