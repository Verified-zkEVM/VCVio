/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import VCVio.ProgramLogic.Tactics

/-!
# Reading scopes of oracle computations

The structural reading is the global `WP` instance of `OracleComp`. The other readings are
scoped, each registering its `WPMonad` and a direct `WP` instance at priority `1100`, above the
generic measure scopes (`ExpectationWP.Quantitative`, `ExpectationWP.Probabilistic`,
priority `1050`) and below the per-call `Dispatch` scopes (`1200`). Core's assertion carriers are
output parameters, so exactly one reading is live per program type in a scope; these checks pin
which one it is under each combination of open scopes, on `ProbComp`.
-/

public section

open Std.WP
open scoped ENNReal

namespace VCVioTest.ProgramLogic.ReadingScopes

/-! ## No scope: the structural reading -/

noncomputable example : WP (ProbComp Bool) Bool Prop EStack⟨⟩ := inferInstance

example : True := by
  fail_if_success
    let _ := (inferInstance : WP (ProbComp Bool) Bool ℝ≥0∞ EStack⟨⟩)
  trivial

example (oa : ProbComp Bool) (post : Bool → Prop) :
    wp oa post Lean.Order.bot ↔ ∀ a ∈ support oa, post a :=
  Iff.rfl

/-! ## The expectation scope -/

section Quantitative
open scoped OracleComp.Quantitative

noncomputable example : WP (ProbComp Bool) Bool ℝ≥0∞ EStack⟨⟩ := inferInstance

example : True := by
  fail_if_success
    let _ := (inferInstance : WP (ProbComp Bool) Bool Prop EStack⟨⟩)
  trivial

example (oa : ProbComp Bool) (post : Bool → ℝ≥0∞) :
    wp oa post Lean.Order.bot = wp⟦oa⟧ post :=
  rfl

end Quantitative

/-! ## The generic measure scope alone -/

section GenericMeasure
open scoped ExpectationWP.Quantitative

noncomputable example : WP (ProbComp Bool) Bool ℝ≥0∞ EStack⟨⟩ := inferInstance

example : True := by
  fail_if_success
    let _ := (inferInstance : WP (ProbComp Bool) Bool Prop EStack⟨⟩)
  trivial

end GenericMeasure

/-! ## A reading scope beside the generic measure scope

The reading of `OracleComp` outranks the generic measure scope's direct instance. -/

section AngelicBesideGeneric
open scoped ExpectationWP.Quantitative OracleComp.Angelic

noncomputable example : WP (ProbComp Bool) Bool Prop EStack⟨⟩ := inferInstance

example : True := by
  fail_if_success
    let _ := (inferInstance : WP (ProbComp Bool) Bool ℝ≥0∞ EStack⟨⟩)
  trivial

example (oa : ProbComp Bool) (post : Bool → Prop) :
    wp oa post Lean.Order.bot ↔ ∃ a ∈ support oa, post a :=
  Iff.rfl

end AngelicBesideGeneric

section UpperBesideGeneric
open scoped ExpectationWP.Quantitative OracleComp.Upper

noncomputable example : WP (ProbComp Bool) Bool ℝ≥0∞ᵒᵈ EStack⟨⟩ᵒᵈ := inferInstance

example : True := by
  fail_if_success
    let _ := (inferInstance : WP (ProbComp Bool) Bool ℝ≥0∞ EStack⟨⟩)
  trivial

end UpperBesideGeneric

section ProbabilisticBesideGeneric
open scoped ExpectationWP.Quantitative OracleComp.Probabilistic

noncomputable example : WP (ProbComp Bool) Bool Prob EStack⟨⟩ := inferInstance

example : True := by
  fail_if_success
    let _ := (inferInstance : WP (ProbComp Bool) Bool ℝ≥0∞ EStack⟨⟩)
  trivial

end ProbabilisticBesideGeneric

/-! ## A per-call scope above a file-level reading -/

section Dispatch
open scoped OracleComp.Upper

noncomputable example : WP (ProbComp Bool) Bool ℝ≥0∞ᵒᵈ EStack⟨⟩ᵒᵈ := inferInstance

open scoped OracleComp.Quantitative.Dispatch in
noncomputable example : WP (ProbComp Bool) Bool ℝ≥0∞ EStack⟨⟩ := inferInstance

open scoped OracleComp.Qualitative.Dispatch in
noncomputable example : WP (ProbComp Bool) Bool Prop EStack⟨⟩ := inferInstance

end Dispatch

end VCVioTest.ProgramLogic.ReadingScopes
