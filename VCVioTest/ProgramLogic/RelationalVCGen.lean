/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import VCVio.OracleComp.OracleComp
public import VCVio.ProgramLogic.Tactics.Relational

/-!
# The relational tactics' documented forms

One regression per form of `rvcstep` and `rvcgen` that the walkthroughs under
`Examples/ProgramLogic/` do not exercise: the `as ⟨…⟩` names after an explicit hint or theorem,
and `rvcgen` with a single cut relation or an explicit theorem.
-/

public section

open ENNReal OracleSpec OracleComp OracleComp.ProgramLogic OracleComp.ProgramLogic.Relational
open scoped OracleComp.ProgramLogic OracleComp.Rel.Quantitative OracleComp.Lower

namespace VCVioTest.ProgramLogic.RelationalVCGen

variable {ι : Type} {spec : OracleSpec.{0, 0} ι} [∀ t, Finite (spec.Range t)]
  [OracleSpec.AnswerMeasure spec] {α β γ : Type}

/-- `rvcstep using S as ⟨a₁, a₂, h⟩` names the continuation's outputs and their relation. -/
example {oa₁ oa₂ : OracleComp spec α} {f₁ : α → OracleComp spec β} {f₂ : α → OracleComp spec γ}
    {S : RelPost α α} {R : RelPost β γ}
    (hoa : ⟪oa₁ ~ oa₂ | S⟫) (hf : ∀ a₁ a₂, S a₁ a₂ → ⟪f₁ a₁ ~ f₂ a₂ | R⟫) :
    ⟪oa₁ >>= f₁ ~ oa₂ >>= f₂ | R⟫ := by
  rvcstep using S as ⟨a₁, a₂, h⟩

/-- `rvcgen using S` with a single cut relation. -/
example {oa₁ oa₂ : OracleComp spec α} {f₁ : α → OracleComp spec β} {f₂ : α → OracleComp spec γ}
    {S : RelPost α α} {R : RelPost β γ}
    (hoa : ⟪oa₁ ~ oa₂ | S⟫) (hf : ∀ a₁ a₂, S a₁ a₂ → ⟪f₁ a₁ ~ f₂ a₂ | R⟫) :
    ⟪oa₁ >>= f₁ ~ oa₂ >>= f₂ | R⟫ := by
  rvcgen using S

/-- A pair of wrapped programs related by a registered rule. -/
@[irreducible] def leftProg : OracleComp spec Bool := pure true

/-- The right-hand partner of `leftProg`. -/
@[irreducible] def rightProg : OracleComp spec Bool := pure true

@[local vcspec]
theorem relTriple_leftProg_rightProg : ⟪leftProg (spec := spec) ~ rightProg (spec := spec) |
    EqRel Bool⟫ := by
  unfold leftProg rightProg
  rvcstep

/-- A relation under a universally quantified side condition, which an explicit step leaves as a
goal whose binder `as ⟨…⟩` names. -/
theorem leftProg_rightProg_of (_h : ∀ b : Bool, b = b) :
    ⟪leftProg (spec := spec) ~ rightProg (spec := spec) | EqRel Bool⟫ :=
  relTriple_leftProg_rightProg

/-- `rvcstep with thm as ⟨…⟩`: an explicit theorem step, naming the binders of the goals it
leaves. -/
example : ⟪leftProg (spec := spec) ~ rightProg (spec := spec) | EqRel Bool⟫ := by
  rvcstep with leftProg_rightProg_of as ⟨b⟩

/-- `rvcgen with thm`: the explicit theorem, then the structural rules. -/
example : ⟪leftProg (spec := spec) ~ rightProg (spec := spec) | EqRel Bool⟫ := by
  rvcgen with relTriple_leftProg_rightProg

end VCVioTest.ProgramLogic.RelationalVCGen
