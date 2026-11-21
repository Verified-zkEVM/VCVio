/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import VCVio.ProgramLogic.Tactics

/-!
# Core `vcgen` on sums of oracle specifications

Queries to a sum `spec₁ + spec₂` step under core `vcgen`, in the necessary and the lower
readings, and through `pvcgen`: a query `query (Sum.inl t)` or `query (Sum.inr t)` at the sum,
written directly or through `liftM`, and a summand's computation brought in by `liftComp` or by
the `SubSpec` coercion. The answer type of a sum query, `(spec₁ + spec₂).Range (Sum.inl t)`,
stays folded at reducible transparency, since the `+` instance unfolds only at instance
transparency. It does not reduce to a matcher, so the generic query rules apply, and the answers
keep the sum's answer type in the verification conditions.

The rules do not apply when the value type of a triple is the summand's answer type instead:
a postcondition elaborated at `spec₁.Range t`, or at `Bool` for a coin, against a query in tail
position. Core then fails to construct its rule for the lift of the query. The examples pin that
failure in both readings, together with the binder ascription at the sum's answer type that
avoids it; `pvcgen` builds its triples from the program, so its postconditions take the sum's
answer type.
-/

public section

open OracleSpec OracleComp OracleComp.ProgramLogic Std.WP ENNReal MeasureTheory

namespace VCVioTest.ProgramLogic.CoreVCGenSum

set_option experimental.vcgen true

/-- Uniform selection and a coin as two oracles. -/
abbrev UnifCoin : OracleSpec (ℕ ⊕ Unit) := unifSpec + coinSpec

variable {ι ι' : Type} {spec : OracleSpec ι} {spec' : OracleSpec ι'}

/-! ## The necessary reading -/

section Necessary

open scoped OracleComp.Necessary

example : ⦃ True ⦄ (do
      let i ← (UnifCoin.query (Sum.inl 3) : OracleComp UnifCoin _)
      let c ← (UnifCoin.query (Sum.inr ()) : OracleComp UnifCoin _)
      if c = true then pure i.val else pure 0) ⦃ fun r => r ≤ 3 ⦄ := by
  vcgen
  · exact Fin.is_le i
  · omega

/-- A query lifted by `liftM`, a uniform draw brought in by the `SubSpec` coercion, and one
brought in by `liftComp`. -/
example : ⦃ True ⦄ (do
      let b ← ($ᵗ Bool : ProbComp Bool)
      let c ← liftM (UnifCoin.query (Sum.inr ()))
      let d ← liftComp ($ᵗ Bool) UnifCoin
      pure (b || c || d || true) : OracleComp UnifCoin Bool) ⦃ fun r => r = true ⦄ := by
  vcgen
  simp

example (t : ι) (t' : ι') (p : spec.Range t → spec'.Range t' → Prop) (hp : ∀ u v, p u v) :
    ⦃ True ⦄ (do
      let u ← (spec + spec').query (Sum.inl t)
      let v ← (spec + spec').query (Sum.inr t')
      pure (p u v) : OracleComp (spec + spec') Prop) ⦃ fun P => P ⦄ := by
  vcgen
  exact hp u v

/-- A tail query whose postcondition has the summand's answer type: core does not step it. With
the binder ascribed at the sum's answer type it does. -/
example (t : ι) (p : spec.Range t → Prop) (hp : ∀ u, p u) :
    ⦃ True ⦄ ((spec + spec').query (Sum.inl t) : OracleComp (spec + spec') _) ⦃ p ⦄ := by
  fail_if_success vcgen
  change ⦃ True ⦄ ((spec + spec').query (Sum.inl t) : OracleComp (spec + spec') _)
    ⦃ fun (u : (spec + spec').Range (Sum.inl t)) => p u ⦄
  vcgen
  exact hp _

end Necessary

/-! ## The lower reading -/

section Lower

open scoped OracleComp.Lower

open scoped OracleComp.Lower.Pointwise in
example : ⦃ 1 ⦄ (do
      let i ← (UnifCoin.query (Sum.inl 3) : OracleComp UnifCoin _)
      let c ← (UnifCoin.query (Sum.inr ()) : OracleComp UnifCoin _)
      pure (i, c)) ⦃ fun r => propInd (r.1.val ≤ 3) ⦄ := by
  vcgen
  simp [Lean.Order.rel_eq_le, Fin.is_le i]

example : ⦃ 2⁻¹ ⦄ liftComp ($ᵗ Bool) UnifCoin ⦃ fun b => propInd (b = true) ⦄ := by
  vcgen
  simp [Lean.Order.rel_eq_le, propInd]

/-- The exact rule integrates against the answer measure of the sum, which reduces to the
coin's. -/
example : ⦃ 2⁻¹ ⦄ (UnifCoin.query (Sum.inr ()) : OracleComp UnifCoin _)
    ⦃ fun (b : UnifCoin.Range (Sum.inr ())) => propInd (b = true) ⦄ := by
  vcgen
  simp only [Lean.Order.rel_eq_le]
  simp [propInd, lintegral_fintype, ProbabilityTheory.uniformOn, ProbabilityTheory.cond_apply,
    Measure.count_apply_finite]

/-- A tail query whose postcondition has the coin's answer type `Bool`: core does not step it. -/
example : ⦃ 2⁻¹ ⦄ (UnifCoin.query (Sum.inr ()) : OracleComp UnifCoin _)
    ⦃ fun b => propInd (b = true) ⦄ := by
  fail_if_success vcgen
  change ⦃ 2⁻¹ ⦄ (UnifCoin.query (Sum.inr ()) : OracleComp UnifCoin _)
    ⦃ fun (b : UnifCoin.Range (Sum.inr ())) => propInd (b = true) ⦄
  vcgen
  simp only [Lean.Order.rel_eq_le]
  simp [propInd, lintegral_fintype, ProbabilityTheory.uniformOn, ProbabilityTheory.cond_apply,
    Measure.count_apply_finite]

end Lower

/-! ## `pvcgen` -/

example :
    Pr{let b ← (($ᵗ Bool : ProbComp Bool) : OracleComp UnifCoin Bool)
       let c ← (UnifCoin.query (Sum.inr ()) : OracleComp UnifCoin _)}[(b || c || true) = true] =
      1 := by
  pvcgen

example : (2⁻¹ : ℝ≥0∞) ≤
    Pr{let c ← (UnifCoin.query (Sum.inr ()) : OracleComp UnifCoin _)}[c = true] := by
  pvcgen
  simp [lintegral_fintype, ProbabilityTheory.uniformOn, ProbabilityTheory.cond_apply,
    Measure.count_apply_finite]

example : ∀ r ∈ support (do
      let i ← (UnifCoin.query (Sum.inl 3) : OracleComp UnifCoin _)
      let c ← (UnifCoin.query (Sum.inr ()) : OracleComp UnifCoin _)
      if c = true then pure i.val else pure 0), r ≤ 3 := by
  pvcgen
  exact Fin.is_le i

example [OracleSpec.AnswerMeasure spec] [OracleSpec.AnswerMeasure spec']
    (t : ι) (t' : ι') (p : spec.Range t → spec'.Range t' → Prop) (hp : ∀ u v, p u v) :
    Pr{let u ← ((spec + spec').query (Sum.inl t) : OracleComp (spec + spec') _)
       let v ← ((spec + spec').query (Sum.inr t') : OracleComp (spec + spec') _)}[p u v] = 1 := by
  pvcgen
  simp [hp]

end VCVioTest.ProgramLogic.CoreVCGenSum
