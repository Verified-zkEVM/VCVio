/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import VCVio.ProgramLogic.Unary.WP.LowerSpecs

/-!
# Core `vcgen` on oracle computations

Core `vcgen` with the `@[spec]` rules of `VCVio.ProgramLogic.Unary.WP.NecessarySpecs` and
`VCVio.ProgramLogic.Unary.WP.LowerSpecs`: uniform draws, `$[0..n]`, replicated draws and lifts in
the necessary reading; the exact rules of the lower reading, whose verification conditions keep
the averages of the draws; and the pointwise rules of `OracleComp.Lower.Pointwise`, which descend
through every draw, also through a `StateT` layer.
-/

public section

namespace VCVioTest.ProgramLogic.CoreVCGen

open OracleSpec OracleComp OracleComp.ProgramLogic Std.WP ENNReal

set_option experimental.vcgen true

section Necessary
open scoped OracleComp.Necessary

example : ⦃ True ⦄ (do let b ← $ᵗ Bool; let c ← $ᵗ Bool; pure (b || c || true) : ProbComp Bool)
    ⦃ fun r => r = true ⦄ := by
  vcgen
  simp

example (n : ℕ) : ⦃ True ⦄ ($[0..n]) ⦃ fun i => i.val ≤ n ⦄ := by
  vcgen
  omega

example : ⦃ True ⦄ ($ᵗ Bool).replicate 3 ⦃ fun xs => xs.length = 3 ⦄ := by
  vcgen
  grind

end Necessary

-- A quantitative triple carries its WP instance even with the necessary reading in scope.
open scoped OracleComp.Necessary in
example (post : Bool → ℝ≥0∞) :
    OracleComp.ProgramLogic.Triple ((∑' b, post b) / Nat.card Bool)
      (do let b ← $ᵗ Bool; pure b : ProbComp Bool) post := by
  vcgen

section Lower
open scoped OracleComp.Lower

variable {ι : Type} {spec : OracleSpec ι} [OracleSpec.AnswerMeasure spec]

/-- Integrate the continuations of a query, even when its eventual results have no chosen
measurable space. -/
example {α : Type} (t : spec.Domain) (k : spec.Range t → OracleComp spec α) (post : α → ℝ≥0∞) :
    OracleComp.ProgramLogic.wp (queryBind t k) post =
      ∫⁻ u, OracleComp.ProgramLogic.wp (k u) post ∂OracleSpec.AnswerMeasure.toMeasure t := by
  simp only [wp_eq_wpFold]
  exact PFunctor.FreeM.wpFold_liftBind (P := spec.toPFunctor) _ t k post

example (t : spec.Domain) (p : spec.Range t → Prop) :
    ⦃ ∫⁻ u, propInd (p u) ∂OracleSpec.AnswerMeasure.toMeasure t ⦄
      (do let u ← (query t : OracleComp spec _); pure u)
    ⦃ fun u => propInd (p u) ⦄ := by
  vcgen

example : ⦃ 2⁻¹ ⦄ ($ᵗ Bool) ⦃ fun b => propInd (b = true) ⦄ := by
  vcgen
  simp [propInd]

example : ⦃ 4⁻¹ ⦄ (do let b ← $ᵗ Bool; let c ← $ᵗ Bool; pure (b && c) : ProbComp Bool)
    ⦃ fun r => propInd (r = true) ⦄ := by
  vcgen
  norm_num [OracleComp.Lower.wp_uniformSample_eq_tsum, propInd, ENNReal.div_eq_inv_mul,
    Finset.filter_insert, Finset.filter_singleton, ← ENNReal.mul_inv]

open scoped OracleComp.Lower.Pointwise in
example : ⦃ 1 ⦄ (do let b ← $ᵗ Bool; let c ← $ᵗ Bool; pure (b || c || true) : ProbComp Bool)
    ⦃ fun r => propInd (r = true) ⦄ := by
  vcgen
  simp

open scoped OracleComp.Lower.Pointwise in
example (t : spec.Domain) (p : spec.Range t → spec.Range t → Prop) (hp : ∀ u v, p u v) :
    ⦃ 1 ⦄
      (do let u ← (query t : OracleComp spec _); let v ← (query t : OracleComp spec _); pure (u, v))
    ⦃ fun uv => propInd (p uv.1 uv.2) ⦄ := by
  vcgen
  simp [hp]

open scoped OracleComp.Lower.Pointwise in
example (post : Bool → ℕ → ℝ≥0∞) (h : ∀ b n, 1 ≤ post b n) :
    ⦃ fun _ => 1 ⦄
      (do let n ← get; let b ← liftM ($ᵗ Bool); set (n + 1); pure b : StateT ℕ ProbComp Bool)
    ⦃ post ⦄ := by
  vcgen
  exact h _ _

open scoped OracleComp.Lower.Pointwise in
example (oa : OracleComp spec Bool) (n : Nat) (post : List Bool → ℝ≥0∞) (p : ℝ≥0∞)
    (h : ∀ xs : List Bool, xs.length = n → (∀ x ∈ xs, x ∈ support oa) → p ≤ post xs) :
    ⦃ p ⦄ oa.replicate n ⦃ post ⦄ := by
  vcgen
  rename_i xs hxs
  exact h xs hxs.1 hxs.2

end Lower

section liftComp

variable {τ : Type} {superSpec : OracleSpec τ} [unifSpec ⊂ₒ superSpec] [unifSpec ˡ⊂ₒ superSpec]

open scoped OracleComp.Necessary in
example : ⦃ True ⦄ liftComp ($[0..3]) superSpec ⦃ fun i => i.val ≤ 3 ⦄ := by
  vcgen
  omega

open scoped OracleComp.Lower in
example [OracleSpec.UniformAnswerMeasure superSpec] :
    ⦃ 2⁻¹ ⦄ liftComp ($ᵗ Bool) superSpec ⦃ fun b => propInd (b = true) ⦄ := by
  vcgen
  simp [propInd]

end liftComp

end VCVioTest.ProgramLogic.CoreVCGen
