/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import VCVioFoxglove.Adequacy
public import Foxglove.Example

/-!
# Polynomial identity testing, from Foxglove to VCVio

Foxglove proves the root test and Schwartz–Zippel for coin programs (`Foxglove.Example`). The
same programs written in VCVio, over `unifSpec`, compile to those coin programs *by definition*
(`interp` is `simulateQ`, and the uniform oracle is rejection sampling `split`). So Foxglove's
specifications are specifications of the VCVio programs, and adequacy reads them in VCVio's
event notation.
-/

@[expose] public section

namespace Foxglove.Examples

open OracleComp OracleSpec Interp
open scoped ENNReal

variable {p : ℕ} [Fact p.Prime]

/-- **Root test** in VCVio: draw `x` uniformly from `ZMod p` and report whether `f x = 0`. -/
noncomputable def rootTest (f : Polynomial (ZMod p)) : ProbComp Bool := do
  let x ← (unifSpec.query (p - 1) : OracleComp unifSpec (Fin (p - 1 + 1)))
  pure (decide (f.eval (x.val : ZMod p) = 0))

/-- The VCVio program compiles to Foxglove's coin program. -/
theorem interp_rootTest (f : Polynomial (ZMod p)) :
    BernoulliInterpretable.interp (rootTest f) = Foxglove.rootTest f := rfl

/-- **The root test reports a root with probability `|roots f| / p`.** -/
theorem prEvent_rootTest (f : Polynomial (ZMod p)) (hf : f ≠ 0) :
    Pr{let b ← rootTest f}[b = true] = (f.roots.toFinset.card : ℝ≥0∞) / p := by
  obtain ⟨ν, hν, hD⟩ := exists_prEvent_of_wp (oa := rootTest f) (Foxglove.wp_rootTest_card f hf)
  rw [hD, hν]

/-- A uniform point of `(ZMod p)^n` in VCVio: `n` independent draws, recast. -/
noncomputable def unifVec : (n : ℕ) → ProbComp (Fin n → ZMod p)
  | 0 => pure Fin.elim0
  | n + 1 => do
    let x ← (unifSpec.query (p - 1) : OracleComp unifSpec (Fin (p - 1 + 1)))
    let xs ← unifVec n
    pure (Fin.cons (x.val : ZMod p) xs)

/-- **Multivariate root test** in VCVio. -/
noncomputable def mvRootTest {n : ℕ} (f : MvPolynomial (Fin n) (ZMod p)) : ProbComp Bool := do
  let xs ← unifVec n
  pure (decide (MvPolynomial.eval xs f = 0))

/-- The VCVio vector sampler compiles to Foxglove's. -/
theorem interp_unifVec : ∀ n : ℕ,
    BernoulliInterpretable.interp (unifVec (p := p) n) = Foxglove.unifVec n
  | 0 => rfl
  | n + 1 => by
    have ih := interp_unifVec n
    simp only [interp_eq_simulateQ] at ih ⊢
    simp only [unifVec, Foxglove.unifVec, simulateQ_bind, simulateQ_pure, simulateQ_spec_query, ih]
    rfl

/-- **Schwartz–Zippel in VCVio**: a nonzero `f` vanishes at a uniform point of `(ZMod p)^n` with
probability at most `deg f / p`. -/
theorem prEvent_mvRootTest_le {n : ℕ} {f : MvPolynomial (Fin n) (ZMod p)} (hf : f ≠ 0) :
    Pr{let b ← mvRootTest f}[b = true] ≤ f.totalDegree / p := by
  have hi : BernoulliInterpretable.interp (mvRootTest f) = Foxglove.mvRootTest f := by
    simp only [interp_eq_simulateQ, mvRootTest, Foxglove.mvRootTest, simulateQ_bind,
      simulateQ_pure, ← interp_unifVec n]
  have h := Foxglove.wp_mvRootTest hf
  rw [← hi] at h
  obtain ⟨ν, hν, hD⟩ := exists_prEvent_of_wp h
  exact (hD true).trans_le hν

end Foxglove.Examples
