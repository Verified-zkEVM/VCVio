/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import VCVio.EvalDist.Expectation

/-!
# `expectedValue` as a Lebesgue integral

`VCVio.EvalDist.Expectation` defines `expectedValue mx g` as `∑' x, Pr[= x | mx] * g x`. This
module identifies that discrete spelling with the `lintegral` against the primary evaluation
measure `𝒟[mx]`, for every semantics that satisfies the façade bridge
`DiscreteEvalDistCompatible`.

`lintegral_evalDist` is an explicit compatibility equation. Native integrals retain their
measure-theoretic normal form under `simp`; compatibility proofs can rewrite to the discrete
expectation when needed. Opening `ProbComp.DiscreteCompatibility` selects that simp direction
locally. `expectedValue_iSup` transports monotone convergence across this equation.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

universe u v

namespace OracleComp.EvalDist

variable {α : Type u} {m : Type u → Type v} [MonadLiftT m SPMF] [EvalDistSemantics m]
  [DiscreteEvalDistCompatible m] [MeasurableSpace α] [DiscreteMeasurableSpace α]

/-- An integral against a discrete denoted measure agrees with the scalar expectation. -/
theorem lintegral_evalDist (mx : m α) (g : α → ℝ≥0∞) :
    ∫⁻ x, g x ∂𝒟[mx] = expectedValue mx g :=
  DiscreteEvalDistCompatible.lintegral_evalDist mx Measurable.of_discrete

/-- **Monotone convergence** for VCVio expectations. -/
theorem expectedValue_iSup (mx : m α) (g : ℕ → α → ℝ≥0∞) (hg : Monotone g) :
    expectedValue mx (fun x => ⨆ n, g n x) = ⨆ n, expectedValue mx (g n) := by
  simp only [← lintegral_evalDist]
  exact lintegral_iSup (fun _ => Measurable.of_discrete) hg

end OracleComp.EvalDist

scoped[ProbComp.DiscreteCompatibility] attribute [simp high]
  OracleComp.EvalDist.lintegral_evalDist
