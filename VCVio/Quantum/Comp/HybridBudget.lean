/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module
public import VCVio.Quantum.Comp.Hybrid
public import VCVio.Quantum.Foundations.Hybrid
public import VCVio.Quantum.Comp.RoundBound

/-!
# Hybrid bounds with total call and width budgets

The square-root hybrid argument charges the square root of a query weight at each call.
A total call budget bounds this sum by Cauchy–Schwarz without adding the per-port budgets;
this retains the round count when different paths choose different batch widths.

For a width-bounded program, a uniform trace estimate is needed only on ports within its
width cap. The resulting query-weight bound applies to arbitrary adaptive local instruments
and positive semidefinite input operators, including mixed and subnormalized states.
-/

public section

open Matrix
open scoped ENNReal ComplexOrder

universe u v u₁ v₁ w

namespace Quantum

namespace QuantumRuntime

variable {spec : QuantumOracleSpec.{u₁, v₁}} {L : LocalSig.{u, v}}
  {X : QReg → Type w} {A : QReg}

/-- Cauchy–Schwarz over calls of a program with a total call budget. The budget
counts all ports together, so variable-width signatures require no sum of per-port budgets. -/
theorem tsum_rpow_inv_two_queryWeight_le_of_isTotalQueryBound
    (R : QuantumRuntime spec) (I : L.Interp)
    {w : ∀ i, Matrix (spec.In i × R.D) (spec.In i × R.D) ℂ → ℝ≥0∞}
    {x : QuantumComp L spec X A} {n : ℕ} (hx : x.IsTotalQueryBound n)
    (ρ : Matrix (A × R.D) (A × R.D) ℂ) :
    ∑' j, R.queryWeight I w x ρ j ^ (2⁻¹ : ℝ) ≤
      ((n : ℝ≥0∞) * ∑' j, R.queryWeight I w x ρ j) ^ (2⁻¹ : ℝ) :=
  tsum_rpow_inv_two_le_of_cutoff _ n fun _ hj ↦
    R.queryWeight_eq_zero_of_isTotalQueryBound I hx hj ρ

section Width

variable {P : Type*} {In : P → QReg}

/-- If the weight of a width-at-most-`k` query is at most `C` times the input trace,
then the weight at every call of a width-bounded adaptive program satisfies the same bound.
No estimate is required on wider ports that the program cannot call. -/
theorem queryWeight_le_mul_of_isWidthBound (R : QuantumRuntime (uBatchSpec P In)) (I : L.Interp)
    {w : ∀ i, Matrix ((uBatchSpec P In).In i × R.D)
      ((uBatchSpec P In).In i × R.D) ℂ → ℝ≥0∞}
    (C : ℝ≥0∞) (k : ℕ)
    (hw : ∀ i, i.2 ≤ k → ∀ σ, σ.PosSemidef → w i σ ≤ C * ENNReal.ofReal σ.trace.re)
    {x : QuantumComp L (uBatchSpec P In) X A} (hx : x.IsWidthBound k)
    {ρ : Matrix (A × R.D) (A × R.D) ℂ} (hρ : ρ.PosSemidef) (j : ℕ) :
    R.queryWeight I w x ρ j ≤ C * ENNReal.ofReal ρ.trace.re := by
  induction x using QuantumComp.inductionOn generalizing j with
  | pure _ _ => simp
  | primBind _ o next ih =>
    rw [QuantumComp.isWidthBound_primBind_iff] at hx
    simp only [queryWeight_primBind]
    refine (ENNReal.tsum_le_tsum fun b ↦
      ih b (hx b) (((I o).frame R.D).posSemidef_branch_apply b hρ) j).trans ?_
    rw [ENNReal.tsum_mul_left]
    exact mul_le_mul le_rfl
      ((((I o).frame R.D).isCPTNIFamily).tsum_ofReal_trace_re_le hρ) bot_le bot_le
  | queryBind _ i E ℓ next ih =>
    rw [QuantumComp.isWidthBound_queryBind_iff] at hx
    cases j with
    | zero => simpa using hw i hx.1 _ (posSemidef_callInput ℓ hρ)
    | succ j =>
      simp only [queryWeight_queryBind_succ]
      refine (ENNReal.tsum_le_tsum fun r ↦
        ih r (hx.2 r) ((R.queryStep i E ℓ).posSemidef_branch_apply r hρ) j).trans ?_
      rw [ENNReal.tsum_mul_left]
      exact mul_le_mul le_rfl
        ((R.queryStep i E ℓ).isCPTNIFamily.tsum_ofReal_trace_re_le hρ) bot_le bot_le
end Width

end QuantumRuntime
end Quantum
