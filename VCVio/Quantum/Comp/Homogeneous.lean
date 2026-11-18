/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module
public import VCVio.Quantum.Comp.Runtime
public import VCVio.Quantum.Foundations.SubState

/-!
# Homogeneity of quantum observations

Every observed run scales linearly with a nonnegative scalar in its input matrix, including
stateful runtimes and outcome-dependent final registers. Normalizing an input for analysis
therefore factors out precisely its successful mass. Observations retain the original
unnormalized input mass.
-/

public section

open MeasureTheory Matrix
open scoped ENNReal Kronecker

namespace Quantum.QuantumRuntime

universe u v u₁ v₁ w
variable {spec : QuantumOracleSpec.{u₁, v₁}} {L : LocalSig.{u, v}}
  {W : QReg → Type w} {A : QReg}

/-- Matrix scaling by a nonnegative real scales every observed run by the same factor. -/
theorem evalDistMap_eq_smul_of_matrix_eq_smul (R : QuantumRuntime spec) (I : L.Interp)
    (x : QuantumComp L spec W A) (ρ σ : SubState A) (c : ℝ) (hc : 0 ≤ c)
    (hρ : ρ.matrix = (c : ℂ) • σ.matrix)
    {γ : Type*} [MeasurableSpace γ] (f : (Σ B, W B) → γ) :
    R.evalDistMap I x ρ f = ENNReal.ofReal c • R.evalDistMap I x σ f := by
  ext s hs
  rw [Measure.smul_apply, R.evalDistMap_apply I x ρ f hs,
    R.evalDistMap_apply I x σ f hs, smul_eq_mul, ← ENNReal.tsum_mul_left]
  apply tsum_congr
  intro leaf
  rw [R.matrix_jointPost, R.matrix_jointPost, hρ, Matrix.smul_kronecker,
    map_smul, Matrix.trace_smul]
  simp only [smul_eq_mul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero, ENNReal.ofReal_mul hc, mul_assoc]

/-- An observed run is its normalized-input law multiplied by the input's successful mass. -/
theorem evalDistMap_eq_mass_smul_normalize (R : QuantumRuntime spec) (I : L.Interp)
    (x : QuantumComp L spec W A) (ρ : SubState A)
    {γ : Type*} [MeasurableSpace γ] (f : (Σ B, W B) → γ) :
    R.evalDistMap I x ρ f = ρ.mass • R.evalDistMap I x ρ.normalize f :=
  R.evalDistMap_eq_smul_of_matrix_eq_smul I x ρ ρ.normalize ρ.matrix.trace.re
    ρ.trace_re_nonneg ρ.matrix_eq_trace_re_smul_normalize f

/-- The same homogeneity identity evaluated at an arbitrary event. -/
theorem evalDistMap_apply_eq_mass_mul_normalize (R : QuantumRuntime spec) (I : L.Interp)
    (x : QuantumComp L spec W A) (ρ : SubState A)
    {γ : Type*} [MeasurableSpace γ] (f : (Σ B, W B) → γ) (s : Set γ) :
    R.evalDistMap I x ρ f s = ρ.mass * R.evalDistMap I x ρ.normalize f s := by
  rw [evalDistMap_eq_mass_smul_normalize, Measure.smul_apply, smul_eq_mul]

end Quantum.QuantumRuntime
