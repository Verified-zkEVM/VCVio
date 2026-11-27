/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module
public import QuantumFoundations.Oracle.Basis
import Mathlib.Analysis.Matrix.PosDef

/-!
# Normalization of substates

A substate's real trace is its successful mass. Normalization divides its matrix by that
trace, returning the zero matrix when the trace is zero. The original matrix is exactly its
mass times the normalized matrix. These identities support analysis on conditional branches
while the operational semantics keeps every branch unnormalized.
-/

public section

open scoped ComplexOrder ENNReal

namespace Quantum.SubState

variable {A : Type*} [Fintype A]

/-- A positive semidefinite substate with zero real trace has zero matrix. -/
theorem matrix_eq_zero_of_trace_re_eq_zero (ρ : SubState A) (h : ρ.matrix.trace.re = 0) :
    ρ.matrix = 0 := by
  apply ρ.posSemidef.trace_eq_zero_iff.mp
  apply Complex.ext
  · exact h
  · exact (Complex.nonneg_iff.mp ρ.posSemidef.trace_nonneg).2.symm

/-- The successful mass of a substate. -/
@[expose]
noncomputable def mass (ρ : SubState A) : ℝ≥0∞ := ENNReal.ofReal ρ.matrix.trace.re

/-- Divide a substate by its real trace; zero-trace input gives the zero substate. -/
@[expose]
noncomputable def normalize (ρ : SubState A) : SubState A where
  matrix := Complex.ofReal ((ρ.matrix.trace.re)⁻¹) • ρ.matrix
  posSemidef := ρ.posSemidef.smul (by
    rw [Complex.nonneg_iff]
    exact ⟨inv_nonneg.mpr ρ.trace_re_nonneg, by simp⟩)
  trace_re_le_one := by
    rw [Matrix.trace_smul]
    simp only [smul_eq_mul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero]
    by_cases h : ρ.matrix.trace.re = 0
    · simp [h]
    · rw [inv_mul_cancel₀ h]

/-- The matrix of the normalized substate. -/
@[simp]
theorem matrix_normalize (ρ : SubState A) :
    ρ.normalize.matrix = Complex.ofReal ((ρ.matrix.trace.re)⁻¹) • ρ.matrix := rfl

/-- Nonzero-trace normalization has real trace one. -/
theorem trace_re_normalize_of_ne_zero (ρ : SubState A) (h : ρ.matrix.trace.re ≠ 0) :
    ρ.normalize.matrix.trace.re = 1 := by
  rw [matrix_normalize, Matrix.trace_smul]
  simp only [smul_eq_mul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero]
  exact inv_mul_cancel₀ h

/-- Recover the original matrix by multiplying normalization by the original real trace. -/
theorem matrix_eq_trace_re_smul_normalize (ρ : SubState A) :
    ρ.matrix = (ρ.matrix.trace.re : ℂ) • ρ.normalize.matrix := by
  by_cases h : ρ.matrix.trace.re = 0
  · rw [matrix_eq_zero_of_trace_re_eq_zero ρ h]
    simp
  · rw [matrix_normalize, smul_smul, ← Complex.ofReal_mul, mul_inv_cancel₀ h,
      Complex.ofReal_one, one_smul]

/-- Taking a partial trace preserves successful mass. -/
theorem mass_traceRight {B : Type*} [Fintype B] (ρ : SubState (A × B)) :
    ρ.traceRight.mass = ρ.mass := by
  unfold mass
  rw [matrix_traceRight, MatrixMap.trace_traceRight]

/-- A trivial private factor carries no correlations to discard: its reduced state and
unique basis state reconstruct the entire original joint substate. -/
theorem prod_traceRight_basis_unit (ρ : SubState (A × Unit)) :
    ρ.traceRight.prod (SubState.basis ()) = ρ := by
  apply SubState.ext
  ext ⟨a, u⟩ ⟨b, v⟩
  cases u
  cases v
  simp [matrix_prod, matrix_traceRight, MatrixMap.traceRight_apply]

end Quantum.SubState
