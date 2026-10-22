/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import Mathlib.Analysis.Matrix.Hermitian
public import Mathlib.Analysis.Matrix.Order

/-!
# Positive semidefinite matrices and the trace pairing

For finite complex matrices, the pairing `Re tr (P * Q)` is nonnegative when `P` and `Q` are
positive semidefinite (`Matrix.PosSemidef.trace_mul_re_nonneg`). Conversely, a Hermitian matrix
`N` is positive semidefinite iff `Re tr (N * Q) ≥ 0` for every positive semidefinite `Q`
(`Matrix.posSemidef_iff_forall_trace_mul_re_nonneg`). The Hermitian hypothesis is essential:
the real trace pairing against Hermitian matrices cannot detect a skew-Hermitian part.
-/

public section

open scoped ComplexOrder
open Matrix

/-- The trace of a positive semidefinite complex matrix has nonnegative real part. -/
theorem Matrix.PosSemidef.trace_re_nonneg {n : Type*} [Fintype n] {ρ : Matrix n n ℂ}
    (hρ : ρ.PosSemidef) : 0 ≤ ρ.trace.re :=
  (Complex.nonneg_iff.mp hρ.trace_nonneg).1

/-- The trace of a product of two positive semidefinite complex matrices has nonnegative real
part. -/
theorem Matrix.PosSemidef.trace_mul_re_nonneg {n : Type*} [Fintype n] {P ρ : Matrix n n ℂ}
    (hP : P.PosSemidef) (hρ : ρ.PosSemidef) : 0 ≤ (P * ρ).trace.re := by
  classical
  open scoped MatrixOrder in
  obtain ⟨Y, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hρ.nonneg
  rw [star_eq_conjTranspose, ← Matrix.mul_assoc, Matrix.trace_mul_comm, ← Matrix.mul_assoc]
  exact (hP.mul_mul_conjTranspose_same Y).trace_re_nonneg

/-! ## Positivity through the trace pairing -/

namespace Matrix

variable {n : Type*} [Fintype n]

/-- A Hermitian complex matrix whose trace pairing with every positive semidefinite matrix has
nonnegative real part is positive semidefinite. -/
theorem IsHermitian.posSemidef_of_trace_mul_re_nonneg {N : Matrix n n ℂ} (hN : N.IsHermitian)
    (h : ∀ ρ : Matrix n n ℂ, ρ.PosSemidef → 0 ≤ (N * ρ).trace.re) : N.PosSemidef := by
  refine PosSemidef.of_dotProduct_mulVec_nonneg hN fun v ↦ ?_
  have h1 := h _ (posSemidef_vecMulVec_self_star v)
  rw [mul_vecMulVec, trace_vecMulVec, dotProduct_comm] at h1
  refine Complex.nonneg_iff.mpr ⟨h1, ?_⟩
  simpa using (hN.im_star_dotProduct_mulVec_self v).symm

/-- A complex matrix is positive semidefinite iff it is Hermitian and its trace pairing with every
positive semidefinite matrix has nonnegative real part. -/
theorem posSemidef_iff_forall_trace_mul_re_nonneg {N : Matrix n n ℂ} :
    N.PosSemidef ↔ N.IsHermitian ∧ ∀ ρ : Matrix n n ℂ, ρ.PosSemidef → 0 ≤ (N * ρ).trace.re :=
  ⟨fun hN ↦ ⟨hN.isHermitian, fun _ hρ ↦ hN.trace_mul_re_nonneg hρ⟩,
    fun h ↦ h.1.posSemidef_of_trace_mul_re_nonneg h.2⟩

end Matrix
