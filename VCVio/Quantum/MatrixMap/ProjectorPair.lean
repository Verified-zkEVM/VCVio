/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.Quantum.MatrixMap.OpNorm

/-!
# The distance between two projectors in a fixed angle

Two orthogonal projections `P` and `Q` with `P Q P = a P` and `Q P Q = a Q` for a real `a` are in
the position of two lines at angle `θ` with `cos² θ = a`, in every two-dimensional block
that they do not annihilate. The square of their difference, `M = (P - Q)²`, then satisfies
`M P = (1 - a) P`, `M Q = (1 - a) Q` and `M² = (1 - a) M`, so for `P ≠ 0` the operator norm of
`P - Q` is `√|1 - a|` exactly (`Matrix.l2_opNorm_sub_sq_eq_of_mul_mul_eq`).

This is the abstract step of the exact discrepancy of a consistency projector and its compressed
conjugate (eq. (26) of the notes on Chiesa, Di, Hu and Zheng, ePrint 2025/2166, Lemma 9.5): there
`a = (1 - 1/N)^(2d)`.

## Main results

* `Matrix.l2_opNorm_sub_sq_eq_of_mul_mul_eq`: `‖P - Q‖² = |1 - a|`.
* `Matrix.l2_opNorm_sub_sq_eq_one_sub_of_mul_mul_eq`: `‖P - Q‖² = 1 - a` for `a ≤ 1`.
-/

public section

open scoped Matrix.Norms.L2Operator

namespace Matrix

variable {n : Type*} [Fintype n]

/-- If `P` and `Q` are idempotent matrices with `P Q P = a P` for a real `a`, then
`(P - Q)²` acts on `P` as the scalar `1 - a`. -/
theorem sub_mul_sub_mul_left_eq {P Q : Matrix n n ℂ} (hPP : P * P = P) (hQQ : Q * Q = Q)
    {a : ℝ} (hPQP : P * Q * P = (a : ℂ) • P) :
    (P - Q) * (P - Q) * P = ((1 - a : ℝ) : ℂ) • P := by
  have h : (P - Q) * (P - Q) * P = P * P * P - P * Q * P - Q * P * P + Q * Q * P := by
    noncomm_ring
  rw [h, hPQP, hQQ, hPP, hPP, mul_assoc Q P P, hPP]
  push_cast
  rw [sub_smul, one_smul]
  abel

/-- If `P` and `Q` are idempotent matrices with `P Q P = a P` and `Q P Q = a Q` for a real `a`,
then `M = (P - Q)²` satisfies `M² = (1 - a) M`. -/
theorem sub_mul_sub_sq_eq {P Q : Matrix n n ℂ} (hPP : P * P = P) (hQQ : Q * Q = Q) {a : ℝ}
    (hPQP : P * Q * P = (a : ℂ) • P) (hQPQ : Q * P * Q = (a : ℂ) • Q) :
    (P - Q) * (P - Q) * ((P - Q) * (P - Q)) = ((1 - a : ℝ) : ℂ) • ((P - Q) * (P - Q)) := by
  have hP := sub_mul_sub_mul_left_eq hPP hQQ hPQP
  have hQ : (Q - P) * (Q - P) * Q = ((1 - a : ℝ) : ℂ) • Q :=
    sub_mul_sub_mul_left_eq hQQ hPP hQPQ
  have hQ' : (P - Q) * (P - Q) * Q = ((1 - a : ℝ) : ℂ) • Q := by
    rw [← hQ]
    noncomm_ring
  rw [← mul_assoc, mul_sub ((P - Q) * (P - Q)), hP, hQ', ← smul_sub, smul_mul_assoc]

/-- **Two projectors in a fixed angle.** If `P ≠ 0` and `Q` are orthogonal projections with
`P Q P = a P` and `Q P Q = a Q` for a real `a`, then `‖P - Q‖² = |1 - a|`. -/
theorem l2_opNorm_sub_sq_eq_of_mul_mul_eq [DecidableEq n] {P Q : Matrix n n ℂ} (hP : Pᴴ = P)
    (hPP : P * P = P) (hQ : Qᴴ = Q) (hQQ : Q * Q = Q) {a : ℝ}
    (hPQP : P * Q * P = (a : ℂ) • P)
    (hQPQ : Q * P * Q = (a : ℂ) • Q) (hP0 : P ≠ 0) :
    ‖P - Q‖ ^ 2 = |1 - a| := by
  set M := (P - Q) * (P - Q) with hM
  have hPQ : (P - Q)ᴴ = P - Q := by rw [conjTranspose_sub, hP, hQ]
  have hMH : Mᴴ = M := by rw [hM, conjTranspose_mul, hPQ]
  have hnormM : ‖M‖ = ‖P - Q‖ ^ 2 := by
    rw [sq, ← l2_opNorm_conjTranspose_mul_self, hPQ]
  have hc : ‖(((1 - a : ℝ) : ℂ))‖ = |1 - a| := by
    rw [Complex.norm_real, Real.norm_eq_abs]
  -- `‖M‖² = |1 - a| ‖M‖`
  have h1 : ‖M‖ * ‖M‖ = |1 - a| * ‖M‖ := by
    rw [← l2_opNorm_conjTranspose_mul_self, hMH, hM, sub_mul_sub_sq_eq hPP hQQ hPQP hQPQ,
      norm_smul, hc]
  -- `|1 - a| ‖P‖ ≤ ‖M‖ ‖P‖`
  have hPpos : 0 < ‖P‖ := norm_pos_iff.mpr hP0
  have h2 : |1 - a| ≤ ‖M‖ := by
    have h := l2_opNorm_mul M P
    rw [hM, sub_mul_sub_mul_left_eq hPP hQQ hPQP, norm_smul, hc] at h
    exact le_of_mul_le_mul_right h hPpos
  rw [← hnormM]
  nlinarith [abs_nonneg (1 - a), norm_nonneg M]

/-- **Two projectors in a fixed angle**, for `a ≤ 1`: `‖P - Q‖² = 1 - a`. -/
theorem l2_opNorm_sub_sq_eq_one_sub_of_mul_mul_eq [DecidableEq n] {P Q : Matrix n n ℂ}
    (hP : Pᴴ = P) (hPP : P * P = P) (hQ : Qᴴ = Q) (hQQ : Q * Q = Q) {a : ℝ} (ha : a ≤ 1)
    (hPQP : P * Q * P = (a : ℂ) • P) (hQPQ : Q * P * Q = (a : ℂ) • Q) (hP0 : P ≠ 0) :
    ‖P - Q‖ ^ 2 = 1 - a := by
  rw [l2_opNorm_sub_sq_eq_of_mul_mul_eq hP hPP hQ hQQ hPQP hQPQ hP0, abs_of_nonneg (by linarith)]

end Matrix
