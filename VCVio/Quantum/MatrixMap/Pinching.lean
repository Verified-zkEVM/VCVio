/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import VCVio.Quantum.MatrixMap.OpNorm

/-!
# Pinching by a labelling of the basis, and label-controlled unitaries

A labelling `β : n → κ` of the basis of `ℂ^n` partitions it into the blocks `β ⁻¹' {i}`, with
diagonal projectors `P i = Matrix.labelProjector β i`. The label type `κ` is arbitrary.

* The **pinching** `Matrix.pinch β A` keeps the entries of `A` between basis vectors with the same
  label and sets the others to zero. For finite `κ` it is `∑ i, P i * A * P i`
  (`Matrix.pinch_eq_sum`).
* The **label-controlled** operator `Matrix.labelControlled β W` applies `W i` on the block of the
  label `i`: its row at a basis vector `a` is the row of `W (β a)`. For finite labels it is
  `∑ i, P i * W i` (`Matrix.labelControlled_eq_sum`).

The main result is the abstract form of Lemma 5.10 of Chiesa, Di, Hu and Zheng,
*How to Prove Post-Quantum Security for Succinct Non-Interactive Reductions* (ePrint 2025/2166):
if each `W i` is unitary, commutes with every `P j` and with `A`, then
`‖[labelControlled β W, A]‖ ≤ 2 ‖pinch β A - A‖`
(`Matrix.l2_opNorm_commutator_labelControlled_le`). It generalizes the two-block argument of
Chiesa, Manohar and Spooner (TCC 2019, Lemma 5.10) and of Don, Fehr, Majenz and Schaffner
(EUROCRYPT 2022, Theorem 3.1) to arbitrary partitions.

## Main results

* `Matrix.mul_pinch_mul_conjTranspose`: conjugating by an operator that maps each block into the
  block of the same label commutes with pinching.
* `Matrix.pinch_kronecker_one`: pinching by a label of the first register commutes with
  tensoring by the identity of the second.
* `Matrix.labelControlled_mem_unitaryGroup`, `Matrix.labelControlled_mul_pinch`.
* `Matrix.l2_opNorm_commutator_labelControlled_le`.
-/

public section

open scoped Matrix.Norms.L2Operator Kronecker

namespace Matrix

variable {n m p κ α : Type*}

/-! ## Pinching -/

section pinch

variable [DecidableEq κ] [Zero α]

/-- The pinching of `A` by the labelling `β`: the entries of `A` between basis vectors with
different labels are set to zero. For finite labels it is `∑ i, P i * A * P i`, with `P i` the
projector onto the basis vectors of label `i` (`Matrix.pinch_eq_sum`). -/
@[expose]
def pinch (β : n → κ) (A : Matrix n n α) : Matrix n n α :=
  of fun a b ↦ if β a = β b then A a b else 0

@[simp]
theorem pinch_apply (β : n → κ) (A : Matrix n n α) (a b : n) :
    pinch β A a b = if β a = β b then A a b else 0 :=
  rfl

/-- Pinching by a constant labelling does nothing. -/
@[simp]
theorem pinch_const (k : κ) (A : Matrix n n α) : pinch (fun _ ↦ k) A = A := by
  ext a b
  simp

/-- The diagonal projector onto the basis vectors of label `i`. -/
@[expose]
def labelProjector [One α] [DecidableEq n] (β : n → κ) (i : κ) : Matrix n n α :=
  diagonal fun a ↦ if β a = i then 1 else 0

end pinch

/-- For finite labels, pinching is the sum of the compressions `P i * A * P i` to the blocks. -/
theorem pinch_eq_sum [DecidableEq κ] [Fintype κ] [Fintype n] [DecidableEq n]
    [NonAssocSemiring α] (β : n → κ) (A : Matrix n n α) :
    pinch β A = ∑ i, labelProjector β i * A * labelProjector β i := by
  ext a b
  simp only [pinch_apply, labelProjector, sum_apply, mul_diagonal, diagonal_mul, ite_mul,
    one_mul, zero_mul, mul_ite, mul_one, mul_zero]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]

/-- Pinching by a label of the first register commutes with tensoring by the identity of the
second register. -/
theorem pinch_kronecker_one [DecidableEq κ] [MulZeroOneClass α] [DecidableEq p] (β : n → κ)
    (A : Matrix n n α) :
    pinch (fun q : n × p ↦ β q.1) (A ⊗ₖ (1 : Matrix p p α)) = pinch β A ⊗ₖ 1 := by
  ext ⟨a, e⟩ ⟨b, e'⟩
  simp only [pinch_apply, kroneckerMap_apply]
  split_ifs <;> simp

/-- Conjugating by an operator `U` that sends each block into the block of the same label
commutes with pinching. -/
theorem mul_pinch_mul_conjTranspose [DecidableEq κ] [Fintype n] [NonUnitalCommSemiring α]
    [StarRing α] (βm : m → κ) (βn : n → κ) {U : Matrix m n α}
    (hU : ∀ a b, U a b ≠ 0 → βm a = βn b) (A : Matrix n n α) :
    U * pinch βn A * Uᴴ = pinch βm (U * A * Uᴴ) := by
  ext a a'
  simp only [mul_apply, pinch_apply, conjTranspose_apply, Finset.sum_mul]
  by_cases h : βm a = βm a'
  · simp only [h, ite_true]
    refine Finset.sum_congr rfl fun c' _ ↦ Finset.sum_congr rfl fun c _ ↦ ?_
    by_cases hc : U a c = 0
    · simp [hc]
    by_cases hc' : U a' c' = 0
    · simp [hc']
    rw [← hU a c hc, ← hU a' c' hc']
    simp [h]
  · simp only [h, ite_false]
    refine Finset.sum_eq_zero fun c' _ ↦ Finset.sum_eq_zero fun c _ ↦ ?_
    by_cases hc : U a c = 0
    · simp [hc]
    by_cases hc' : U a' c' = 0
    · simp [hc']
    rw [← hU a c hc, ← hU a' c' hc']
    simp [h]

/-! ## Label-controlled operators -/

section labelControlled

/-- The operator that applies `W i` on the block of the label `i`: its row at a basis vector `a`
is the row of `W (β a)` at `a`. For finite labels it is `∑ i, P i * W i`
(`Matrix.labelControlled_eq_sum`), where the `W i` act on the same register as the `P i`; the
unitarity and commutator results below ask each `W i` to preserve the labels, that is, to map every
block into itself.

The tensor case is a specialization: on `n × p` with `β` a label of the first factor and
`W i = 1 ⊗ U i`, the operator is `∑ i, P i ⊗ U i`. -/
@[expose]
def labelControlled (β : n → κ) (W : κ → Matrix n n α) : Matrix n n α :=
  of fun a b ↦ W (β a) a b

@[simp]
theorem labelControlled_apply (β : n → κ) (W : κ → Matrix n n α) (a b : n) :
    labelControlled β W a b = W (β a) a b :=
  rfl

/-- For finite labels, a label-controlled operator is `∑ i, P i * W i`. -/
theorem labelControlled_eq_sum [DecidableEq κ] [Fintype κ] [Fintype n] [DecidableEq n]
    [NonAssocSemiring α] (β : n → κ) (W : κ → Matrix n n α) :
    labelControlled β W = ∑ i, labelProjector β i * W i := by
  ext a b
  simp only [labelControlled_apply, labelProjector, sum_apply, diagonal_mul, ite_mul, one_mul,
    zero_mul]
  simp [Finset.sum_ite_eq]

/-- A label-controlled operator whose members are unitaries mapping every block into itself is
unitary. -/
theorem labelControlled_mem_unitaryGroup [Fintype n] [DecidableEq n] [CommRing α] [StarRing α]
    {β : n → κ} {W : κ → Matrix n n α} (hW : ∀ k a b, W k a b ≠ 0 → β a = β b)
    (hU : ∀ k, W k ∈ unitaryGroup n α) : labelControlled β W ∈ unitaryGroup n α := by
  rw [mem_unitaryGroup_iff]
  ext a b
  simp only [mul_apply, star_apply, labelControlled_apply]
  by_cases h : β a = β b
  · have hk := congrFun (congrFun (mem_unitaryGroup_iff.mp (hU (β a))) a) b
    simp only [mul_apply, star_apply] at hk
    rw [← hk, h]
  · have hab : a ≠ b := fun e ↦ h (e ▸ rfl)
    rw [one_apply_ne hab]
    refine Finset.sum_eq_zero fun c _ ↦ ?_
    by_cases hc : W (β a) a c = 0
    · simp [hc]
    have hb : W (β b) b c = 0 := by
      by_contra hb
      exact h ((hW _ a c hc).trans (hW _ b c hb).symm)
    simp [hb]

/-- A label-controlled operator whose members map every block into itself and commute with `A`
commutes with the pinching of `A`. -/
theorem labelControlled_mul_pinch [DecidableEq κ] [Fintype n] [NonUnitalCommSemiring α] {β : n → κ}
    {W : κ → Matrix n n α} (hW : ∀ k a b, W k a b ≠ 0 → β a = β b) {A : Matrix n n α}
    (hA : ∀ k, W k * A = A * W k) :
    labelControlled β W * pinch β A = pinch β A * labelControlled β W := by
  ext a b
  have hl : (labelControlled β W * pinch β A) a b =
      if β a = β b then (W (β a) * A) a b else 0 := by
    simp only [mul_apply, labelControlled_apply, pinch_apply]
    split_ifs with h
    · refine Finset.sum_congr rfl fun c _ ↦ ?_
      by_cases hc : W (β a) a c = 0
      · simp [hc]
      rw [← hW _ a c hc]
      simp [h]
    · refine Finset.sum_eq_zero fun c _ ↦ ?_
      by_cases hc : W (β a) a c = 0
      · simp [hc]
      rw [← hW _ a c hc]
      simp [h]
  have hr : (pinch β A * labelControlled β W) a b =
      if β a = β b then (A * W (β a)) a b else 0 := by
    simp only [mul_apply, labelControlled_apply, pinch_apply]
    split_ifs with h
    · refine Finset.sum_congr rfl fun c _ ↦ ?_
      by_cases hc : W (β c) c b = 0
      · have hc' : W (β a) c b = 0 := by
          by_contra hc'
          have hcb := hW _ c b hc'
          rw [hcb, ← h] at hc
          exact hc' hc
        simp [hc, hc']
      · have hcb : β c = β a := (hW _ c b hc).trans h.symm
        rw [hcb]
        simp
    · refine Finset.sum_eq_zero fun c _ ↦ ?_
      by_cases hc : W (β c) c b = 0
      · simp [hc]
      rw [hW _ c b hc]
      simp [h]
  rw [hl, hr, hA]

end labelControlled

/-! ## The commutator bound -/

variable {𝕜 : Type*} [RCLike 𝕜] [DecidableEq κ] [Fintype n] [DecidableEq n]

/-- **Abstract form of Lemma 5.10 of ePrint 2025/2166.** Let `W i` be unitaries that map every
block of the labelling `β` into itself and commute with `A`. Then the commutator of `A` with the
label-controlled unitary `V = ∑ i, P i * W i` is at most twice the distance from `A` to its
pinching: `‖V A - A V‖ ≤ 2 ‖pinch β A - A‖`. -/
theorem l2_opNorm_commutator_labelControlled_le {β : n → κ} {W : κ → Matrix n n 𝕜}
    (hW : ∀ k a b, W k a b ≠ 0 → β a = β b) (hU : ∀ k, W k ∈ unitaryGroup n 𝕜)
    {A : Matrix n n 𝕜} (hA : ∀ k, W k * A = A * W k) :
    ‖labelControlled β W * A - A * labelControlled β W‖ ≤ 2 * ‖pinch β A - A‖ := by
  set V := labelControlled β W
  have hV : ‖V‖ ≤ 1 := l2_opNorm_le_one_of_conjTranspose_mul_self <|
    mem_unitaryGroup_iff'.mp (labelControlled_mem_unitaryGroup hW hU)
  have hVQ := labelControlled_mul_pinch hW hA
  have e : V * A - A * V = V * (A - pinch β A) + (pinch β A - A) * V := by
    rw [Matrix.mul_sub, Matrix.sub_mul, hVQ]
    abel
  rw [e]
  calc ‖V * (A - pinch β A) + (pinch β A - A) * V‖
      ≤ ‖V‖ * ‖A - pinch β A‖ + ‖pinch β A - A‖ * ‖V‖ :=
        (norm_add_le _ _).trans (add_le_add (l2_opNorm_mul _ _) (l2_opNorm_mul _ _))
    _ ≤ 1 * ‖pinch β A - A‖ + ‖pinch β A - A‖ * 1 := by
        rw [norm_sub_rev]
        gcongr
    _ = 2 * ‖pinch β A - A‖ := by ring

end Matrix
