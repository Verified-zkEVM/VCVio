/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import VCVio.Quantum.MatrixMap.Pinching

/-!
# Commutators with label-controlled unitaries through label-preserving approximations

Let `β : n → κ` label the basis of `𝕜^n`, and let `V = labelControlled β W` be the
label-controlled operator of unitaries `W k` that preserve the labels and commute with a matrix
`A`. `Matrix.l2_opNorm_commutator_labelControlled_le` bounds `‖[V, A]‖` by twice the distance from
`A` to its pinching. This file replaces the pinching by **any** label-preserving matrix `S`
(`pinch β S = S`):

  `‖[V, A]‖ ≤ 2 ‖A - S‖` (`Matrix.l2_opNorm_commutator_labelControlled_le_of_pinch_eq`).

The pinching of `A` is one such `S`, but it is not the closest one in general. The `W k` are not
assumed to commute with `S`; the proof replaces `S` by a label-preserving matrix that does.

## Proof

Among the label-preserving matrices `X` with `‖A - X‖ ≤ ‖A - S‖`, a compact set, choose `S₀` of
least squared Frobenius norm `‖S₀‖_F² = re (trace (S₀ᴴ S₀))`. Conjugation by `W k` maps this set
to itself, because `W k` preserves the labels and commutes with `A`, and it preserves the squared
Frobenius norm. By the parallelogram law the midpoint of `S₀` and `W k S₀ (W k)ᴴ`, which lies in
the set, has squared Frobenius norm `‖S₀‖_F² - ‖S₀ - W k S₀ (W k)ᴴ‖_F² / 4`, so minimality forces
`W k S₀ = S₀ W k`. Then
`S₀` commutes with `V` (`Matrix.labelControlled_mul_pinch`), and
`[V, A] = [V, A - S₀]` has norm at most `2 ‖A - S₀‖ ≤ 2 ‖A - S‖`.

## Main results

* `Matrix.pinch_eq_self_iff`: a matrix is label preserving if and only if its nonzero entries
  stay inside the blocks.
* `Matrix.l2_opNorm_pinch_le`: pinching does not increase the operator norm.
* `Matrix.l2_opNorm_commutator_labelControlled_le_of_pinch_eq`.

## References

* A. Chiesa, Z. Di, Z. Hu and Y. Zheng, *How to Prove Post-Quantum Security for Succinct
  Non-Interactive Reductions*, ePrint 2025/2166, Lemma 5.10, of which this is a strengthening.
* A. Chiesa, P. Manohar and N. Spooner, *Succinct Arguments in the Quantum Random Oracle Model*,
  TCC 2019, Lemma 5.10.
* J. Don, S. Fehr, C. Majenz and C. Schaffner, *Online-Extractability in the Quantum Random-Oracle
  Model*, EUROCRYPT 2022, Theorem 3.1.
-/

public section

open scoped Matrix.Norms.L2Operator Kronecker

namespace Matrix

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n]

/-! ## The squared Frobenius norm through the trace -/


omit [DecidableEq n] in
/-- The real part of `trace (Xᴴ X)` is the sum of the squared entries of `X`. -/
theorem re_trace_conjTranspose_mul_self (X : Matrix n n 𝕜) :
    RCLike.re (trace (Xᴴ * X)) = ∑ i, ∑ j, ‖X i j‖ ^ 2 := by
  simp only [trace, diag_apply, mul_apply, conjTranspose_apply, RCLike.star_def, RCLike.conj_mul,
    map_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
  rw [← RCLike.ofReal_pow, RCLike.ofReal_re]

omit [DecidableEq n] in
/-- A matrix with `re (trace (Xᴴ X)) ≤ 0` vanishes. -/
theorem eq_zero_of_re_trace_conjTranspose_mul_self_nonpos {X : Matrix n n 𝕜}
    (h : RCLike.re (trace (Xᴴ * X)) ≤ 0) : X = 0 := by
  rw [re_trace_conjTranspose_mul_self] at h
  have h0 : ∀ i j, ‖X i j‖ ^ 2 = 0 := by
    have hs := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ ↦ Finset.sum_nonneg fun j _ ↦
      sq_nonneg ‖X i j‖)).mp (le_antisymm h (Finset.sum_nonneg fun i _ ↦
        Finset.sum_nonneg fun j _ ↦ sq_nonneg _))
    intro i j
    exact (Finset.sum_eq_zero_iff_of_nonneg (fun j _ ↦ sq_nonneg ‖X i j‖)).mp
      (hs i (Finset.mem_univ _)) j (Finset.mem_univ _)
  ext i j
  simpa using h0 i j

/-- Conjugating by an isometry preserves the squared Frobenius norm `re (trace (Xᴴ X))`. -/
theorem re_trace_conjTranspose_mul_self_mul_mul_conjTranspose {U : Matrix n n 𝕜}
    (hU : Uᴴ * U = 1) (X : Matrix n n 𝕜) :
    RCLike.re (trace ((U * X * Uᴴ)ᴴ * (U * X * Uᴴ))) = RCLike.re (trace (Xᴴ * X)) := by
  have e : (U * X * Uᴴ)ᴴ * (U * X * Uᴴ) = U * (Xᴴ * X) * Uᴴ := by
    rw [conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Uᴴ U, hU, Matrix.one_mul]
  rw [e, trace_mul_comm, ← Matrix.mul_assoc, hU, Matrix.one_mul]

omit [DecidableEq n] in
/-- The parallelogram law for the squared Frobenius norm `re (trace (Xᴴ X))`. -/
theorem re_trace_parallelogram (X Y : Matrix n n 𝕜) :
    RCLike.re (trace ((X + Y)ᴴ * (X + Y))) + RCLike.re (trace ((X - Y)ᴴ * (X - Y))) =
      2 * RCLike.re (trace (Xᴴ * X)) + 2 * RCLike.re (trace (Yᴴ * Y)) := by
  have e : (X + Y)ᴴ * (X + Y) + (X - Y)ᴴ * (X - Y) = Xᴴ * X + Xᴴ * X + (Yᴴ * Y + Yᴴ * Y) := by
    rw [conjTranspose_add, conjTranspose_sub]; noncomm_ring
  rw [← map_add, ← trace_add, e, trace_add, trace_add, trace_add, map_add, map_add, map_add]
  ring

omit [DecidableEq n] in
/-- Halving a matrix divides its squared Frobenius norm `re (trace (Xᴴ X))` by `4`. -/
theorem re_trace_half_smul (X : Matrix n n 𝕜) :
    RCLike.re (trace (((2 : 𝕜)⁻¹ • X)ᴴ * ((2 : 𝕜)⁻¹ • X))) = RCLike.re (trace (Xᴴ * X)) / 4 := by
  rw [conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, trace_smul, smul_eq_mul]
  have : star (2 : 𝕜)⁻¹ * (2 : 𝕜)⁻¹ = (((4 : ℝ)⁻¹ : ℝ) : 𝕜) := by
    rw [star_inv₀, star_ofNat, RCLike.ofReal_inv]; push_cast; ring
  rw [this, RCLike.re_ofReal_mul]
  ring

/-! ## Label-preserving matrices -/

section pinch

variable {κ : Type*} [DecidableEq κ]

omit [Fintype n] [DecidableEq n] in
/-- A matrix is fixed by pinching if and only if its nonzero entries stay inside the blocks. -/
theorem pinch_eq_self_iff {α : Type*} [Zero α] {β : n → κ} {X : Matrix n n α} :
    pinch β X = X ↔ ∀ a b, X a b ≠ 0 → β a = β b := by
  constructor
  · intro h a b hab
    by_contra hne
    rw [← h, pinch_apply, ite_eq_right (fun h' ↦ (hne h').elim)] at hab
    exact hab rfl
  · intro h
    ext a b
    rw [pinch_apply]
    split_ifs with hab
    · rfl
    · by_contra hne
      exact hab (h a b (Ne.symm hne))

omit [DecidableEq n] in
/-- Products of label-preserving matrices are label preserving. -/
theorem pinch_mul_of_pinch_eq {β : n → κ} {X Y : Matrix n n 𝕜} (hX : pinch β X = X)
    (hY : pinch β Y = Y) : pinch β (X * Y) = X * Y := by
  rw [pinch_eq_self_iff] at hX hY ⊢
  intro a b hab
  obtain ⟨c, -, hc⟩ := Finset.exists_ne_zero_of_sum_ne_zero hab
  exact (hX a c (left_ne_zero_of_mul hc)).trans (hY c b (right_ne_zero_of_mul hc))

omit [Fintype n] [DecidableEq n] in
/-- The adjoint of a label-preserving matrix is label preserving. -/
theorem pinch_conjTranspose_of_pinch_eq {β : n → κ} {X : Matrix n n 𝕜} (hX : pinch β X = X) :
    pinch β Xᴴ = Xᴴ := by
  rw [pinch_eq_self_iff] at hX ⊢
  intro a b hab
  exact (hX b a (by simpa [conjTranspose_apply] using hab)).symm

omit [Fintype n] [DecidableEq n] in
theorem pinch_add (β : n → κ) (X Y : Matrix n n 𝕜) :
    pinch β (X + Y) = pinch β X + pinch β Y := by
  ext a b; simp only [pinch_apply, add_apply]; split_ifs <;> simp

omit [Fintype n] [DecidableEq n] in
theorem pinch_smul (β : n → κ) (c : 𝕜) (X : Matrix n n 𝕜) :
    pinch β (c • X) = c • pinch β X := by
  ext a b; simp only [pinch_apply, smul_apply]; split_ifs <;> simp

/-- **Pinching is a contraction.** Pinching by any labelling does not increase the operator
norm. -/
theorem l2_opNorm_pinch_le (β : n → κ) (A : Matrix n n 𝕜) : ‖pinch β A‖ ≤ ‖A‖ := by
  refine l2_opNorm_le_of_sum_norm_mulVec_sq_le (norm_nonneg A) fun v ↦ ?_
  set w : κ → n → 𝕜 := fun k j ↦ if β j = k then v j else 0 with hw
  have hrow : ∀ i, (pinch β A *ᵥ v) i = (A *ᵥ w (β i)) i := fun i ↦ by
    simp only [mulVec, dotProduct, pinch_apply, hw]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    by_cases h : β i = β j
    · simp [h]
    · simp [h, Ne.symm h]
  set s := Finset.univ.image β
  have hsplit : ∀ g : n → ℝ, ∑ i, g i = ∑ k ∈ s, ∑ i, if β i = k then g i else 0 := fun g ↦ by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [Finset.sum_ite_eq]
    simp [s]
  calc ∑ i, ‖(pinch β A *ᵥ v) i‖ ^ 2
      = ∑ k ∈ s, ∑ i, if β i = k then ‖(A *ᵥ w k) i‖ ^ 2 else 0 := by
        rw [hsplit]
        refine Finset.sum_congr rfl fun k _ ↦ Finset.sum_congr rfl fun i _ ↦ ?_
        split_ifs with h
        · rw [hrow, h]
        · rfl
    _ ≤ ∑ k ∈ s, ∑ i, ‖(A *ᵥ w k) i‖ ^ 2 := by
        refine Finset.sum_le_sum fun k _ ↦ Finset.sum_le_sum fun i _ ↦ ?_
        split_ifs
        · exact le_rfl
        · positivity
    _ ≤ ∑ k ∈ s, ‖A‖ ^ 2 * ∑ j, ‖w k j‖ ^ 2 :=
        Finset.sum_le_sum fun k _ ↦ sum_norm_mulVec_sq_le A (w k)
    _ = ‖A‖ ^ 2 * ∑ j, ‖v j‖ ^ 2 := by
        rw [← Finset.mul_sum, hsplit fun j ↦ ‖v j‖ ^ 2]
        congr 1
        refine Finset.sum_congr rfl fun k _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
        simp only [hw]
        split_ifs <;> simp


/-- **Commutators through a label-preserving approximation.** Let `W k` be unitaries that preserve
the labels of `β` and commute with `A`, and let `S` be any label-preserving matrix. Then the
label-controlled unitary `V = labelControlled β W` satisfies `‖[V, A]‖ ≤ 2 ‖A - S‖`. -/
theorem l2_opNorm_commutator_labelControlled_le_of_pinch_eq {β : n → κ} {W : κ → Matrix n n 𝕜}
    (hW : ∀ k a b, W k a b ≠ 0 → β a = β b) (hU : ∀ k, W k ∈ unitaryGroup n 𝕜)
    {A : Matrix n n 𝕜} (hA : ∀ k, W k * A = A * W k) {S : Matrix n n 𝕜} (hS : pinch β S = S) :
    ‖labelControlled β W * A - A * labelControlled β W‖ ≤ 2 * ‖A - S‖ := by
  have : ProperSpace (Matrix n n 𝕜) := FiniteDimensional.proper_rclike 𝕜 _
  set c := ‖A - S‖
  set C : Set (Matrix n n 𝕜) := {X | pinch β X = X ∧ ‖A - X‖ ≤ c} with hC
  have hCc : IsCompact C := by
    refine Metric.isCompact_of_isClosed_isBounded ?_ (Metric.isBounded_closedBall (x := A)
      (r := c) |>.subset fun X hX ↦ ?_)
    · refine (isClosed_eq ?_ continuous_id).inter
        (isClosed_le (continuous_const.sub continuous_id).norm continuous_const)
      refine continuous_pi fun a ↦ continuous_pi fun b ↦ ?_
      simp only [pinch_apply]
      split_ifs
      · fun_prop
      · fun_prop
    · rw [Metric.mem_closedBall, dist_eq_norm, norm_sub_rev]
      exact hX.2
  obtain ⟨S₀, hS₀, hmin⟩ := hCc.exists_isMinOn ⟨S, hS, le_rfl⟩
    (show Continuous fun X : Matrix n n 𝕜 ↦ RCLike.re (trace (Xᴴ * X)) by fun_prop).continuousOn
  -- the minimizer commutes with every `W k`
  have hcomm : ∀ k, W k * S₀ = S₀ * W k := by
    intro k
    have hUU : (W k)ᴴ * W k = 1 := mem_unitaryGroup_iff'.mp (hU k)
    have hUU' : W k * (W k)ᴴ = 1 := mem_unitaryGroup_iff.mp (hU k)
    have hWk : pinch β (W k) = W k := pinch_eq_self_iff.mpr (hW k)
    have hS₁ : W k * S₀ * (W k)ᴴ ∈ C := by
      refine ⟨pinch_mul_of_pinch_eq (pinch_mul_of_pinch_eq hWk hS₀.1)
        (pinch_conjTranspose_of_pinch_eq hWk), ?_⟩
      have e : A - W k * S₀ * (W k)ᴴ = W k * (A - S₀) * (W k)ᴴ := by
        rw [Matrix.mul_sub, Matrix.sub_mul, hA k, Matrix.mul_assoc A, hUU', Matrix.mul_one]
      rw [e]
      exact (l2_opNorm_mul_mul_conjTranspose_le hUU _).trans hS₀.2
    have hmid : (2 : 𝕜)⁻¹ • (S₀ + W k * S₀ * (W k)ᴴ) ∈ C := by
      refine ⟨by rw [pinch_smul, pinch_add, hS₀.1, hS₁.1], ?_⟩
      have e : A - (2 : 𝕜)⁻¹ • (S₀ + W k * S₀ * (W k)ᴴ) =
          (2 : 𝕜)⁻¹ • ((A - S₀) + (A - W k * S₀ * (W k)ᴴ)) := by module
      rw [e, norm_smul, norm_inv, RCLike.norm_ofNat]
      have := norm_add_le (A - S₀) (A - W k * S₀ * (W k)ᴴ)
      linarith [hS₀.2, hS₁.2]
    have h₁ : RCLike.re (trace (S₀ᴴ * S₀)) ≤
        RCLike.re (trace (((2 : 𝕜)⁻¹ • (S₀ + W k * S₀ * (W k)ᴴ))ᴴ *
          ((2 : 𝕜)⁻¹ • (S₀ + W k * S₀ * (W k)ᴴ)))) := hmin hmid
    rw [re_trace_half_smul] at h₁
    have h₂ := re_trace_parallelogram S₀ (W k * S₀ * (W k)ᴴ)
    rw [re_trace_conjTranspose_mul_self_mul_mul_conjTranspose hUU] at h₂
    have h₃ := eq_zero_of_re_trace_conjTranspose_mul_self_nonpos (X := S₀ - W k * S₀ * (W k)ᴴ)
      (by linarith)
    rw [sub_eq_zero] at h₃
    calc W k * S₀ = W k * S₀ * ((W k)ᴴ * W k) := by rw [hUU, Matrix.mul_one]
      _ = S₀ * W k := by rw [← Matrix.mul_assoc, ← h₃]
  have hVS : labelControlled β W * S₀ = S₀ * labelControlled β W := by
    have h := labelControlled_mul_pinch hW (A := S₀) hcomm
    rwa [hS₀.1] at h
  have hV : ‖labelControlled β W‖ ≤ 1 := l2_opNorm_le_one_of_conjTranspose_mul_self <|
    mem_unitaryGroup_iff'.mp (labelControlled_mem_unitaryGroup hW hU)
  have e : labelControlled β W * A - A * labelControlled β W =
      labelControlled β W * (A - S₀) - (A - S₀) * labelControlled β W := by
    rw [Matrix.mul_sub, Matrix.sub_mul, hVS]; abel
  rw [e]
  calc _ ≤ ‖labelControlled β W‖ * ‖A - S₀‖ + ‖A - S₀‖ * ‖labelControlled β W‖ :=
        (norm_sub_le _ _).trans (add_le_add (l2_opNorm_mul _ _) (l2_opNorm_mul _ _))
    _ ≤ 1 * c + c * 1 := by gcongr; exacts [hS₀.2, hS₀.2]
    _ = 2 * c := by ring

/-! ## A label of the first register and an ancilla -/

variable {m : Type*} [Fintype m] [DecidableEq m]

/-- **Commutators with an ancilla.** Let `S` preserve the labels of `β`, and let `W k` be
unitaries on `n × m` that preserve the label of the first register and commute with `A ⊗ 1_m`.
Then `‖[V, A ⊗ 1_m]‖ ≤ 2 ‖A - S‖` for `V = labelControlled (β ∘ Prod.fst) W`. -/
theorem l2_opNorm_commutator_labelControlled_kronecker_one_le {β : n → κ} {A S : Matrix n n 𝕜}
    (hS : pinch β S = S) {W : κ → Matrix (n × m) (n × m) 𝕜}
    (hW : ∀ k a b, W k a b ≠ 0 → β a.1 = β b.1) (hU : ∀ k, W k ∈ unitaryGroup (n × m) 𝕜)
    (hA : ∀ k, W k * (A ⊗ₖ (1 : Matrix m m 𝕜)) = (A ⊗ₖ (1 : Matrix m m 𝕜)) * W k) :
    ‖labelControlled (fun a ↦ β a.1) W * (A ⊗ₖ (1 : Matrix m m 𝕜)) -
        (A ⊗ₖ (1 : Matrix m m 𝕜)) * labelControlled (fun a ↦ β a.1) W‖ ≤ 2 * ‖A - S‖ := by
  have hS' : pinch (fun a : n × m ↦ β a.1) (S ⊗ₖ (1 : Matrix m m 𝕜)) = S ⊗ₖ 1 := by
    rw [pinch_kronecker_one, hS]
  refine (l2_opNorm_commutator_labelControlled_le_of_pinch_eq hW hU hA hS').trans ?_
  have hsub : A ⊗ₖ (1 : Matrix m m 𝕜) - S ⊗ₖ (1 : Matrix m m 𝕜) =
      (A - S) ⊗ₖ (1 : Matrix m m 𝕜) := by
    ext a b
    simp only [Matrix.sub_apply, kroneckerMap_apply, sub_mul]
  rw [hsub]
  gcongr
  exact l2_opNorm_kronecker_one_le _

/-- **Purified measurements.** Let `S` preserve the labels of `β`, and let `U k` be any unitaries
on an ancilla `m`. Then `V = ∑ k, P k ⊗ U k`, the label-controlled operator of the `1 ⊗ U k`,
satisfies `‖[V, A ⊗ 1_m]‖ ≤ 2 ‖A - S‖`. -/
theorem l2_opNorm_commutator_labelControlled_one_kronecker_le {β : n → κ}
    {A S : Matrix n n 𝕜} (hS : pinch β S = S) {U : κ → Matrix m m 𝕜}
    (hU : ∀ k, U k ∈ unitaryGroup m 𝕜) :
    ‖labelControlled (fun a ↦ β a.1) (fun k ↦ (1 : Matrix n n 𝕜) ⊗ₖ U k) *
          (A ⊗ₖ (1 : Matrix m m 𝕜)) -
        (A ⊗ₖ (1 : Matrix m m 𝕜)) *
          labelControlled (fun a ↦ β a.1) (fun k ↦ (1 : Matrix n n 𝕜) ⊗ₖ U k)‖ ≤
      2 * ‖A - S‖ := by
  refine l2_opNorm_commutator_labelControlled_kronecker_one_le hS ?_ ?_ ?_
  · intro k a b h
    have hab : a.1 = b.1 := by
      by_contra hne
      simp [kroneckerMap_apply, one_apply_ne hne] at h
    rw [hab]
  · intro k
    rw [mem_unitaryGroup_iff, star_eq_conjTranspose, conjTranspose_kronecker, conjTranspose_one,
      ← mul_kronecker_mul, Matrix.one_mul, ← star_eq_conjTranspose,
      mem_unitaryGroup_iff.mp (hU k), one_kronecker_one]
  · intro k
    rw [← mul_kronecker_mul, ← mul_kronecker_mul, Matrix.one_mul, Matrix.mul_one, Matrix.mul_one,
      Matrix.one_mul]

end pinch

end Matrix
