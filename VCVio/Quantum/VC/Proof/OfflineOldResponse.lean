/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.Quantum.VC.Proof.OfflineOldPartial
public import VCVio.Quantum.VC.Proof.OfflineOldLeaves

/-!
# Retained measurement branches and coherent response registers

The Stinespring matrix of a checked label measurement is exactly the coherent label copy
with the same checks. This identifies the sum of branch weights before using a unitary
factorization of the response register.
-/

public section

open Matrix
open scoped ComplexOrder Kronecker ENNReal
namespace Quantum.MatrixMap

variable {A B C Z : Type*}

/-- Stacking a Kraus family commutes with the common operators before and after it. -/
theorem stinespring_sandwich [Fintype A] [Fintype B] [Fintype Z] [DecidableEq Z]
    (K : Z → Matrix B A ℂ) (L : Matrix C B ℂ)
    (R : Matrix A A ℂ) :
    stinespring (fun z ↦ L * K z * R) =
      (L ⊗ₖ (1 : Matrix Z Z ℂ)) * stinespring K * R := by
  ext ⟨c, z⟩ a
  simp only [stinespring_apply, Matrix.mul_apply, Fintype.sum_prod_type,
    kroneckerMap_apply, one_apply, mul_ite, mul_one, mul_zero, ite_mul, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, ite_true]

/-- The Stinespring matrix of label projectors coherently copies the label. -/
theorem stinespring_labelProjector [DecidableEq B] [DecidableEq Z] (β : B → Z) :
    stinespring (fun z ↦ (labelProjector β z : Matrix B B ℂ)) =
      basisMatrix (fun b ↦ (b, β b)) := by
  ext ⟨b, z⟩ a
  simp only [stinespring_apply, labelProjector, diagonal_apply, basisMatrix_apply,
    Prod.mk.injEq]
  by_cases h : b = a
  · subst a
    simp [eq_comm]
  · simp [h]

/-- Summing the branch weights equals the weight of their stacked Kraus matrix. -/
theorem tsum_conj_weight_eq_stinespring [Fintype A] [Fintype B] [Fintype Z]
    (K : Z → Matrix B A ℂ)
    {ρ : Matrix A A ℂ} (hρ : ρ.PosSemidef) :
    ∑' z, ENNReal.ofReal (conj (K z) ρ).trace.re =
      ENNReal.ofReal (conj (stinespring K) ρ).trace.re := by
  rw [tsum_fintype, ← ENNReal.ofReal_sum_of_nonneg
    (fun z _ ↦ ((isCP_conj _).posSemidef hρ).trace_re_nonneg)]
  congr 1
  rw [← Complex.re_sum, ← Matrix.trace_sum, ← LinearMap.sum_apply,
    sum_conj_apply_eq_traceRight, trace_traceRight]

/-- The measured difference of two checked label maps has precisely the coherent-copy weight. -/
theorem checked_label_difference_weight [Fintype B] [Fintype Z]
    [DecidableEq B] [DecidableEq Z] (β : B → Z)
    (Aa Ab Qa Qb : Matrix B B ℂ) {ρ : Matrix B B ℂ} (hρ : ρ.PosSemidef) :
    let T := basisMatrix (fun b ↦ (b, β b))
    (∑' z, ENNReal.ofReal (conj
      (Ab * labelProjector β z * Aa - Qb * labelProjector β z * Qa) ρ).trace.re) =
      ENNReal.ofReal (conj
        ((Ab ⊗ₖ (1 : Matrix Z Z ℂ)) * T * Aa -
          (Qb ⊗ₖ (1 : Matrix Z Z ℂ)) * T * Qa) ρ).trace.re := by
  rw [tsum_conj_weight_eq_stinespring _ hρ]
  have he (K L : Z → Matrix B B ℂ) :
      stinespring (fun z ↦ K z - L z) = stinespring K - stinespring L := rfl
  rw [he, stinespring_sandwich, stinespring_sandwich,
    stinespring_labelProjector]

/-- Injective encodings preserve each label projector. -/
theorem labelProjector_encode [DecidableEq B] [DecidableEq Z] {ι : Type*}
    [DecidableEq ι] (β : B → ι)
    (enc : ι → Z) (henc : Function.Injective enc) (i : ι) :
    (labelProjector (enc ∘ β) (enc i) : Matrix B B ℂ) = labelProjector β i := by
  simp only [labelProjector, Function.comp_apply, henc.eq_iff]

/-- The retained decoded outcomes are bounded by the coherent response weight. Unused
codewords contribute nonnegative weights. Decoded outcomes need no finiteness assumption. -/
theorem encoded_checked_difference_le [Fintype B] [Fintype Z]
    [DecidableEq B] [DecidableEq Z] {ι : Type*} [DecidableEq ι]
    (β : B → ι) (enc : ι → Z) (henc : Function.Injective enc)
    (Aa Ab Qa Qb : Matrix B B ℂ) {ρ : Matrix B B ℂ} (hρ : ρ.PosSemidef) :
    let T := basisMatrix (fun b ↦ (b, enc (β b)))
    (∑' i, ENNReal.ofReal (conj
      (Ab * labelProjector β i * Aa - Qb * labelProjector β i * Qa) ρ).trace.re) ≤
      ENNReal.ofReal (conj
        ((Ab ⊗ₖ (1 : Matrix Z Z ℂ)) * T * Aa -
          (Qb ⊗ₖ (1 : Matrix Z Z ℂ)) * T * Qa) ρ).trace.re := by
  have hh := ENNReal.tsum_comp_le_tsum_of_injective henc (fun z ↦ ENNReal.ofReal
    (conj (Ab * labelProjector (enc ∘ β) z * Aa -
      Qb * labelProjector (enc ∘ β) z * Qa) ρ).trace.re)
  simp only [labelProjector_encode β enc henc] at hh
  exact hh.trans_eq (checked_label_difference_weight (enc ∘ β) Aa Ab Qa Qb hρ)

/-- Unused response codewords have zero projector, including off the image of the encoder. -/
theorem labelProjector_encode_eq_zero [DecidableEq B] [DecidableEq Z] {ι : Type*}
    (β : B → ι) (enc : ι → Z) (z : Z) (hz : z ∉ Set.range enc) :
    (labelProjector (enc ∘ β) z : Matrix B B ℂ) = 0 := by
  have h (b : B) : enc (β b) ≠ z := fun he ↦ hz ⟨β b, he⟩
  simp [labelProjector, Function.comp_apply, h]

/-- The decoded branch sum equals the coherent response weight exactly. All unused
codewords vanish, so injective encodings need not be surjective. -/
theorem encoded_checked_difference_eq [Fintype B] [Fintype Z]
    [DecidableEq B] [DecidableEq Z] {ι : Type*} [DecidableEq ι]
    (β : B → ι) (enc : ι → Z) (henc : Function.Injective enc)
    (Aa Ab Qa Qb : Matrix B B ℂ) {ρ : Matrix B B ℂ} (hρ : ρ.PosSemidef) :
    let T := basisMatrix (fun b ↦ (b, enc (β b)))
    (∑' i, ENNReal.ofReal (conj
      (Ab * labelProjector β i * Aa - Qb * labelProjector β i * Qa) ρ).trace.re) =
      ENNReal.ofReal (conj
        ((Ab ⊗ₖ (1 : Matrix Z Z ℂ)) * T * Aa -
          (Qb ⊗ₖ (1 : Matrix Z Z ℂ)) * T * Qa) ρ).trace.re := by
  let w := fun z ↦ ENNReal.ofReal (conj
    (Ab * labelProjector (enc ∘ β) z * Aa -
      Qb * labelProjector (enc ∘ β) z * Qa) ρ).trace.re
  have hs : Function.support w ⊆ Set.range enc := by
    intro z hz
    by_contra hn
    have hp := labelProjector_encode_eq_zero β enc z hn
    exact hz (by simp [w, hp, conj_apply])
  have hh := henc.tsum_eq hs
  simp only [w, labelProjector_encode β enc henc] at hh
  exact hh.trans (checked_label_difference_weight (enc ∘ β) Aa Ab Qa Qb hρ)

variable [Fintype B] [Fintype Z] [DecidableEq B] [DecidableEq Z]

/-- A translation of the response controlled by the database basis label. -/
@[expose]
noncomputable def responseTranslation [AddGroup Z] (β : B → Z) : Matrix (B × Z) (B × Z) ℂ :=
  labelControlled (fun a : B × Z ↦ β a.1)
    (fun z ↦ (1 : Matrix B B ℂ) ⊗ₖ xorShift Z z)

omit [Fintype B] [Fintype Z] in
/-- A controlled translation is its deterministic basis permutation matrix. -/
theorem responseTranslation_eq_basisMatrix [AddGroup Z] (β : B → Z) :
    responseTranslation β = basisMatrix (fun a : B × Z ↦ (a.1, a.2 + β a.1)) := by
  ext ⟨b, z⟩ ⟨a, r⟩
  simp only [responseTranslation, labelControlled_apply, kroneckerMap_apply, one_apply,
    xorShift_apply, basisMatrix_apply, Prod.mk.injEq]
  by_cases h : b = a
  · subst a
    simp
  · simp [h]

/-- A controlled response translation is unitary. -/
theorem responseTranslation_unitary [AddGroup Z] (β : B → Z) :
    responseTranslation β ∈ unitaryGroup (B × Z) ℂ := by
  rw [responseTranslation_eq_basisMatrix, mem_unitaryGroup_iff']
  apply conjTranspose_basisMatrix_mul_self
  intro a b h
  have h₁ := congrArg Prod.fst h
  have h₂ := congrArg Prod.snd h
  dsimp only at h₁ h₂
  apply Prod.ext h₁
  rw [h₁] at h₂
  exact add_right_cancel h₂

/-- For an abelian response alphabet, addition of offsets factors controlled translations. -/
theorem responseTranslation_add [AddCommGroup Z] (β γ : B → Z) :
    responseTranslation (fun b ↦ β b + γ b) =
      responseTranslation β * responseTranslation γ := by
  simp only [responseTranslation_eq_basisMatrix, ← basisMatrix_comp]
  congr 1
  funext a
  dsimp only [Function.comp_apply]
  congr 1
  abel

/-- Adding a database-dependent response to an initially zero response register copies it. -/
theorem responseTranslation_zero [AddGroup Z] (β : B → Z) :
    labelControlled (fun a : B × Z ↦ β a.1)
        (fun z ↦ (1 : Matrix B B ℂ) ⊗ₖ xorShift Z z) *
      basisMatrix (fun b : B ↦ (b, (0 : Z))) = basisMatrix (fun b ↦ (b, β b)) := by
  ext ⟨b, z⟩ a
  simp only [Matrix.mul_apply, basisMatrix_apply, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true, labelControlled_apply,
    kroneckerMap_apply, one_apply, xorShift_apply, zero_add, Prod.mk.injEq]
  by_cases h : b = a
  · subst a
    simp
  · simp [h]

/-- Operators on the database commute with adjoining a zero response register. -/
theorem zero_response_intertwines [AddGroup Z] (M : Matrix B B ℂ) :
    (M ⊗ₖ (1 : Matrix Z Z ℂ)) * basisMatrix (fun b : B ↦ (b, (0 : Z))) =
      basisMatrix (fun b : B ↦ (b, (0 : Z))) * M := by
  ext ⟨b, z⟩ a
  simp only [Matrix.mul_apply, basisMatrix_apply, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true, kroneckerMap_apply, one_apply,
    Prod.mk.injEq]
  by_cases hz : z = 0
  · simp [hz]
  · simp [hz]

/-- The coherent copy comparison is the two-batch response-unitary difference applied to a
zero-initialized response. This is an operator identity before any measurement is discarded. -/
theorem checked_response_difference [AddGroup Z] (β : B → Z) (Aa Ab Qa Qb : Matrix B B ℂ) :
    let U := labelControlled (fun a : B × Z ↦ β a.1)
      (fun z ↦ (1 : Matrix B B ℂ) ⊗ₖ xorShift Z z)
    let J := basisMatrix (fun b : B ↦ (b, (0 : Z)))
    let T := basisMatrix (fun b ↦ (b, β b))
    ((Ab ⊗ₖ (1 : Matrix Z Z ℂ)) * U * (Aa ⊗ₖ 1) -
      (Qb ⊗ₖ (1 : Matrix Z Z ℂ)) * U * (Qa ⊗ₖ 1)) * J =
        (Ab ⊗ₖ (1 : Matrix Z Z ℂ)) * T * Aa -
          (Qb ⊗ₖ (1 : Matrix Z Z ℂ)) * T * Qa := by
  dsimp only
  rw [Matrix.sub_mul]
  have he (M N : Matrix B B ℂ) :
      ((M ⊗ₖ (1 : Matrix Z Z ℂ)) *
        labelControlled (fun a : B × Z ↦ β a.1)
          (fun z ↦ (1 : Matrix B B ℂ) ⊗ₖ xorShift Z z) * (N ⊗ₖ 1)) *
            basisMatrix (fun b : B ↦ (b, (0 : Z))) =
        (M ⊗ₖ (1 : Matrix Z Z ℂ)) * basisMatrix (fun b ↦ (b, β b)) * N := by
    rw [Matrix.mul_assoc, zero_response_intertwines]
    rw [← Matrix.mul_assoc, Matrix.mul_assoc (M ⊗ₖ (1 : Matrix Z Z ℂ)),
      responseTranslation_zero]
  rw [he, he]

/-- Decoded checker-difference weights are bounded by the coherent response-unitary
comparison on the original state with a fresh zero response register. -/
theorem encoded_checked_difference_le_response [AddGroup Z] {ι : Type*} [DecidableEq ι]
    (β : B → ι) (enc : ι → Z) (henc : Function.Injective enc)
    (Aa Ab Qa Qb : Matrix B B ℂ) {ρ : Matrix B B ℂ} (hρ : ρ.PosSemidef) :
    let U := labelControlled (fun a : B × Z ↦ enc (β a.1))
      (fun z ↦ (1 : Matrix B B ℂ) ⊗ₖ xorShift Z z)
    let J := basisMatrix (fun b : B ↦ (b, (0 : Z)))
    (∑' i, ENNReal.ofReal (conj
      (Ab * labelProjector β i * Aa - Qb * labelProjector β i * Qa) ρ).trace.re) ≤
      ENNReal.ofReal (conj
        ((Ab ⊗ₖ (1 : Matrix Z Z ℂ)) * U * (Aa ⊗ₖ 1) -
          (Qb ⊗ₖ (1 : Matrix Z Z ℂ)) * U * (Qa ⊗ₖ 1)) (conj J ρ)).trace.re := by
  have hh := encoded_checked_difference_le β enc henc Aa Ab Qa Qb hρ
  have he := checked_response_difference (enc ∘ β) Aa Ab Qa Qb
  dsimp only [Function.comp_apply] at he hh
  rw [← he, conj_mul, LinearMap.comp_apply] at hh
  exact hh

/-- The response dilation preserves the complete decoded difference weight on the original
input with a fresh zero response. This equality includes every unused codeword. -/
theorem encoded_checked_difference_eq_response [AddGroup Z] {ι : Type*} [DecidableEq ι]
    (β : B → ι) (enc : ι → Z) (henc : Function.Injective enc)
    (Aa Ab Qa Qb : Matrix B B ℂ) {ρ : Matrix B B ℂ} (hρ : ρ.PosSemidef) :
    let U := responseTranslation (enc ∘ β)
    let J := basisMatrix (fun b : B ↦ (b, (0 : Z)))
    (∑' i, ENNReal.ofReal (conj
      (Ab * labelProjector β i * Aa - Qb * labelProjector β i * Qa) ρ).trace.re) =
      ENNReal.ofReal (conj
        ((Ab ⊗ₖ (1 : Matrix Z Z ℂ)) * U * (Aa ⊗ₖ 1) -
          (Qb ⊗ₖ (1 : Matrix Z Z ℂ)) * U * (Qa ⊗ₖ 1)) (conj J ρ)).trace.re := by
  have hh := encoded_checked_difference_eq β enc henc Aa Ab Qa Qb hρ
  have he := checked_response_difference (enc ∘ β) Aa Ab Qa Qb
  dsimp only [Function.comp_apply] at he hh
  rw [← he, conj_mul, LinearMap.comp_apply] at hh
  exact hh

end Quantum.MatrixMap
