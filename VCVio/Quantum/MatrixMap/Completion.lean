/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
public import Mathlib.Analysis.Matrix.Order
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
public import VCVio.Quantum.MatrixMap.OpNorm

/-!
# Completing a matrix outside a projection without increasing its norm

Let `P` be an orthogonal projection on `𝕜^n` and `M` a square matrix. The products `P * M` and
`M * P` fix every block of `M` with respect to the decomposition `𝕜^n = range P ⊕ ker P` except
the block `(1 - P) * M * (1 - P)`. **Parrott's theorem** says that this last block can be chosen
so that the norm of the completed matrix is the larger of the two norms `‖P * M‖` and `‖M * P‖`,
which are obvious lower bounds:

  there is `T` with `P * T = P * M`, `T * P = M * P` and `‖T‖ ≤ h`
  as soon as `‖P * M‖ ≤ h` and `‖M * P‖ ≤ h` (`Matrix.exists_completion`).

The norm is the `L²` operator norm (open `Matrix.Norms.L2Operator`), and the order on Hermitian
matrices is the Loewner order (open `MatrixOrder`). The scalars are any `RCLike` field `𝕜`, so
real and complex matrices are both covered. The proof uses Mathlib's real continuous functional
calculus for Hermitian matrices over `𝕜` (for square roots) and the C⋆-identity of the operator
norm; the bridge `‖X‖ ≤ 1 ↔ Xᴴ X ≤ 1` between the norm and the Loewner order is proved from
quadratic forms (`Matrix.l2_opNorm_le_one_iff_conjTranspose_mul_self_le_one`), so no
`CStarAlgebra` (complex) structure is needed.

## Proof

Write `D = P M P`, `C = P M (1 - P)` and `B = (1 - P) M P`. Normalize to `‖P * M‖ < 1` and
`‖M * P‖ ≤ 1`. The defect operators `DL = (1 - D Dᴴ) ^ (1/2)` and `DR = (1 - Dᴴ D) ^ (1/2)` are
Hermitian, invertible, and intertwine `D`: `DL * D = D * DR` (`Matrix.exists_defect`, through the
Hermitian dilation of `D` and the continuous functional calculus). The row bound says
`C Cᴴ ≤ DL ^ 2` and the column bound says `Bᴴ B ≤ DR ^ 2`, so `K = DL⁻¹ C` and `L = B DR⁻¹` are
contractions. The completion is

  `T = L (DR P - Dᴴ K) + P (DL K + D P)`,

which the classical choice of the free block `-L Dᴴ K` produces; one checks
`Tᴴ T ≤ Kᴴ K + P ≤ 1`. The general case follows by scaling and, for the boundary value `h`
itself, by compactness of the set of completions of norm at most `h + 1`.

## Main results

* `Matrix.l2_opNorm_le_one_iff_conjTranspose_mul_self_le_one`: `‖X‖ ≤ 1 ↔ Xᴴ X ≤ 1`.
* `Matrix.exists_defect`: defect operators of a contraction.
* `Matrix.exists_completion_of_lt`, `Matrix.exists_completion`: Parrott's theorem.

## References

* S. Parrott, *On a quotient norm and the Sz.-Nagy–Foiaş lifting theorem*, J. Funct. Anal. 30
  (1978).
* C. Davis, W. Kahan and H. Weinberger, *Norm-preserving dilations and their applications to
  optimal error bounds*, SIAM J. Numer. Anal. 19 (1982).
-/

public section

open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder

namespace Matrix

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n]

/-! ## The operator norm and the Loewner order -/

omit [DecidableEq n] in
/-- `star w ⬝ᵥ w` is the squared Euclidean norm of `w`. -/
theorem star_dotProduct_self_eq_sum_norm_sq (w : n → 𝕜) :
    star w ⬝ᵥ w = ((∑ i, ‖w i‖ ^ 2 : ℝ) : 𝕜) := by
  push_cast
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [Pi.star_apply, RCLike.star_def, RCLike.conj_mul]

omit [DecidableEq n] in
/-- The quadratic form of `Xᴴ X` at `v` is the squared norm of `X v`. -/
theorem star_dotProduct_conjTranspose_mul_self_mulVec {m : Type*} [Fintype m]
    (X : Matrix m n 𝕜) (v : n → 𝕜) :
    star v ⬝ᵥ ((Xᴴ * X) *ᵥ v) = ((∑ i, ‖(X *ᵥ v) i‖ ^ 2 : ℝ) : 𝕜) := by
  rw [← mulVec_mulVec, dotProduct_mulVec, ← star_mulVec, star_dotProduct_self_eq_sum_norm_sq]

/-- A square matrix is a contraction if and only if `Xᴴ X ≤ 1`. -/
theorem l2_opNorm_le_one_iff_conjTranspose_mul_self_le_one (X : Matrix n n 𝕜) :
    ‖X‖ ≤ 1 ↔ Xᴴ * X ≤ 1 := by
  have hq : ∀ v : n → 𝕜, star v ⬝ᵥ ((1 - Xᴴ * X) *ᵥ v) =
      ((∑ j, ‖v j‖ ^ 2 - ∑ i, ‖(X *ᵥ v) i‖ ^ 2 : ℝ) : 𝕜) := fun v ↦ by
    rw [sub_mulVec, one_mulVec, dotProduct_sub, star_dotProduct_conjTranspose_mul_self_mulVec,
      star_dotProduct_self_eq_sum_norm_sq, RCLike.ofReal_sub]
  have hH : (1 - Xᴴ * X).IsHermitian := by
    rw [IsHermitian, conjTranspose_sub, conjTranspose_one, conjTranspose_mul,
      conjTranspose_conjTranspose]
  rw [le_iff, posSemidef_iff_dotProduct_mulVec]
  simp only [hH, true_and, hq, RCLike.ofReal_nonneg, sub_nonneg]
  constructor
  · intro h v
    simpa using (sum_norm_mulVec_sq_le X v).trans
      (mul_le_of_le_one_left (Finset.sum_nonneg fun _ _ ↦ sq_nonneg _)
        (pow_le_one₀ (norm_nonneg _) h))
  · intro h
    exact l2_opNorm_le_of_sum_norm_mulVec_sq_le zero_le_one fun v ↦ by simpa using h v

/-- A square matrix is a contraction if and only if `X Xᴴ ≤ 1`. -/
theorem l2_opNorm_le_one_iff_mul_conjTranspose_le_one (X : Matrix n n 𝕜) :
    ‖X‖ ≤ 1 ↔ X * Xᴴ ≤ 1 := by
  rw [← l2_opNorm_conjTranspose, l2_opNorm_le_one_iff_conjTranspose_mul_self_le_one,
    conjTranspose_conjTranspose]

/-! ## Defect operators -/


/-- For a contraction `D`, the matrix `1 - D Dᴴ` is positive semidefinite. -/
theorem one_sub_mul_conjTranspose_nonneg {D : Matrix n n 𝕜} (hD : ‖D‖ ≤ 1) :
    0 ≤ 1 - D * Dᴴ := by
  rwa [sub_nonneg, ← l2_opNorm_le_one_iff_mul_conjTranspose_le_one]

/-- For a contraction `D`, the matrix `1 - Dᴴ D` is positive semidefinite. -/
theorem one_sub_conjTranspose_mul_nonneg {D : Matrix n n 𝕜} (hD : ‖D‖ ≤ 1) :
    0 ≤ 1 - Dᴴ * D := by
  have h := one_sub_mul_conjTranspose_nonneg (D := Dᴴ) (by rwa [l2_opNorm_conjTranspose])
  rwa [conjTranspose_conjTranspose] at h

/-- **Defect operators.** A contraction `D` has Hermitian square roots `DL` of `1 - D Dᴴ` and `DR`
of `1 - Dᴴ D` that intertwine it: `DL * D = D * DR`. They are the blocks of the square root of
`1 - N ^ 2`, where `N` is the Hermitian dilation of `D`, which commutes with `N`. -/
theorem exists_defect (D : Matrix n n 𝕜) (hD : ‖D‖ ≤ 1) :
    ∃ DL DR : Matrix n n 𝕜, DLᴴ = DL ∧ DRᴴ = DR ∧ DL * DL = 1 - D * Dᴴ ∧
      DR * DR = 1 - Dᴴ * D ∧ DL * D = D * DR := by
  set N : Matrix (n ⊕ n) (n ⊕ n) 𝕜 := fromBlocks 0 D Dᴴ 0 with hN
  set G : Matrix (n ⊕ n) (n ⊕ n) 𝕜 := fromBlocks (1 - D * Dᴴ) 0 0 (1 - Dᴴ * D) with hG
  set E : Matrix (n ⊕ n) (n ⊕ n) 𝕜 := fromBlocks 1 0 0 0 with hE
  have hGN : G = 1 - N * N := by
    rw [hG, hN, fromBlocks_multiply, ← fromBlocks_one, sub_eq_add_neg, sub_eq_add_neg,
      sub_eq_add_neg, fromBlocks_neg, fromBlocks_add]
    simp
  have hG0 : 0 ≤ G := by
    set a := CFC.sqrt (1 - D * Dᴴ)
    set b := CFC.sqrt (1 - Dᴴ * D)
    have ha : a * a = 1 - D * Dᴴ := CFC.sqrt_mul_sqrt_self _ (one_sub_mul_conjTranspose_nonneg hD)
    have hb : b * b = 1 - Dᴴ * D := CFC.sqrt_mul_sqrt_self _ (one_sub_conjTranspose_mul_nonneg hD)
    have ha' : aᴴ = a := (CFC.sqrt_nonneg _).isSelfAdjoint
    have hb' : bᴴ = b := (CFC.sqrt_nonneg _).isSelfAdjoint
    have : G = star (fromBlocks a 0 0 b) * fromBlocks a 0 0 b := by
      rw [star_eq_conjTranspose, fromBlocks_conjTranspose, fromBlocks_multiply, ha', hb', ha, hb]
      simp [hG]
    rw [this]
    exact star_mul_self_nonneg _
  set S := CFC.sqrt G with hS
  have hSS : S * S = G := CFC.sqrt_mul_sqrt_self G hG0
  have hSh : Sᴴ = S := (CFC.sqrt_nonneg G).isSelfAdjoint
  have hcomm : ∀ X, Commute G X → Commute S X := fun X h ↦ by
    rw [hS, CFC.sqrt_eq_cfc]
    exact h.cfc_nnreal _
  have hSN : S * N = N * S := hcomm N (by
    rw [hGN]; exact (Commute.one_left N).sub_left ((Commute.refl N).mul_left (Commute.refl N)))
  have hSE : S * E = E * S := hcomm E (by
    change G * E = E * G
    rw [hG, hE, fromBlocks_multiply, fromBlocks_multiply]
    simp)
  clear_value S
  obtain ⟨S₁, S₂, S₃, S₄, rfl⟩ : ∃ S₁ S₂ S₃ S₄, S = fromBlocks S₁ S₂ S₃ S₄ :=
    ⟨_, _, _, _, (fromBlocks_toBlocks S).symm⟩
  rw [hE, fromBlocks_multiply, fromBlocks_multiply] at hSE
  simp only [Matrix.mul_one, Matrix.mul_zero, add_zero, Matrix.one_mul, Matrix.zero_mul,
    fromBlocks_inj] at hSE
  obtain ⟨-, h2, h3, -⟩ := hSE
  subst h2 h3
  rw [fromBlocks_multiply, hG] at hSS
  rw [fromBlocks_conjTranspose] at hSh
  rw [hN, fromBlocks_multiply, fromBlocks_multiply] at hSN
  simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, fromBlocks_inj] at hSS hSh hSN
  exact ⟨S₁, S₄, hSh.1, hSh.2.2.2, hSS.1, hSS.2.2.2, hSN.2.1⟩

private theorem isUnit_det_of_mul_self_eq {S G : Matrix n n 𝕜} (h : S * S = G) (hG : IsUnit G) :
    IsUnit S.det := by
  rw [isUnit_iff_isUnit_det, ← h, det_mul] at hG
  exact isUnit_of_mul_isUnit_left hG

/-- The algebra behind Parrott's theorem: given the defect operators of `D = P M P` and
contractions `K`, `L` that solve `DL K = P M (1 - P)` and `L DR = (1 - P) M P`, the explicit
completion has the prescribed row and column and is a contraction. -/
private theorem completion_aux {P M DL DR K L : Matrix n n 𝕜} (hPh : Pᴴ = P) (hPP : P * P = P)
    (hDLh : DLᴴ = DL) (hDRh : DRᴴ = DR)
    (hDL : DL * DL = 1 - (P * M * P) * (P * M * P)ᴴ)
    (hDR : DR * DR = 1 - (P * M * P)ᴴ * (P * M * P))
    (hint : DL * (P * M * P) = (P * M * P) * DR) (hKP : K * P = 0) (hPL : P * L = 0)
    (hDLK : DL * K = P * M * (1 - P)) (hLDR : L * DR = (1 - P) * M * P)
    (hK : Kᴴ * K ≤ 1) (hL : Lᴴ * L ≤ 1) :
    P * (L * (DR * P - (P * M * P)ᴴ * K) + P * (DL * K + (P * M * P) * P)) = P * M ∧
    (L * (DR * P - (P * M * P)ᴴ * K) + P * (DL * K + (P * M * P) * P)) * P = M * P ∧
    (L * (DR * P - (P * M * P)ᴴ * K) + P * (DL * K + (P * M * P) * P))ᴴ *
      (L * (DR * P - (P * M * P)ᴴ * K) + P * (DL * K + (P * M * P) * P)) ≤ 1 := by
  obtain ⟨D, hD⟩ : ∃ D, D = P * M * P := ⟨_, rfl⟩
  obtain ⟨X₁, hX₁⟩ : ∃ X, X = DR * P - Dᴴ * K := ⟨_, rfl⟩
  obtain ⟨X₂, hX₂⟩ : ∃ X, X = DL * K + D * P := ⟨_, rfl⟩
  rw [← hD] at hDL hDR hint ⊢
  rw [← hX₁, ← hX₂]
  refine ⟨?_, ?_, ?_⟩
  · have e : P * (L * X₁ + P * X₂) = (P * L) * X₁ + (P * P - P) * X₂
        + P * (DL * K - P * M * (1 - P)) + (P * P - P) * M - (P * P - P) * M * P
        + (P * P - P) * M * P * P + P * M * (P * P - P)
        + P * M := by
      rw [hX₂, hD]; noncomm_ring
    rw [e, hPL, hDLK, hPP]; simp
  · have e : (L * X₁ + P * X₂) * P = L * DR * (P * P - P) - L * Dᴴ * (K * P) + P * DL * (K * P)
        + P * D * (P * P - P) + (L * DR - (1 - P) * M * P) * P + (P * P - P) * M * P * P
        + M * (P * P - P) + M * P := by
      rw [hX₁, hX₂, hD]; noncomm_ring
    rw [e, hLDR, hKP, hPP]; simp
  · have hLP : Lᴴ * P = 0 := by
      rw [← hPh, ← conjTranspose_mul, hPL, conjTranspose_zero]
    have hint' : Dᴴ * DL = DR * Dᴴ := by
      rw [← hDLh, ← hDRh, ← conjTranspose_mul, ← conjTranspose_mul, hint]
    have hQ : (1 - P)ᴴ * (1 - P) = 1 - P := by
      have e : (1 - P)ᴴ * (1 - P) = (1 - P) + (P * P - P) := by
        rw [conjTranspose_sub, conjTranspose_one, hPh]; noncomm_ring
      rw [e, hPP, sub_self, add_zero]
    have hP1 : P ≤ 1 := by
      rw [← sub_nonneg, ← hQ]
      simpa only [star_eq_conjTranspose] using star_mul_self_nonneg (1 - P)
    -- `Kᴴ K ≤ 1 - P`, since `K` vanishes on the range of `P`
    have hKQ : K * (1 - P) = K := by rw [Matrix.mul_sub, hKP, Matrix.mul_one, sub_zero]
    have hKK : Kᴴ * K ≤ 1 - P := by
      have h := star_left_conjugate_le_conjugate hK (1 - P)
      simp only [star_eq_conjTranspose, Matrix.mul_one] at h
      rwa [hQ, Matrix.mul_assoc, Matrix.mul_assoc, hKQ, ← Matrix.mul_assoc, ← conjTranspose_mul,
        hKQ] at h
    -- the two blocks of `Tᴴ T`
    have e₁ : (L * X₁ + P * X₂)ᴴ * (L * X₁ + P * X₂) = X₁ᴴ * (Lᴴ * L) * X₁ + X₂ᴴ * P * X₂
        + X₁ᴴ * (Lᴴ * P) * X₂ + X₂ᴴ * (P * L) * X₁ + X₂ᴴ * (P * P - P) * X₂ := by
      rw [conjTranspose_add, conjTranspose_mul, conjTranspose_mul, hPh]; noncomm_ring
    have e₂ : X₁ᴴ * X₁ + X₂ᴴ * X₂ = Kᴴ * K + P + Kᴴ * (DL * DL - (1 - D * Dᴴ)) * K
        + P * (DR * DR - (1 - Dᴴ * D)) * P + Kᴴ * (DL * D - D * DR) * P
        + P * (Dᴴ * DL - DR * Dᴴ) * K + (P * P - P) := by
      rw [hX₁, hX₂, conjTranspose_sub, conjTranspose_add, conjTranspose_mul, conjTranspose_mul,
        conjTranspose_mul, conjTranspose_mul, hPh, hDLh, hDRh, conjTranspose_conjTranspose]
      noncomm_ring
    rw [hDL, hDR, hint, hint', hPP, sub_self, sub_self, sub_self, sub_self, sub_self] at e₂
    simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero] at e₂
    rw [e₁, hLP, hPL, hPP, sub_self]
    simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero]
    have h₁ := star_left_conjugate_le_conjugate hL X₁
    have h₂ := star_left_conjugate_le_conjugate hP1 X₂
    simp only [star_eq_conjTranspose, Matrix.mul_one] at h₁ h₂
    calc X₁ᴴ * (Lᴴ * L) * X₁ + X₂ᴴ * P * X₂ ≤ X₁ᴴ * X₁ + X₂ᴴ * X₂ := add_le_add h₁ h₂
      _ = Kᴴ * K + P := e₂
      _ ≤ (1 - P) + P := add_le_add_left hKK P
      _ = 1 := sub_add_cancel 1 P

/-- Parrott's theorem with a strict row bound, normalized to `1`. -/
private theorem exists_completion_of_norm_lt_one {P M : Matrix n n 𝕜} (hP : IsStarProjection P)
    (hrow : ‖P * M‖ < 1) (hcol : ‖M * P‖ ≤ 1) :
    ∃ T, P * T = P * M ∧ T * P = M * P ∧ ‖T‖ ≤ 1 := by
  have hPh : Pᴴ = P := hP.isSelfAdjoint
  have hPP : P * P = P := hP.isIdempotentElem
  have hPn : ‖P‖ ≤ 1 := by
    have h := l2_opNorm_conjTranspose_mul_self P
    rw [hPh, hPP] at h
    nlinarith [norm_nonneg P]
  have hD : ‖P * M * P‖ < 1 := calc
    ‖P * M * P‖ ≤ ‖P * M‖ * ‖P‖ := l2_opNorm_mul _ _
    _ ≤ ‖P * M‖ * 1 := by gcongr
    _ < 1 := by simpa using hrow
  have hD2 : ‖P * M * P‖ * ‖P * M * P‖ < 1 := by nlinarith [norm_nonneg (P * M * P)]
  obtain ⟨DL, DR, hDLh, hDRh, hDL, hDR, hint⟩ := exists_defect (P * M * P) hD.le
  have hDLu : IsUnit DL.det := isUnit_det_of_mul_self_eq hDL <| isUnit_one_sub_of_norm_lt_one <|
    (l2_opNorm_mul _ _).trans_lt (by rwa [l2_opNorm_conjTranspose])
  have hDRu : IsUnit DR.det := isUnit_det_of_mul_self_eq hDR <| isUnit_one_sub_of_norm_lt_one <|
    (l2_opNorm_mul _ _).trans_lt (by rwa [l2_opNorm_conjTranspose])
  have hQP : (1 - P) * P = 0 := by rw [Matrix.sub_mul, Matrix.one_mul, hPP, sub_self]
  have hPQ : P * (1 - P) = 0 := by rw [Matrix.mul_sub, Matrix.mul_one, hPP, sub_self]
  -- the row and the column bounds, as operator inequalities
  have hCC : (P * M * (1 - P)) * (P * M * (1 - P))ᴴ ≤ 1 - (P * M * P) * (P * M * P)ᴴ := by
    have e : (P * M * (1 - P)) * (P * M * (1 - P))ᴴ + (P * M * P) * (P * M * P)ᴴ =
        (P * M) * (P * M)ᴴ + (P * M * (P * P - P) * Mᴴ * P + P * M * (P * P - P) * Mᴴ * P) := by
      simp only [conjTranspose_mul, conjTranspose_sub, conjTranspose_one, hPh]; noncomm_ring
    rw [hPP, sub_self] at e
    simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero] at e
    rw [le_sub_iff_add_le, e, ← l2_opNorm_le_one_iff_mul_conjTranspose_le_one]
    exact hrow.le
  have hBB : ((1 - P) * M * P)ᴴ * ((1 - P) * M * P) ≤ 1 - (P * M * P)ᴴ * (P * M * P) := by
    have e : ((1 - P) * M * P)ᴴ * ((1 - P) * M * P) + (P * M * P)ᴴ * (P * M * P) =
        (M * P)ᴴ * (M * P) + (P * Mᴴ * (P * P - P) * M * P + P * Mᴴ * (P * P - P) * M * P) := by
      simp only [conjTranspose_mul, conjTranspose_sub, conjTranspose_one, hPh]; noncomm_ring
    rw [hPP, sub_self] at e
    simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero] at e
    rw [le_sub_iff_add_le, e, ← l2_opNorm_le_one_iff_conjTranspose_mul_self_le_one]
    exact hcol
  -- the contractions `K = DL⁻¹ C` and `L = B DR⁻¹`
  have hK : (DL⁻¹ * (P * M * (1 - P)))ᴴ * (DL⁻¹ * (P * M * (1 - P))) ≤ 1 := by
    rw [← l2_opNorm_le_one_iff_conjTranspose_mul_self_le_one,
      l2_opNorm_le_one_iff_mul_conjTranspose_le_one]
    have h := star_right_conjugate_le_conjugate hCC DL⁻¹
    have e1 : DL⁻¹ * (DL * DL) * DL⁻¹ = 1 := by
      rw [← Matrix.mul_assoc, nonsing_inv_mul _ hDLu, Matrix.one_mul, mul_nonsing_inv _ hDLu]
    rw [← hDL, star_eq_conjTranspose, conjTranspose_nonsing_inv, hDLh, e1] at h
    rw [conjTranspose_mul, conjTranspose_nonsing_inv, hDLh]
    simpa only [Matrix.mul_assoc] using h
  have hL : (((1 - P) * M * P) * DR⁻¹)ᴴ * (((1 - P) * M * P) * DR⁻¹) ≤ 1 := by
    have h := star_left_conjugate_le_conjugate hBB DR⁻¹
    have e1 : DR⁻¹ * (DR * DR) * DR⁻¹ = 1 := by
      rw [← Matrix.mul_assoc, nonsing_inv_mul _ hDRu, Matrix.one_mul, mul_nonsing_inv _ hDRu]
    rw [← hDR, star_eq_conjTranspose, conjTranspose_nonsing_inv, hDRh, e1] at h
    rw [conjTranspose_mul, conjTranspose_nonsing_inv, hDRh]
    simpa only [Matrix.mul_assoc] using h
  obtain ⟨h₁, h₂, h₃⟩ := completion_aux (M := M) (K := DL⁻¹ * (P * M * (1 - P)))
    (L := ((1 - P) * M * P) * DR⁻¹) hPh hPP hDLh hDRh hDL hDR hint
    (by rw [Matrix.mul_assoc, Matrix.mul_assoc, hQP]; simp)
    (by rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hPQ]; simp)
    (by rw [← Matrix.mul_assoc, mul_nonsing_inv _ hDLu, Matrix.one_mul])
    (by rw [Matrix.mul_assoc, nonsing_inv_mul _ hDRu, Matrix.mul_one]) hK hL
  exact ⟨_, h₁, h₂, (l2_opNorm_le_one_iff_conjTranspose_mul_self_le_one _).mpr h₃⟩

/-- Parrott's theorem up to an arbitrarily small loss: if `‖P M‖ ≤ h`, `‖M P‖ ≤ h` and `h < c`,
then `M` has a completion of norm at most `c` that agrees with it on the range of `P`, on both
sides. -/
theorem exists_completion_of_lt {P M : Matrix n n 𝕜} (hP : IsStarProjection P) {h c : ℝ}
    (hrow : ‖P * M‖ ≤ h) (hcol : ‖M * P‖ ≤ h) (hc : h < c) :
    ∃ T, P * T = P * M ∧ T * P = M * P ∧ ‖T‖ ≤ c := by
  have hc0 : 0 < c := (norm_nonneg _).trans_lt (hrow.trans_lt hc)
  have hk : ‖((c : ℝ) : 𝕜)‖ = c := by rw [RCLike.norm_ofReal, abs_of_pos hc0]
  have hk0 : ((c : ℝ) : 𝕜) ≠ 0 := RCLike.ofReal_ne_zero.mpr hc0.ne'
  obtain ⟨T, h₁, h₂, h₃⟩ := exists_completion_of_norm_lt_one hP (M := ((c : ℝ) : 𝕜)⁻¹ • M)
    (by rw [Matrix.mul_smul, norm_smul, norm_inv, hk, inv_mul_lt_one₀ hc0]
        exact hrow.trans_lt hc)
    (by rw [Matrix.smul_mul, norm_smul, norm_inv, hk, inv_mul_le_one₀ hc0]
        exact hcol.trans hc.le)
  refine ⟨((c : ℝ) : 𝕜) • T, ?_, ?_, ?_⟩
  · rw [Matrix.mul_smul, h₁, Matrix.mul_smul, smul_inv_smul₀ hk0]
  · rw [Matrix.smul_mul, h₂, Matrix.smul_mul, smul_inv_smul₀ hk0]
  · rw [norm_smul, hk]
    nlinarith

/-- **Parrott's theorem.** Let `P` be an orthogonal projection. If `‖P M‖ ≤ h` and `‖M P‖ ≤ h`,
there is a matrix `T` with `P T = P M`, `T P = M P` and `‖T‖ ≤ h`: the block of `M` outside the
range of `P` on both sides can be replaced so that the norm drops to `max ‖P M‖ ‖M P‖`. -/
theorem exists_completion {P M : Matrix n n 𝕜} (hP : IsStarProjection P) {h : ℝ}
    (hrow : ‖P * M‖ ≤ h) (hcol : ‖M * P‖ ≤ h) :
    ∃ T, P * T = P * M ∧ T * P = M * P ∧ ‖T‖ ≤ h := by
  have : ProperSpace (Matrix n n 𝕜) := FiniteDimensional.proper 𝕜 _
  set S : Set (Matrix n n 𝕜) :=
    {T | P * T = P * M ∧ T * P = M * P} ∩ Metric.closedBall 0 (h + 1) with hS
  have hSc : IsCompact S := by
    refine Metric.isCompact_of_isClosed_isBounded (IsClosed.inter ?_ Metric.isClosed_closedBall)
      (Metric.isBounded_closedBall.subset Set.inter_subset_right)
    exact (isClosed_eq (continuous_const.mul continuous_id) continuous_const).inter
      (isClosed_eq (continuous_id.mul continuous_const) continuous_const)
  have hmem : ∀ c, h < c → c ≤ h + 1 → ∃ T ∈ S, ‖T‖ ≤ c := fun c hc hc' ↦ by
    obtain ⟨T, h₁, h₂, h₃⟩ := exists_completion_of_lt hP hrow hcol hc
    exact ⟨T, ⟨⟨h₁, h₂⟩, by rw [mem_closedBall_zero_iff]; linarith⟩, h₃⟩
  obtain ⟨T₁, hT₁, -⟩ := hmem (h + 1) (by linarith) le_rfl
  obtain ⟨T, hT, hmin⟩ := hSc.exists_isMinOn ⟨T₁, hT₁⟩ continuous_norm.continuousOn
  refine ⟨T, hT.1.1, hT.1.2, le_of_forall_gt_imp_ge_of_dense fun c hc ↦ ?_⟩
  rcases le_or_gt c (h + 1) with hc' | hc'
  · obtain ⟨T', hT', hc''⟩ := hmem c hc hc'
    exact (hmin hT').trans hc''
  · exact (mem_closedBall_zero_iff.mp hT.2).trans hc'.le

end Matrix
