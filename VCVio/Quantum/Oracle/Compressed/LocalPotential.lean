/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import VCVio.Quantum.Oracle.Compressed.CommutatorBound

/-!
# Local potential inequalities for the compressed oracle

This file proves local positive-operator inequalities for binary events of one compressed
cell over a finite abelian answer group. The two-coefficient inequality is equation (77) of
the accompanying bounds note (NOTE), refining ePrint 2025/2166 §9.3's collision-event
argument (Lemma 9.6, p. 61; event bound, pp. 64–65).
The three-coefficient source estimate retains the phase component as in NOTE (100) and (107).
The potential-drop identity underlies the population transition inequality (78).

`LeakBound` and `PhaseLeakBound` separate numerical calibration from the operator proof.
`posSemidef_smul_cellDiag_sub_flip` proves the occupancy-sensitive bound, and
`sum_norm_flipCommutator_sq_le` gives its three-coefficient source form. The latter retains
the phase component after restricting to the unflipped source; this restriction matters when
using the estimate in a potential certificate. `posSemidef_cellDrop_sub_flip` removes that
restriction with the additive coefficient `lam * d * |fl| / N` from equation (107).
`posSemidef_smul_cellDiag_sub_binary` also covers binary events true on the empty cell.

The phase-cell results are stated for the scalar character blocks of the standard compressed
oracle. They do not identify a response-mixing empty-sector extension with those blocks.
The population inequality `posSemidef_scalar_sub_unitary_twoLevel` applies to every unitary,
including such extensions. Quantitative events of arbitrary programs are handled by
`VCVio.Quantum.Comp.Potential` once its drop and leak hypotheses have been established.
-/

public section

open Matrix
open scoped Kronecker ComplexOrder ComplexConjugate InnerProductSpace

namespace Quantum

/-! ## Positive semidefinite matrices from quadratic forms -/

section psd

variable {n : Type*} [Fintype n]

/-- A Hermitian matrix whose quadratic form has nonnegative real part is positive semidefinite. -/
theorem posSemidef_of_re_dotProduct_mulVec_nonneg {M : Matrix n n ℂ} (hM : M.IsHermitian)
    (h : ∀ x : n → ℂ, 0 ≤ (star x ⬝ᵥ (M *ᵥ x)).re) : M.PosSemidef := by
  refine PosSemidef.of_dotProduct_mulVec_nonneg hM fun x ↦ ?_
  have him : (star x ⬝ᵥ (M *ᵥ x)).im = 0 :=
    Complex.conj_eq_iff_im.mp (hM.star_dotProduct_mulVec_comm x x)
  exact Complex.nonneg_iff.mpr ⟨h x, him.symm⟩

/-- The real part of `star v ⬝ᵥ v` is the squared norm of `v`. -/
theorem re_star_dotProduct_self (v : n → ℂ) : (star v ⬝ᵥ v).re = ∑ a, ‖v a‖ ^ 2 := by
  simp only [dotProduct, Pi.star_apply, Complex.re_sum]
  refine Finset.sum_congr rfl fun a _ ↦ ?_
  rw [RCLike.star_def, Complex.conj_mul', ← Complex.ofReal_pow, Complex.ofReal_re]

/-- The quadratic form of `Kᴴ K` is the squared norm of `K x`. -/
theorem star_dotProduct_conjTranspose_mul_self_mulVec {m : Type*} [Fintype m]
    (K : Matrix m n ℂ) (x : n → ℂ) :
    star x ⬝ᵥ ((Kᴴ * K) *ᵥ x) = star (K *ᵥ x) ⬝ᵥ (K *ᵥ x) := by
  rw [← mulVec_mulVec, dotProduct_mulVec, star_mulVec]

/-- A block-diagonal matrix of positive semidefinite blocks is positive semidefinite. -/
theorem posSemidef_blockDiagonal {m o : Type*} [Finite m] [Finite o] [DecidableEq o]
    {M : o → Matrix m m ℂ} (hM : ∀ k, (M k).PosSemidef) : (blockDiagonal M).PosSemidef := by
  have := Fintype.ofFinite m
  have := Fintype.ofFinite o
  refine PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun x ↦ ?_
  · rw [IsHermitian, blockDiagonal_conjTranspose]
    exact congrArg blockDiagonal (funext fun k ↦ (hM k).1)
  · have h : star x ⬝ᵥ (blockDiagonal M *ᵥ x) =
        ∑ k, star (fun i ↦ x (i, k)) ⬝ᵥ (M k *ᵥ fun i ↦ x (i, k)) := by
      simp only [dotProduct, mulVec, Fintype.sum_prod_type, blockDiagonal_apply, Pi.star_apply,
        ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
      rw [Finset.sum_comm]
    rw [h]
    exact Finset.sum_nonneg fun k _ ↦ (hM k).dotProduct_mulVec_nonneg _

/-- A block-diagonal matrix of positive semidefinite blocks, over a sigma type, is positive
semidefinite. -/
theorem posSemidef_blockDiagonal' {o : Type*} [Finite o] [DecidableEq o] {m : o → Type*}
    [∀ k, Finite (m k)] {M : ∀ k, Matrix (m k) (m k) ℂ} (hM : ∀ k, (M k).PosSemidef) :
    (blockDiagonal' M).PosSemidef := by
  have := Fintype.ofFinite o
  have := fun k ↦ Fintype.ofFinite (m k)
  refine PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun x ↦ ?_
  · rw [IsHermitian, blockDiagonal'_conjTranspose]
    exact congrArg blockDiagonal' (funext fun k ↦ (hM k).1)
  · have h : star x ⬝ᵥ (blockDiagonal' M *ᵥ x) =
        ∑ k, star (fun i ↦ x ⟨k, i⟩) ⬝ᵥ (M k *ᵥ fun i ↦ x ⟨k, i⟩) := by
      simp only [dotProduct, mulVec, Fintype.sum_sigma, blockDiagonal'_apply, Pi.star_apply]
      refine Finset.sum_congr rfl fun k _ ↦ Finset.sum_congr rfl fun i _ ↦ ?_
      congr 1
      rw [Finset.sum_eq_single k]
      · exact Finset.sum_congr rfl fun j _ ↦ by simp
      · intro k' _ hk'
        exact Finset.sum_eq_zero fun j _ ↦ by simp [Ne.symm hk']
      · simp
    rw [h]
    exact Finset.sum_nonneg fun k _ ↦ (hM k).dotProduct_mulVec_nonneg _

/-- **Bessel's inequality for two orthonormal vectors**, in coordinates. -/
theorem norm_dotProduct_star_sq_add_le {e₁ e₂ : n → ℂ} (h₁ : e₁ ⬝ᵥ star e₁ = 1)
    (h₂ : e₂ ⬝ᵥ star e₂ = 1) (h₁₂ : e₂ ⬝ᵥ star e₁ = 0) (φ : n → ℂ) :
    ‖φ ⬝ᵥ star e₁‖ ^ 2 + ‖φ ⬝ᵥ star e₂‖ ^ 2 ≤ ∑ i, ‖φ i‖ ^ 2 := by
  have h₂₁ : e₁ ⬝ᵥ star e₂ = 0 := by rw [dotProduct_star, h₁₂, star_zero]
  let v : Fin 2 → EuclideanSpace ℂ n := ![WithLp.toLp 2 e₁, WithLp.toLp 2 e₂]
  have hv : Orthonormal ℂ v := by
    rw [orthonormal_iff_ite]
    simp only [Fin.forall_fin_two, v, Matrix.cons_val_zero, Matrix.cons_val_one,
      EuclideanSpace.inner_toLp_toLp, h₁, h₂, h₁₂, h₂₁]
    simp
  have := hv.sum_inner_products_le (x := WithLp.toLp 2 φ) (s := Finset.univ)
  simpa [Fin.sum_univ_two, v, EuclideanSpace.inner_toLp_toLp, EuclideanSpace.norm_sq_eq]
    using this

/-- Weighted Cauchy–Schwarz for the three terms of the leak of a flipped cell. -/
theorem sq_add_two_mul_add_le {p q : ℝ} (hp : 0 < p) (hq : 0 < q) (x y z : ℝ) :
    (x + 2 * y + z) ^ 2 ≤ (p⁻¹ + 5 * q⁻¹) * (p * x ^ 2 + q * (y ^ 2 + z ^ 2)) := by
  have key : (p⁻¹ + 5 * q⁻¹) * (p * x ^ 2 + q * (y ^ 2 + z ^ 2)) - (x + 2 * y + z) ^ 2 =
      q / p * (y - 2 * p / q * x) ^ 2 + q / p * (z - p / q * x) ^ 2 + (y - 2 * z) ^ 2 := by
    field_simp
    ring
  have : 0 ≤ q / p * (y - 2 * p / q * x) ^ 2 + q / p * (z - p / q * x) ^ 2 + (y - 2 * z) ^ 2 := by
    positivity
  linarith

/-- Weighted Cauchy–Schwarz for three real source components with coefficients `1, 2, 1`. -/
theorem sq_add_two_mul_add_le_three {p q r : ℝ} (hp : 0 < p) (hq : 0 < q)
    (hr : 0 < r) (x y z : ℝ) :
    (x + 2 * y + z) ^ 2 ≤
      (p⁻¹ + 4 * q⁻¹ + r⁻¹) * (p * x ^ 2 + q * y ^ 2 + r * z ^ 2) := by
  have key : (p⁻¹ + 4 * q⁻¹ + r⁻¹) * (p * x ^ 2 + q * y ^ 2 + r * z ^ 2) -
      (x + 2 * y + z) ^ 2 =
      q / p * (y - 2 * p / q * x) ^ 2 + r / p * (z - p / r * x) ^ 2 +
        r / q * (2 * z - q / r * y) ^ 2 := by
    field_simp
    ring
  have : 0 ≤ q / p * (y - 2 * p / q * x) ^ 2 + r / p * (z - p / r * x) ^ 2 +
      r / q * (2 * z - q / r * y) ^ 2 := by positivity
  linarith

/-- A unitary conjugate of a two-level potential is bounded by its larger scalar value.
This is the local population transition inequality (78), with no restriction on the unitary. -/
theorem posSemidef_scalar_sub_unitary_twoLevel [DecidableEq n]
    {E U : Matrix n n ℂ} (hE : E.PosSemidef) (hU : Uᴴ * U = 1)
    {u v : ℝ} (huv : u ≤ v) :
    (v • (1 : Matrix n n ℂ) - Uᴴ * (v • 1 - (v - u) • E) * U).PosSemidef := by
  rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.mul_one, hU, Matrix.mul_smul, Matrix.smul_mul, sub_sub_cancel]
  exact (hE.conjTranspose_mul_mul_same U).smul (sub_nonneg.mpr huv)

/-- A unitary preserving a potential has zero potential drop, as for extraction and recording
ports when the potential counts only the oracle databases. -/
theorem conjTranspose_mul_mul_eq_of_commute [DecidableEq n]
    {F U : Matrix n n ℂ} (hU : Uᴴ * U = 1) (hF : F * U = U * F) :
    Uᴴ * F * U = F := by
  rw [Matrix.mul_assoc, hF, ← Matrix.mul_assoc, hU, Matrix.one_mul]

end psd

/-! ## One cell of the phase oracle -/

section cell

variable {Y : Type*} [DecidableEq Y]

/-- The diagonal operator on the contents of one cell with the value `u` on the empty content and
the value `v` on every filled content. -/
@[expose]
noncomputable def cellDiag (u v : ℝ) : Matrix (Option Y) (Option Y) ℂ :=
  diagonal fun a ↦ ((Option.elim a u fun _ ↦ v : ℝ) : ℂ)

/-- The projector onto the empty content of one cell. -/
@[expose]
noncomputable def cellEmpty : Matrix (Option Y) (Option Y) ℂ :=
  diagonal fun a ↦ if a = none then 1 else 0

/-- A two-level cell potential is a scalar minus its empty-sector correction. -/
theorem cellDiag_eq (u v : ℝ) :
    (cellDiag u v : Matrix (Option Y) (Option Y) ℂ) = v • 1 - (v - u) • cellEmpty := by
  ext a b
  rcases a with _ | a <;> rcases b with _ | b <;>
    simp [cellDiag, cellEmpty, diagonal_apply, one_apply]

/-- Adding a scalar shifts both values of a cell potential. -/
theorem cellDiag_add_smul_one (u v θ : ℝ) :
    (cellDiag u v : Matrix (Option Y) (Option Y) ℂ) + θ • 1 = cellDiag (u + θ) (v + θ) := by
  ext a b
  rcases a with _ | a <;> rcases b with _ | b
  all_goals simp [cellDiag, diagonal_apply, one_apply, ite_add_ite]

/-- `cellDiag u v` is positive semidefinite when `u` and `v` are nonnegative. -/
theorem posSemidef_cellDiag {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) :
    (cellDiag u v : Matrix (Option Y) (Option Y) ℂ).PosSemidef := by
  refine PosSemidef.diagonal fun a ↦ ?_
  rcases a with _ | a <;> simpa using Complex.zero_le_real.mpr ‹_›

/-- The empty-sector projector is positive semidefinite. -/
theorem posSemidef_cellEmpty : (cellEmpty : Matrix (Option Y) (Option Y) ℂ).PosSemidef :=
  PosSemidef.diagonal fun a ↦ by by_cases h : a = none <;> simp [h]

variable [Fintype Y] [AddCommGroup Y]

/-- **The phase cell is unitary.** -/
theorem conjTranspose_phaseCell_mul_self (χ : AddChar Y ℂ) :
    (phaseCell Y χ)ᴴ * phaseCell Y χ = 1 := by
  have hd : (diagonal fun a : Option Y ↦ χ (a.getD 0))ᴴ *
      diagonal (fun a : Option Y ↦ χ (a.getD 0)) = 1 := by
    rw [diagonal_conjTranspose, diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext a
    rw [Pi.star_apply, RCLike.star_def, Complex.conj_mul', AddChar.norm_apply]
    simp
  rw [phaseCell]
  simp only [conjTranspose_mul, conjTranspose_cellCompress, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (cellCompress Y) (cellCompress Y), cellCompress_mul_self,
    Matrix.one_mul, ← Matrix.mul_assoc _ (diagonal _), hd, Matrix.one_mul, cellCompress_mul_self]

/-- **The drop of one cell.** With `u ≤ v` the potential values after the query on the empty
and on the filled contents, the drop operator of the cell is
`cellDiag (p₀ + θ - v) (p₁ + θ - v) + (v - u) Pᴴ |⊥⟩⟨⊥| P`: the cell potential falls from `v`
to `u` on the empty content after the query, and the phase cell is unitary. -/
theorem cellDiag_add_sub_eq (χ : AddChar Y ℂ) (p₀ p₁ u v θ : ℝ) :
    cellDiag p₀ p₁ + θ • 1 - (phaseCell Y χ)ᴴ * cellDiag u v * phaseCell Y χ =
      cellDiag (p₀ + θ - v) (p₁ + θ - v) +
        (v - u) • ((phaseCell Y χ)ᴴ * cellEmpty * phaseCell Y χ) := by
  have h : (cellDiag (p₀ + θ - v) (p₁ + θ - v) : Matrix (Option Y) (Option Y) ℂ) =
      cellDiag p₀ p₁ + θ • 1 - v • 1 := by
    rw [cellDiag_add_smul_one]
    ext a b
    rcases a with _ | a <;> rcases b with _ | b
    all_goals simp [cellDiag, diagonal_apply, one_apply, ite_sub_ite]
  rw [h, cellDiag_eq u v, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.mul_one, conjTranspose_phaseCell_mul_self, Matrix.mul_smul, Matrix.smul_mul]
  abel

/-- **The drop of one cell is nonnegative** when the drop coefficients `p₀ + θ - v`,
`p₁ + θ - v` are nonnegative and the potential after the query is monotone, `u ≤ v`. -/
theorem posSemidef_cellDrop (χ : AddChar Y ℂ) {p₀ p₁ u v θ : ℝ} (h₀ : 0 ≤ p₀ + θ - v)
    (h₁ : 0 ≤ p₁ + θ - v) (huv : u ≤ v) :
    (cellDiag p₀ p₁ + θ • 1 - (phaseCell Y χ)ᴴ * cellDiag u v * phaseCell Y χ).PosSemidef := by
  rw [cellDiag_add_sub_eq]
  exact (posSemidef_cellDiag h₀ h₁).add
    ((posSemidef_cellEmpty.conjTranspose_mul_mul_same _).smul (sub_nonneg.mpr huv))

end cell

/-! ## The leak of one cell -/

/-- **The leak condition of one cell**, for a rate `lam`, drop coefficients `a₀` (empty content)
and `a₁` (filled contents), and the proportion `β` of filled contents on which the event
differs from its value on the empty content: either nothing flips, or both coefficients are
positive, `β (1 / a₀ + 5 / a₁) ≤ lam` and `6 β ≤ lam a₁`. -/
@[expose]
def LeakBound (lam a₀ a₁ β : ℝ) : Prop :=
  β = 0 ∨ (0 < a₀ ∧ 0 < a₁ ∧ β * (a₀⁻¹ + 5 * a₁⁻¹) ≤ lam ∧ 6 * β ≤ lam * a₁)

/-- The leak condition is monotone in the proportion of flipped contents. -/
theorem LeakBound.mono {lam a₀ a₁ β β' : ℝ} (h : LeakBound lam a₀ a₁ β) (hβ' : 0 ≤ β')
    (hle : β' ≤ β) : LeakBound lam a₀ a₁ β' := by
  rcases h with h | ⟨h₀, h₁, h₂, h₃⟩
  · exact Or.inl (le_antisymm (h ▸ hle) hβ')
  · exact Or.inr ⟨h₀, h₁, (mul_le_mul_of_nonneg_right hle (by positivity)).trans h₂,
      by linarith⟩

/-- Positive weights `a ≤ b` give the round-6 rate `1/a + 5/b` for every nonnegative
flipped proportion. -/
theorem leakBound_of_pos_of_le {a b β : ℝ} (ha : 0 < a) (hab : a ≤ b) (hβ : 0 ≤ β) :
    LeakBound (β * (a⁻¹ + 5 * b⁻¹)) a b β := by
  have hb : 0 < b := ha.trans_le hab
  refine Or.inr ⟨ha, hb, le_rfl, ?_⟩
  have hratio : 1 ≤ b / a := (le_div_iff₀ ha).mpr (by simpa using hab)
  have heq : (a⁻¹ + 5 * b⁻¹) * b = b / a + 5 := by field_simp
  rw [mul_assoc, heq]
  nlinarith

/-- Equation (77)'s calibration: `1 < α ≤ 6` and `β = 5α/(α−1)`. -/
theorem leakBound_alpha {α b : ℝ} (hα : 1 < α) (hα6 : α ≤ 6) (hb : 0 ≤ b) :
    LeakBound b α (5 * α / (α - 1)) b := by
  have ha : 0 < α := by linarith
  have had : 0 < α - 1 := by linarith
  have hβ : 0 < 5 * α / (α - 1) := by positivity
  have hβ6 : 6 ≤ 5 * α / (α - 1) := (le_div_iff₀ had).mpr (by linarith)
  have heq : α⁻¹ + 5 * (5 * α / (α - 1))⁻¹ = 1 := by
    field_simp
    ring
  refine Or.inr ⟨ha, hβ, ?_, ?_⟩
  · rw [heq, mul_one]
  · nlinarith

section leak

variable {Y : Type*} [Fintype Y] [DecidableEq Y]

/-- The projector onto the filled contents of one cell that lie in `fl`. -/
@[expose]
noncomputable def flipCell (fl : Finset Y) : Matrix (Option Y) (Option Y) ℂ :=
  diagonal fun a ↦ Option.elim a 0 fun y ↦ if y ∈ fl then 1 else 0

/-- The flip projector keeps exactly the coordinates in the flipped set. -/
theorem flipCell_mulVec_apply (fl : Finset Y) (ψ : Option Y → ℂ) (a : Option Y) :
    (flipCell fl *ᵥ ψ) a = Option.elim a 0 (fun y ↦ if y ∈ fl then 1 else 0) * ψ a := by
  rw [flipCell, mulVec_diagonal]

variable [AddCommGroup Y]

/-- The commutator of the flip projector with the phase cell, applied to a vector. -/
theorem flipCommutator_mulVec_apply (χ : AddChar Y ℂ) (fl : Finset Y) (ψ : Option Y → ℂ)
    (a : Option Y) :
    ((flipCell fl * phaseCell Y χ - phaseCell Y χ * flipCell fl) *ᵥ ψ) a =
      Option.elim a 0 (fun y ↦ if y ∈ fl then 1 else 0) * (phaseCell Y χ *ᵥ ψ) a -
        (phaseCell Y χ *ᵥ fun b ↦ Option.elim b 0 (fun y ↦ if y ∈ fl then 1 else 0) * ψ b) a := by
  have hT : flipCell fl *ᵥ ψ = fun b ↦ Option.elim b 0 (fun y ↦ if y ∈ fl then 1 else 0) * ψ b :=
    funext (flipCell_mulVec_apply fl ψ)
  rw [sub_mulVec, ← mulVec_mulVec, ← mulVec_mulVec, Pi.sub_apply, flipCell_mulVec_apply, hT]

/-- The entry of the commutator of the flip projector with the phase cell at a flipped filled
content: only the empty content and the unflipped filled contents contribute. -/
theorem flipCommutator_mulVec_some_of_mem {χ : AddChar Y ℂ} (hχ : χ ≠ 0) {fl : Finset Y}
    {y : Y} (hy : y ∈ fl) (ψ : Option Y → ℂ) :
    ((flipCell fl * phaseCell Y χ - phaseCell Y χ * flipCell fl) *ᵥ ψ) (some y) =
      cellAmp Y * (χ y * ψ none +
        (1 - χ y) * (cellAmp Y * ∑ w, if w ∈ fl then 0 else ψ (some w)) -
          cellAmp Y * ∑ w, χ w * if w ∈ fl then 0 else ψ (some w)) := by
  have hw : ∀ w, phaseCell Y χ (some y) (some w) * ψ (some w) -
      phaseCell Y χ (some y) (some w) * ((if w ∈ fl then 1 else 0) * ψ (some w)) =
      cellAmp Y * cellAmp Y * (1 - χ y - χ w) * (if w ∈ fl then 0 else ψ (some w)) := fun w ↦ by
    by_cases hw : w ∈ fl
    · simp [hw]
    · have hyw : y ≠ w := fun h ↦ hw (h ▸ hy)
      simp only [hw, ite_false, zero_mul, mul_zero, sub_zero, phaseCell_some_some hχ, hyw,
        zero_add, cellAmp_mul_self]
  have hsum : ∑ w, cellAmp Y * cellAmp Y * (1 - χ y - χ w) * (if w ∈ fl then 0 else ψ (some w)) =
      cellAmp Y * ((1 - χ y) * (cellAmp Y * ∑ w, if w ∈ fl then 0 else ψ (some w))) -
        cellAmp Y * (cellAmp Y * ∑ w, χ w * if w ∈ fl then 0 else ψ (some w)) := by
    simp only [Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun w _ ↦ by ring
  rw [flipCommutator_mulVec_apply, mulVec, mulVec, dotProduct, dotProduct]
  simp only [Option.elim_some, hy, ite_true, one_mul]
  rw [← Finset.sum_sub_distrib, Fintype.sum_option]
  simp only [Option.elim_none, Option.elim_some, zero_mul, mul_zero, sub_zero, hw, hsum,
    phaseCell_some_none hχ]
  ring

/-- The entry of the commutator of the flip projector with the phase cell at a content outside
the flipped set: only the flipped filled contents contribute. -/
theorem flipCommutator_mulVec_of_elim_eq_zero (χ : AddChar Y ℂ) {fl : Finset Y} {a : Option Y}
    (ha : Option.elim a 0 (fun y ↦ if y ∈ fl then 1 else 0) = (0 : ℂ)) (ψ : Option Y → ℂ) :
    ((flipCell fl * phaseCell Y χ - phaseCell Y χ * flipCell fl) *ᵥ ψ) a =
      -∑ w, phaseCell Y χ a (some w) * if w ∈ fl then ψ (some w) else 0 := by
  rw [flipCommutator_mulVec_apply, ha, zero_mul, zero_sub, mulVec, dotProduct, Fintype.sum_option]
  simp only [Option.elim_none, Option.elim_some, zero_mul, mul_zero, zero_add, ite_mul, one_mul]

/-- The phase component of a vector after deleting the filled contents in `fl`. -/
@[expose]
noncomputable def unflippedPhase (χ : AddChar Y ℂ) (fl : Finset Y)
    (ψ : Option Y → ℂ) : ℂ :=
  cellAmp Y * ∑ w, χ w * if w ∈ fl then 0 else ψ (some w)

/-- The three-coefficient leak condition of bounds-note equation (107). -/
@[expose]
def PhaseLeakBound (lam a₀ a₁ d β : ℝ) : Prop :=
  β = 0 ∨ (0 < a₀ ∧ 0 < a₁ ∧
    β * (a₀⁻¹ + 4 * a₁⁻¹ + (a₁ + d)⁻¹) ≤ lam ∧ 6 * β ≤ lam * a₁)

/-- The binary phase-cell commutator with three source coefficients. The last term retains
only the phase component of the unflipped source, as in bounds-note equations (100), (107). -/
theorem sum_norm_flipCommutator_sq_le (χ : AddChar Y ℂ) (fl : Finset Y)
    {lam a₀ a₁ d : ℝ} (hlam : 0 ≤ lam) (h₀ : 0 ≤ a₀) (h₁ : 0 ≤ a₁) (hd : 0 ≤ d)
    (hleak : PhaseLeakBound lam a₀ a₁ d (fl.card / Fintype.card Y)) (ψ : Option Y → ℂ) :
    ∑ a, ‖((flipCell fl * phaseCell Y χ - phaseCell Y χ * flipCell fl) *ᵥ ψ) a‖ ^ 2 ≤
      lam * (a₀ * ‖ψ none‖ ^ 2 + a₁ * ∑ y, ‖ψ (some y)‖ ^ 2 +
        d * ‖unflippedPhase χ fl ψ‖ ^ 2) := by
  set K := flipCell fl * phaseCell Y χ - phaseCell Y χ * flipCell fl with hKdef
  have hR : 0 ≤ lam * (a₀ * ‖ψ none‖ ^ 2 + a₁ * ∑ y, ‖ψ (some y)‖ ^ 2 +
      d * ‖unflippedPhase χ fl ψ‖ ^ 2) := by positivity
  by_cases hK0 : K = 0
  · simpa [hK0] using hR
  have hχ : χ ≠ 0 := fun h ↦ hK0 (by
    rw [hKdef, h, phaseCell_zero, Matrix.mul_one, Matrix.one_mul, sub_self])
  have hfl : fl.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    rintro rfl
    refine hK0 ?_
    have h0 : flipCell (∅ : Finset Y) = 0 := by
      rw [flipCell, ← diagonal_zero]
      congr 1
      funext a
      rcases a with _ | a <;> simp
    rw [hKdef, h0, Matrix.zero_mul, Matrix.mul_zero, sub_self]
  obtain ⟨N, hNdef⟩ : ∃ N : ℝ, N = Fintype.card Y := ⟨_, rfl⟩
  have hN : 0 < N := hNdef ▸ Nat.cast_pos.mpr Fintype.card_pos
  rw [← hNdef] at hleak
  have hβ : 0 < (fl.card : ℝ) / N := div_pos (Nat.cast_pos.mpr hfl.card_pos) hN
  obtain ⟨hA, hB, hν, h6⟩ := hleak.resolve_left hβ.ne'
  set β : ℝ := (fl.card : ℝ) / N with hβdef
  set a := cellAmp Y with hadef
  set φ₀ : Y → ℂ := fun w ↦ if w ∈ fl then 0 else ψ (some w) with hφ₀
  set S := a * ∑ w, φ₀ w with hS
  set G := a * ∑ w, χ w * φ₀ w with hG
  set W₀ := ∑ w, ‖φ₀ w‖ ^ 2 with hW₀
  set W₁ := ∑ w, if w ∈ fl then ‖ψ (some w)‖ ^ 2 else 0 with hW₁
  have hW : ∑ y, ‖ψ (some y)‖ ^ 2 = W₀ + W₁ := by
    rw [hW₀, hW₁, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun w _ ↦ by by_cases hw : w ∈ fl <;> simp [φ₀, hw]
  have hW₁0 : 0 ≤ W₁ := Finset.sum_nonneg fun w _ ↦ by positivity
  have ha2 : ‖a‖ ^ 2 = N⁻¹ := by rw [hadef, norm_cellAmp_sq, hNdef]
  have hNc : (Fintype.card Y : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  -- Bessel's inequality for the two components of the unflipped part.
  have hbessel : ‖S‖ ^ 2 + ‖G‖ ^ 2 ≤ W₀ := by
    have hs := sum_apply_eq_zero_of_ne_zero hχ
    have hχχ : ∀ w, starRingEnd ℂ (χ w) * χ w = 1 := fun w ↦ by
      rw [Complex.conj_mul', AddChar.norm_apply]
      simp
    have e₁ : (fun _ : Y ↦ a) ⬝ᵥ star (fun _ : Y ↦ a) = 1 := by
      simp only [dotProduct, Pi.star_apply, hadef, star_cellAmp, cellAmp_mul_self,
        Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      exact mul_inv_cancel₀ hNc
    have e₂ : (fun w ↦ a * starRingEnd ℂ (χ w)) ⬝ᵥ star (fun w ↦ a * starRingEnd ℂ (χ w)) = 1 := by
      simp only [dotProduct, Pi.star_apply, star_mul', hadef, star_cellAmp, RCLike.star_def,
        Complex.conj_conj]
      calc ∑ w, cellAmp Y * starRingEnd ℂ (χ w) * (cellAmp Y * χ w)
          = ∑ _w : Y, cellAmp Y * cellAmp Y :=
            Finset.sum_congr rfl fun w _ ↦ by
              rw [show cellAmp Y * starRingEnd ℂ (χ w) * (cellAmp Y * χ w) =
                cellAmp Y * cellAmp Y * (starRingEnd ℂ (χ w) * χ w) by ring, hχχ, mul_one]
        _ = 1 := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, cellAmp_mul_self]
          exact mul_inv_cancel₀ hNc
    have e₁₂ : (fun w ↦ a * starRingEnd ℂ (χ w)) ⬝ᵥ star (fun _ : Y ↦ a) = 0 := by
      simp only [dotProduct, Pi.star_apply, hadef, star_cellAmp]
      calc ∑ w, cellAmp Y * starRingEnd ℂ (χ w) * cellAmp Y
          = cellAmp Y * cellAmp Y * starRingEnd ℂ (∑ w, χ w) := by
            rw [map_sum, Finset.mul_sum]
            exact Finset.sum_congr rfl fun w _ ↦ by ring
        _ = 0 := by rw [hs, map_zero, mul_zero]
    have hb := norm_dotProduct_star_sq_add_le e₁ e₂ e₁₂ φ₀
    have hS' : φ₀ ⬝ᵥ star (fun _ : Y ↦ a) = S := by
      simp only [dotProduct, Pi.star_apply, hS, hadef, star_cellAmp, Finset.mul_sum]
      exact Finset.sum_congr rfl fun w _ ↦ by ring
    have hG' : φ₀ ⬝ᵥ star (fun w ↦ a * starRingEnd ℂ (χ w)) = G := by
      simp only [dotProduct, Pi.star_apply, star_mul', hG, hadef, star_cellAmp, RCLike.star_def,
        Complex.conj_conj, Finset.mul_sum]
      exact Finset.sum_congr rfl fun w _ ↦ by ring
    rwa [hS', hG'] at hb
  -- The rows at flipped contents.
  set X := ‖ψ none‖ + 2 * ‖S‖ + ‖G‖ with hX
  have hrow1 : ∀ y ∈ fl, ‖(K *ᵥ ψ) (some y)‖ ^ 2 ≤ N⁻¹ * X ^ 2 := fun y hy ↦ by
    rw [hKdef, flipCommutator_mulVec_some_of_mem hχ hy]
    change ‖a * (χ y * ψ none + (1 - χ y) * S - G)‖ ^ 2 ≤ _
    rw [norm_mul, mul_pow, ha2]
    refine mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) ?_ 2) (by positivity)
    have h1 : ‖1 - χ y‖ ≤ 2 :=
      (norm_sub_le _ _).trans (by rw [norm_one, AddChar.norm_apply]; norm_num)
    calc ‖χ y * ψ none + (1 - χ y) * S - G‖
        ≤ ‖χ y * ψ none‖ + ‖(1 - χ y) * S‖ + ‖G‖ :=
          (norm_sub_le _ _).trans (add_le_add_left (norm_add_le _ _) _)
      _ ≤ X := by
          rw [norm_mul, norm_mul, AddChar.norm_apply, one_mul, hX]
          gcongr
  -- The rows at the other contents.
  have hrow0 : ∀ b : Option Y, Option.elim b 0 (fun y ↦ if y ∈ fl then 1 else 0) = (0 : ℂ) →
      ‖(K *ᵥ ψ) b‖ ^ 2 ≤
        (∑ w, if w ∈ fl then ‖phaseCell Y χ b (some w)‖ ^ 2 else 0) * W₁ := fun b hb ↦ by
    rw [hKdef, flipCommutator_mulVec_of_elim_eq_zero χ hb, norm_neg]
    calc ‖∑ w, phaseCell Y χ b (some w) * if w ∈ fl then ψ (some w) else 0‖ ^ 2
        ≤ (∑ w, (if w ∈ fl then ‖phaseCell Y χ b (some w)‖ else 0) *
            (if w ∈ fl then ‖ψ (some w)‖ else 0)) ^ 2 := by
          refine pow_le_pow_left₀ (norm_nonneg _) ((norm_sum_le _ _).trans_eq ?_) 2
          exact Finset.sum_congr rfl fun w _ ↦ by by_cases hw : w ∈ fl <;> simp [hw]
      _ ≤ (∑ w, (if w ∈ fl then ‖phaseCell Y χ b (some w)‖ else 0) ^ 2) *
            ∑ w, (if w ∈ fl then ‖ψ (some w)‖ else 0) ^ 2 :=
          Finset.sum_mul_sq_le_sq_mul_sq _ _ _
      _ = _ := by
          congr 1 <;> exact Finset.sum_congr rfl fun w _ ↦ by by_cases hw : w ∈ fl <;> simp [hw]
  -- The columns at flipped contents.
  have hcol : ∀ w ∈ fl, ‖phaseCell Y χ none (some w)‖ ^ 2 +
      ∑ y, (if y ∈ fl then 0 else ‖phaseCell Y χ (some y) (some w)‖ ^ 2) ≤ 6 / N := by
    intro w hw
    have h := sum_ite_norm_phaseCell_sq_le χ w
    rw [Fintype.sum_option, ← hNdef] at h
    simp only [reduceCtorEq, ite_false, Option.some.injEq] at h
    refine le_trans ?_ h
    rw [phaseCell_apply_comm χ none (some w)]
    refine add_le_add le_rfl (Finset.sum_le_sum fun y _ ↦ ?_)
    by_cases hy : y ∈ fl
    · simp only [hy, ite_true]
      split_ifs <;> positivity
    · have hwy : w ≠ y := fun h ↦ hy (h ▸ hw)
      simp only [hy, hwy, ite_false, phaseCell_apply_comm χ (some y) (some w), le_refl]
  -- Assembly.
  have hsplit : ∑ a, ‖(K *ᵥ ψ) a‖ ^ 2 =
      (∑ y, if y ∈ fl then ‖(K *ᵥ ψ) (some y)‖ ^ 2 else 0) +
        (‖(K *ᵥ ψ) none‖ ^ 2 + ∑ y, if y ∈ fl then 0 else ‖(K *ᵥ ψ) (some y)‖ ^ 2) := by
    rw [Fintype.sum_option, add_left_comm, ← Finset.sum_add_distrib]
    congr 1
    exact Finset.sum_congr rfl fun y _ ↦ by by_cases hy : y ∈ fl <;> simp [hy]
  have hcount : ∀ c : ℝ, (∑ y : Y, if y ∈ fl then c else 0) = fl.card * c := fun c ↦ by
    rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul]
  have hT1 : (∑ y, if y ∈ fl then ‖(K *ᵥ ψ) (some y)‖ ^ 2 else 0) ≤ β * X ^ 2 := by
    calc (∑ y, if y ∈ fl then ‖(K *ᵥ ψ) (some y)‖ ^ 2 else 0)
        ≤ ∑ y : Y, if y ∈ fl then N⁻¹ * X ^ 2 else 0 :=
          Finset.sum_le_sum fun y _ ↦ by
            by_cases hy : y ∈ fl
            · simp only [hy, ite_true]
              exact hrow1 y hy
            · simp [hy]
      _ = β * X ^ 2 := by rw [hcount, hβdef]; ring
  have hT2 : ‖(K *ᵥ ψ) none‖ ^ 2 + (∑ y, if y ∈ fl then 0 else ‖(K *ᵥ ψ) (some y)‖ ^ 2) ≤
      6 * β * W₁ := by
    set g : Option Y → ℝ := fun b ↦ ∑ w, if w ∈ fl then ‖phaseCell Y χ b (some w)‖ ^ 2 else 0
    calc ‖(K *ᵥ ψ) none‖ ^ 2 + (∑ y, if y ∈ fl then 0 else ‖(K *ᵥ ψ) (some y)‖ ^ 2)
        ≤ g none * W₁ + ∑ y, if y ∈ fl then 0 else g (some y) * W₁ := by
          refine add_le_add (hrow0 none rfl) (Finset.sum_le_sum fun y _ ↦ ?_)
          by_cases hy : y ∈ fl
          · simp [hy]
          · simp only [hy, ite_false]
            exact hrow0 (some y) (by simp [hy])
      _ = (∑ w : Y, if w ∈ fl then ‖phaseCell Y χ none (some w)‖ ^ 2 +
            ∑ y, (if y ∈ fl then 0 else ‖phaseCell Y χ (some y) (some w)‖ ^ 2) else 0) * W₁ := by
          have hs : (∑ y, if y ∈ fl then 0 else g (some y) * W₁) =
              (∑ y, if y ∈ fl then 0 else g (some y)) * W₁ := by
            rw [Finset.sum_mul]
            exact Finset.sum_congr rfl fun y _ ↦ by
              by_cases hy : y ∈ fl <;> simp [hy]
          rw [hs, ← add_mul]
          congr 1
          simp only [g]
          rw [show (∑ y, if y ∈ fl then 0 else
              ∑ w, if w ∈ fl then ‖phaseCell Y χ (some y) (some w)‖ ^ 2 else 0) =
              ∑ w, if w ∈ fl then
                ∑ y, if y ∈ fl then 0 else ‖phaseCell Y χ (some y) (some w)‖ ^ 2
                else 0 by
            calc
              _ = ∑ y, ∑ w, if w ∈ fl then
                  (if y ∈ fl then 0 else ‖phaseCell Y χ (some y) (some w)‖ ^ 2)
                  else 0 := Finset.sum_congr rfl fun y _ ↦ by
                    by_cases hy : y ∈ fl <;> simp [hy]
              _ = ∑ w, ∑ y, if w ∈ fl then
                  (if y ∈ fl then 0 else ‖phaseCell Y χ (some y) (some w)‖ ^ 2)
                  else 0 := Finset.sum_comm
              _ = _ := Finset.sum_congr rfl fun w _ ↦ by
                by_cases hw : w ∈ fl <;> simp [hw]]
          rw [← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl fun w _ ↦ by
            by_cases hw : w ∈ fl <;> simp [hw]
      _ ≤ (∑ w : Y, if w ∈ fl then 6 / N else 0) * W₁ := by
          refine mul_le_mul_of_nonneg_right (Finset.sum_le_sum fun w _ ↦ ?_) hW₁0
          by_cases hw : w ∈ fl
          · simp only [hw, ite_true]
            exact hcol w hw
          · simp [hw]
      _ = 6 * β * W₁ := by rw [hcount, hβdef]; ring
  have hGfull : unflippedPhase χ fl ψ = G := rfl
  have e1 : β * X ^ 2 ≤ lam * (a₀ * ‖ψ none‖ ^ 2 + a₁ * W₀ + d * ‖G‖ ^ 2) := by
    calc β * X ^ 2
        ≤ β * ((a₀⁻¹ + 4 * a₁⁻¹ + (a₁ + d)⁻¹) *
            (a₀ * ‖ψ none‖ ^ 2 + a₁ * ‖S‖ ^ 2 + (a₁ + d) * ‖G‖ ^ 2)) :=
          mul_le_mul_of_nonneg_left
            (sq_add_two_mul_add_le_three hA hB (by positivity) _ _ _) hβ.le
      _ ≤ β * ((a₀⁻¹ + 4 * a₁⁻¹ + (a₁ + d)⁻¹) *
            (a₀ * ‖ψ none‖ ^ 2 + a₁ * W₀ + d * ‖G‖ ^ 2)) := by
          apply mul_le_mul_of_nonneg_left _ hβ.le
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          nlinarith [mul_le_mul_of_nonneg_left hbessel h₁]
      _ = β * (a₀⁻¹ + 4 * a₁⁻¹ + (a₁ + d)⁻¹) *
            (a₀ * ‖ψ none‖ ^ 2 + a₁ * W₀ + d * ‖G‖ ^ 2) := by ring
      _ ≤ lam * (a₀ * ‖ψ none‖ ^ 2 + a₁ * W₀ + d * ‖G‖ ^ 2) :=
          mul_le_mul_of_nonneg_right hν (by positivity)
  have e2 : 6 * β * W₁ ≤ lam * a₁ * W₁ := mul_le_mul_of_nonneg_right h6 hW₁0
  rw [hsplit, hW, hGfull]
  nlinarith [hT1, hT2, e1, e2]

omit [AddCommGroup Y] in
/-- The quadratic form of a two-level cell potential. -/
theorem re_star_dotProduct_cellDiag_mulVec (a₀ a₁ : ℝ) (ψ : Option Y → ℂ) :
    (star ψ ⬝ᵥ (cellDiag a₀ a₁ *ᵥ ψ)).re =
      a₀ * ‖ψ none‖ ^ 2 + a₁ * ∑ y, ‖ψ (some y)‖ ^ 2 := by
  have e : ∀ (r : ℝ) (z : ℂ), (star z * ((r : ℂ) * z)).re = r * ‖z‖ ^ 2 := fun r z ↦ by
    rw [mul_left_comm, RCLike.star_def, Complex.conj_mul', ← Complex.ofReal_pow,
      ← Complex.ofReal_mul, Complex.ofReal_re]
  simp only [cellDiag, mulVec_diagonal, dotProduct, Fintype.sum_option, Pi.star_apply,
    Option.elim_none, Option.elim_some, Complex.add_re, Complex.re_sum, e, Finset.mul_sum]

/-- The occupancy-sensitive positive-operator bound for a binary cell event, bounds-note (77).
This supports NOTE's refinement of the paper's §9.3 collision-event argument
(Lemma 9.6, p. 61; event bound, pp. 64–65).
The rate satisfies the weighted Cauchy–Schwarz condition and absorbs the reverse cross block. -/
theorem posSemidef_smul_cellDiag_sub_flip (χ : AddChar Y ℂ) (fl : Finset Y) {lam a₀ a₁ : ℝ}
    (hlam : 0 ≤ lam) (h₀ : 0 ≤ a₀) (h₁ : 0 ≤ a₁)
    (hleak : LeakBound lam a₀ a₁ (fl.card / Fintype.card Y)) :
    (lam • cellDiag a₀ a₁ - (flipCell fl * phaseCell Y χ - phaseCell Y χ * flipCell fl)ᴴ *
      (flipCell fl * phaseCell Y χ - phaseCell Y χ * flipCell fl)).PosSemidef := by
  set K := flipCell fl * phaseCell Y χ - phaseCell Y χ * flipCell fl
  refine posSemidef_of_re_dotProduct_mulVec_nonneg
    (((posSemidef_cellDiag h₀ h₁).smul hlam).isHermitian.sub
      (isHermitian_conjTranspose_mul_self K)) fun ψ ↦ ?_
  rw [sub_mulVec, dotProduct_sub, star_dotProduct_conjTranspose_mul_self_mulVec, Complex.sub_re,
    re_star_dotProduct_self, smul_mulVec, dotProduct_smul, Complex.smul_re, smul_eq_mul,
    re_star_dotProduct_cellDiag_mulVec,
    sub_nonneg]
  have hleak' : PhaseLeakBound lam a₀ a₁ 0 (fl.card / Fintype.card Y) := by
    rcases hleak with h | ⟨ha, hb, hν, h6⟩
    · exact Or.inl h
    · refine Or.inr ⟨ha, hb, ?_, h6⟩
      simpa only [add_zero, show 4 * a₁⁻¹ + a₁⁻¹ = 5 * a₁⁻¹ by ring,
        add_assoc] using hν
  simpa only [zero_mul, add_zero] using
    sum_norm_flipCommutator_sq_le χ fl hlam h₀ h₁ le_rfl hleak' ψ

/-- The omitted part of the phase component has squared norm at most the flipped proportion
of the full source norm. -/
theorem norm_phase_flipped_sq_le (χ : AddChar Y ℂ) (fl : Finset Y)
    (ψ : Option Y → ℂ) :
    ‖cellAmp Y * ∑ y, χ y * if y ∈ fl then ψ (some y) else 0‖ ^ 2 ≤
      (fl.card / Fintype.card Y : ℝ) * ∑ a, ‖ψ a‖ ^ 2 := by
  rw [norm_mul, mul_pow, norm_cellAmp_sq]
  have hsum : ‖∑ y, χ y * if y ∈ fl then ψ (some y) else 0‖ ≤
      ∑ y ∈ fl, ‖ψ (some y)‖ := by
    calc _ ≤ ∑ y, ‖χ y * if y ∈ fl then ψ (some y) else 0‖ := norm_sum_le _ _
      _ = _ := by
        simp only [norm_mul, AddChar.norm_apply, one_mul, apply_ite norm,
          norm_zero, Finset.sum_ite_mem, Finset.univ_inter]
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq fl (fun _ ↦ (1 : ℝ))
    (fun y ↦ ‖ψ (some y)‖)
  simp only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one] at hcs
  have hs : (∑ y ∈ fl, ‖ψ (some y)‖ ^ 2) ≤ ∑ a, ‖ψ a‖ ^ 2 := by
    rw [Fintype.sum_option]
    exact (Finset.sum_le_univ_sum_of_nonneg fun _ ↦ sq_nonneg _).trans
      (le_add_of_nonneg_left (sq_nonneg _))
  calc _ ≤ (Fintype.card Y : ℝ)⁻¹ *
          ((fl.card : ℝ) * ∑ a, ‖ψ a‖ ^ 2) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact ((pow_le_pow_left₀ (norm_nonneg _) hsum 2).trans hcs).trans
          (mul_le_mul_of_nonneg_left hs (by positivity))
    _ = _ := by ring

/-- Replacing the unflipped phase component by the full component costs the additive term
from bounds-note (104b). This form uses Young's inequality, as in the runtime certificate. -/
theorem norm_unflippedPhase_sq_le {χ : AddChar Y ℂ} (hχ : χ ≠ 0) (fl : Finset Y)
    (ψ : Option Y → ℂ) {s : ℝ} (hs : 0 < s) :
    ‖unflippedPhase χ fl ψ‖ ^ 2 ≤
      (1 + s) * ‖(phaseCell Y χ *ᵥ ψ) none‖ ^ 2 +
        (1 + s⁻¹) * (fl.card / Fintype.card Y : ℝ) * ∑ a, ‖ψ a‖ ^ 2 := by
  set R := cellAmp Y * ∑ y, χ y * if y ∈ fl then ψ (some y) else 0
  have heq : (phaseCell Y χ *ᵥ ψ) none = unflippedPhase χ fl ψ + R := by
    rw [mulVec, dotProduct, Fintype.sum_option, phaseCell_none_none hχ, zero_mul, zero_add]
    simp only [phaseCell_none_some hχ, unflippedPhase, R, Finset.mul_sum,
      ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun y _ ↦ by by_cases hy : y ∈ fl <;> simp [hy, mul_assoc]
  have hnorm : ‖unflippedPhase χ fl ψ‖ ≤ ‖(phaseCell Y χ *ᵥ ψ) none‖ + ‖R‖ := by
    rw [← sub_eq_iff_eq_add.mpr heq]
    exact norm_sub_le _ _
  have hyoung (x y : ℝ) : (x + y) ^ 2 ≤ (1 + s) * x ^ 2 + (1 + s⁻¹) * y ^ 2 := by
    apply (mul_le_mul_iff_right₀ hs).mp
    have hss : s⁻¹ * s = 1 := inv_mul_cancel₀ hs.ne'
    nlinarith [sq_nonneg (s * x - y)]
  calc _ ≤ (‖(phaseCell Y χ *ᵥ ψ) none‖ + ‖R‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) hnorm 2
    _ ≤ (1 + s) * ‖(phaseCell Y χ *ᵥ ψ) none‖ ^ 2 + (1 + s⁻¹) * ‖R‖ ^ 2 :=
        hyoung _ _
    _ ≤ _ := by
        have hR := norm_phase_flipped_sq_le χ fl ψ
        dsimp [R]
        nlinarith [mul_le_mul_of_nonneg_left hR (by positivity : 0 ≤ 1 + s⁻¹)]

/-- The three-coefficient binary leak bound with the phase restriction removed. The error
coefficient is `lam * d * |fl| / N`, exactly as in bounds-note equation (107). -/
theorem sum_norm_flipCommutator_sq_le_drop (χ : AddChar Y ℂ) (fl : Finset Y)
    {lam a₀ a₁ d s : ℝ} (hlam : 0 ≤ lam) (h₀ : 0 ≤ a₀) (h₁ : 0 ≤ a₁) (hd : 0 ≤ d)
    (hs : 0 < s) (hleak : PhaseLeakBound lam a₀ a₁ d (fl.card / Fintype.card Y))
    (ψ : Option Y → ℂ) :
    ∑ a, ‖((flipCell fl * phaseCell Y χ - phaseCell Y χ * flipCell fl) *ᵥ ψ) a‖ ^ 2 ≤
      (1 + s) * lam * (a₀ * ‖ψ none‖ ^ 2 + a₁ * ∑ y, ‖ψ (some y)‖ ^ 2 +
        d * ‖(phaseCell Y χ *ᵥ ψ) none‖ ^ 2) +
        (1 + s⁻¹) * (lam * d * (fl.card / Fintype.card Y)) * ∑ a, ‖ψ a‖ ^ 2 := by
  by_cases hχ : χ = 0
  · subst χ
    simp only [phaseCell_zero, Matrix.mul_one, Matrix.one_mul, sub_self, zero_mulVec,
      Pi.zero_apply, norm_zero, zero_pow (by decide : 2 ≠ 0), Finset.sum_const_zero]
    positivity
  have h := sum_norm_flipCommutator_sq_le χ fl hlam h₀ h₁ hd hleak ψ
  have hphase := norm_unflippedPhase_sq_le hχ fl ψ hs
  have hbase : 0 ≤ a₀ * ‖ψ none‖ ^ 2 + a₁ * ∑ y, ‖ψ (some y)‖ ^ 2 := by positivity
  have hm := mul_le_mul_of_nonneg_left hphase (mul_nonneg hlam hd)
  have hb := mul_nonneg (mul_nonneg hs.le hlam) hbase
  nlinarith

/-- The three-coefficient leak bound as a positive-operator inequality, with the full
phase projector and the additive scalar error of bounds-note (107).
This supports NOTE's refinement of the paper's §9.3 collision-event argument
(Lemma 9.6, p. 61; event bound, pp. 64–65). -/
theorem posSemidef_cellDrop_sub_flip (χ : AddChar Y ℂ) (fl : Finset Y)
    {lam a₀ a₁ d s : ℝ} (hlam : 0 ≤ lam) (h₀ : 0 ≤ a₀) (h₁ : 0 ≤ a₁) (hd : 0 ≤ d)
    (hs : 0 < s) (hleak : PhaseLeakBound lam a₀ a₁ d (fl.card / Fintype.card Y)) :
    (((1 + s) * lam) • (cellDiag a₀ a₁ +
        d • ((phaseCell Y χ)ᴴ * cellEmpty * phaseCell Y χ)) +
      ((1 + s⁻¹) * (lam * d * (fl.card / Fintype.card Y))) • 1 -
        (flipCell fl * phaseCell Y χ - phaseCell Y χ * flipCell fl)ᴴ *
          (flipCell fl * phaseCell Y χ - phaseCell Y χ * flipCell fl)).PosSemidef := by
  set U := phaseCell Y χ
  set C := flipCell fl * U - U * flipCell fl
  have hD := (posSemidef_cellDiag (Y := Y) h₀ h₁).add
    ((posSemidef_cellEmpty.conjTranspose_mul_mul_same U).smul hd)
  have hE := (PosSemidef.one (n := Option Y) (R := ℂ)).smul
    (show 0 ≤ (1 + s⁻¹) * (lam * d * (fl.card / Fintype.card Y : ℝ)) by positivity)
  refine posSemidef_of_re_dotProduct_mulVec_nonneg
    (((hD.smul (by positivity : 0 ≤ (1 + s) * lam)).add hE).isHermitian.sub
      (isHermitian_conjTranspose_mul_self C)) fun ψ ↦ ?_
  have hG : (star ψ ⬝ᵥ ((Uᴴ * cellEmpty * U) *ᵥ ψ)).re = ‖(U *ᵥ ψ) none‖ ^ 2 := by
    have he : (cellEmpty : Matrix (Option Y) (Option Y) ℂ) = cellDiag 1 0 := by
      ext a b
      rcases a with _ | a <;> simp [cellEmpty, cellDiag, diagonal_apply]
    rw [← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec, ← star_mulVec,
      he, re_star_dotProduct_cellDiag_mulVec]
    ring
  have hI : (star ψ ⬝ᵥ ((1 : Matrix (Option Y) (Option Y) ℂ) *ᵥ ψ)).re =
      ∑ a, ‖ψ a‖ ^ 2 := by rw [one_mulVec, re_star_dotProduct_self]
  simp only [sub_mulVec, add_mulVec, smul_mulVec, dotProduct_sub, dotProduct_add,
    dotProduct_smul, Complex.sub_re, Complex.add_re, Complex.smul_re, smul_eq_mul,
    star_dotProduct_conjTranspose_mul_self_mulVec, re_star_dotProduct_self,
    re_star_dotProduct_cellDiag_mulVec, hG, hI, sub_nonneg]
  exact sum_norm_flipCommutator_sq_le_drop χ fl hlam h₀ h₁ hd hs hleak ψ

/-- The filled labels on which a binary event differs from its empty-cell value. -/
@[expose]
def binaryFlipSet (q : Option Y → Bool) : Finset Y :=
  Finset.univ.filter fun y ↦ q (some y) ≠ q none

omit [AddCommGroup Y] in
/-- Complementing a binary event does not change its commutator Gram matrix. -/
theorem binaryCell_commutator_gram (q : Option Y → Bool) (U : Matrix (Option Y) (Option Y) ℂ) :
    (labelProjector q true * U - U * labelProjector q true)ᴴ *
        (labelProjector q true * U - U * labelProjector q true) =
      (flipCell (binaryFlipSet q) * U - U * flipCell (binaryFlipSet q))ᴴ *
        (flipCell (binaryFlipSet q) * U - U * flipCell (binaryFlipSet q)) := by
  cases hq : q none
  · have heq : labelProjector q true = flipCell (binaryFlipSet q) := by
      apply congrArg diagonal
      funext a
      cases a with
      | none => simp [binaryFlipSet, hq]
      | some y => cases hy : q (some y) <;> simp [binaryFlipSet, hq, hy]
    rw [heq]
  · have heq : labelProjector q true = 1 - flipCell (binaryFlipSet q) := by
      rw [show (1 : Matrix (Option Y) (Option Y) ℂ) = diagonal (fun _ ↦ 1) from
        diagonal_one.symm, flipCell, diagonal_sub]
      apply congrArg diagonal
      funext a
      cases a with
      | none => simp [binaryFlipSet, hq]
      | some y => cases hy : q (some y) <;> simp [binaryFlipSet, hq, hy]
    have hc : (1 - flipCell (binaryFlipSet q)) * U -
        U * (1 - flipCell (binaryFlipSet q)) =
        -(flipCell (binaryFlipSet q) * U - U * flipCell (binaryFlipSet q)) := by
      simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one]
      abel
    rw [heq, hc]
    rw [conjTranspose_neg, neg_mul_neg]

/-- Equation (77) for an arbitrary binary event, whether its empty-cell label is true or false. -/
theorem posSemidef_smul_cellDiag_sub_binary (χ : AddChar Y ℂ) (q : Option Y → Bool)
    {lam a₀ a₁ : ℝ} (hlam : 0 ≤ lam) (h₀ : 0 ≤ a₀) (h₁ : 0 ≤ a₁)
    (hleak : LeakBound lam a₀ a₁ ((binaryFlipSet q).card / Fintype.card Y)) :
    (lam • cellDiag a₀ a₁ -
      (labelProjector q true * phaseCell Y χ - phaseCell Y χ * labelProjector q true)ᴴ *
        (labelProjector q true * phaseCell Y χ -
          phaseCell Y χ * labelProjector q true)).PosSemidef := by
  rw [binaryCell_commutator_gram]
  exact posSemidef_smul_cellDiag_sub_flip χ (binaryFlipSet q) hlam h₀ h₁ hleak

end leak

end Quantum
