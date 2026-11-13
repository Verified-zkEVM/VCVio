/-
Copyright (c) 2026 XC0R. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XC0R
-/

module
import all LatticeCrypto.Falcon.PackedFFT
public import LatticeCrypto.Falcon.PrecisionTail
public import LatticeCrypto.Falcon.Coset
import LatticeCrypto.Falcon.FFTStagesL2

/-!
# The true tree and the preimage tail at Falcon-512

`trueTree sk` is exact ffLDL⋆ (Falcon specification Alg. 9; ePrint 2026/1531 Alg. 5) of the Gram
matrix `B · B⋆` of `B = [[g, -f], [G, -F]]` (`gramFFT`), in the packed representation of this
library, with leaves `σ / √D00`.

A linear functional of the deviation `t - z` written in slot form (`slotForm a b`) has, under an
ffLDL⋆ tree of a positive Gram matrix (`PosGram`), variance proxy at most `ρ σ² 2^κ` times the
quadratic form `gramQ` of the inverse Gram matrix (`devVar_ffLDL_le`): one level of ffLDL⋆ splits
that form into the forms of the two children (`gramQ_node`, from the LDL⋆ identity
`slotQ_eq_ldl` and the split identity `slotQ_split`), and at a leaf the isotropic `σ / √D00`
costs the leaf ratio `ρ = (g00 + g11)/g00` (`norm_sq_add_le_slotQ`). Below the root every leaf
Gram matrix comes from a split, so `ρ ≤ 2` (`trueTreeLeafRatio_le_two`). At the root the NTRU
equation gives `det = q²` at every slot (`ntru_coord`), and Parseval for the packed FFT
(`Falcon.FFTStages.sum_norm_coord_ofCoeffs_sq`) turns the quadratic form of a coefficient
functional into `(‖F‖² + ‖G‖²)/q²` or `(‖f‖² + ‖g‖²)/q²` (`devVar_trueTree_le`).

`preimageTailMass_falcon512_le` is the Falcon-512 tail generic in `Z`;
`preimageTailMass_falcon512_two_pow_33_le` and `preimageTailMass_falcon512_80000_le` bound it by
`2⁻¹⁰⁰⁰` at `Z = 2^33` and at `Z = 80000`.

## What is not proved

* The leaves of VCVio's `ffSampling` (`κ = 0`) sample the four coordinates of Falcon's `n = 2`
  level with one `σ` and no `ℓ` step. The isotropic leaf doubles the variance proxy against
  Falcon's exact leaf; the tail bounds carry its leaf ratio `2`.
* Keys with coefficients in `[-127, 127]` that satisfy the NTRU equation, and trees equal to the
  true tree with leaves in `[σmin, σmax]`, are hypotheses: key generation is not covered.
-/

public section

open OracleComp OracleSpec LatticeCrypto MeasureTheory
open scoped ENNReal ComplexConjugate

namespace Falcon

variable {p : Params}

namespace RealFFTPoly

/-- The packed FFT polynomial with the given slots. -/
@[expose] noncomputable def ofCoord {k : ℕ} (f : Fin (2 ^ k) → ℂ) : RealFFTPoly k :=
  pack (Vector.ofFn fun j => (f j).re) (Vector.ofFn fun j => (f j).im)

variable {k : ℕ}

/-- Slotwise division. -/
@[expose] noncomputable def divFFT {k : ℕ} (a b : RealFFTPoly k) : RealFFTPoly k :=
  ofCoord fun j => coord a j / coord b j

/-- The adjoint `f⋆(x) = f(x⁻¹)`: slotwise conjugation. -/
@[expose] noncomputable def adjFFT {k : ℕ} (a : RealFFTPoly k) : RealFFTPoly k :=
  ofCoord fun j => conj (coord a j)

end RealFFTPoly

/-! ## The true tree -/

/-- **ffLDL⋆, exact**, of the self-adjoint Gram matrix `[[g00, g10⋆], [g10, g11]]`:
`ℓ = g10 / g00`, `D00 = g00`, `D11 = g11 - g10 g10⋆ / g00`; the left subtree is ffLDL⋆ of the
split of `D00` and the right one of the split of `D11`, each as `[[a, b⋆], [b, a]]` with
`(a, b) = splitFFT D`; a leaf is `σ / √D00`. -/
@[expose] noncomputable def ffLDL (σ : ℝ) : (κ : ℕ) → (g00 g10 g11 : RealFFTPoly κ) → FalconTree κ
  | 0, g00, _, _ => .leaf (σ / √(RealFFTPoly.re g00 ⟨0, by omega⟩))
  | k + 1, g00, g10, g11 =>
    .node (RealFFTPoly.divFFT g10 g00)
      (ffLDL σ k (Primitives.splitFFT g00).1
        (RealFFTPoly.adjFFT (Primitives.splitFFT g00).2) (Primitives.splitFFT g00).1)
      (ffLDL σ k (Primitives.splitFFT (g11 - Primitives.mulFFT g10
          (RealFFTPoly.divFFT (RealFFTPoly.adjFFT g10) g00))).1
        (RealFFTPoly.adjFFT (Primitives.splitFFT (g11 - Primitives.mulFFT g10
          (RealFFTPoly.divFFT (RealFFTPoly.adjFFT g10) g00))).2)
        (Primitives.splitFFT (g11 - Primitives.mulFFT g10
          (RealFFTPoly.divFFT (RealFFTPoly.adjFFT g10) g00))).1)

/-- The largest ratio `(g00 + g11) / g00` (trace over top-left entry) of the leaf Gram matrices of
`ffLDL`: it bounds the largest eigenvalue of each leaf Gram matrix by `ρ · g00`. -/
@[expose] noncomputable def ffLDLLeafRatio : (κ : ℕ) → (g00 g10 g11 : RealFFTPoly κ) → ℝ
  | 0, g00, _, g11 =>
    (RealFFTPoly.re g00 ⟨0, by omega⟩ + RealFFTPoly.re g11 ⟨0, by omega⟩) /
      RealFFTPoly.re g00 ⟨0, by omega⟩
  | k + 1, g00, g10, g11 =>
    max (ffLDLLeafRatio k (Primitives.splitFFT g00).1
        (RealFFTPoly.adjFFT (Primitives.splitFFT g00).2) (Primitives.splitFFT g00).1)
      (ffLDLLeafRatio k (Primitives.splitFFT (g11 - Primitives.mulFFT g10
          (RealFFTPoly.divFFT (RealFFTPoly.adjFFT g10) g00))).1
        (RealFFTPoly.adjFFT (Primitives.splitFFT (g11 - Primitives.mulFFT g10
          (RealFFTPoly.divFFT (RealFFTPoly.adjFFT g10) g00))).2)
        (Primitives.splitFFT (g11 - Primitives.mulFFT g10
          (RealFFTPoly.divFFT (RealFFTPoly.adjFFT g10) g00))).1)

variable (p) in
/-- The Gram matrix `B · B⋆` of `B = [[g, -f], [G, -F]]` in the exact packed FFT:
`(gg⋆ + ff⋆, Gg⋆ + Ff⋆, GG⋆ + FF⋆)`. -/
@[expose] noncomputable def gramFFT (sk : SecretKey p) :
    RealFFTPoly p.fftDepth × RealFFTPoly p.fftDepth × RealFFTPoly p.fftDepth :=
  let g := Primitives.exactFftInt p sk.g
  let f := Primitives.exactFftInt p sk.f
  let G := Primitives.exactFftInt p sk.capG
  let F := Primitives.exactFftInt p sk.capF
  (Primitives.mulFFT g (RealFFTPoly.adjFFT g) + Primitives.mulFFT f (RealFFTPoly.adjFFT f),
    Primitives.mulFFT G (RealFFTPoly.adjFFT g) + Primitives.mulFFT F (RealFFTPoly.adjFFT f),
    Primitives.mulFFT G (RealFFTPoly.adjFFT G) + Primitives.mulFFT F (RealFFTPoly.adjFFT F))

variable (p) in
/-- **The true tree** of a key: exact ffLDL⋆ of its Gram matrix at the signature `σ`. -/
@[expose] noncomputable def trueTree (sk : SecretKey p) : FalconTree p.fftDepth :=
  ffLDL p.sigma p.fftDepth (gramFFT p sk).1 (gramFFT p sk).2.1 (gramFFT p sk).2.2

variable (p) in
/-- The leaf ratio of the true tree. -/
@[expose] noncomputable def trueTreeLeafRatio (sk : SecretKey p) : ℝ :=
  ffLDLLeafRatio p.fftDepth (gramFFT p sk).1 (gramFFT p sk).2.1 (gramFFT p sk).2.2

private theorem ffLDLLeafRatio_self_le_two :
    ∀ (κ : ℕ) (a b : RealFFTPoly κ), ffLDLLeafRatio κ a b a ≤ 2
  | 0, a, _ => by
    rw [ffLDLLeafRatio]
    rcases eq_or_ne (RealFFTPoly.re a ⟨0, by omega⟩) 0 with h | h
    · rw [h]; norm_num
    · rw [← two_mul, mul_div_assoc, div_self h, mul_one]
  | k + 1, a, b => by
    rw [ffLDLLeafRatio]
    exact max_le (ffLDLLeafRatio_self_le_two k _ _) (ffLDLLeafRatio_self_le_two k _ _)

/-- Below the root every leaf Gram matrix of `ffLDL` comes from a split, `[[a, b⋆], [b, a]]`, so
the leaf ratio is at most `2`. -/
theorem ffLDLLeafRatio_le_two (k : ℕ) (g00 g10 g11 : RealFFTPoly (k + 1)) :
    ffLDLLeafRatio (k + 1) g00 g10 g11 ≤ 2 := by
  rw [ffLDLLeafRatio]
  exact max_le (ffLDLLeafRatio_self_le_two k _ _) (ffLDLLeafRatio_self_le_two k _ _)

/-- The leaf ratio of the true tree is at most `2` when `1 ≤ fftDepth`. -/
theorem trueTreeLeafRatio_le_two (hdepth : 1 ≤ p.fftDepth) (sk : SecretKey p) :
    trueTreeLeafRatio p sk ≤ 2 := by
  have h : ∀ (κ : ℕ), 1 ≤ κ → ∀ g00 g10 g11 : RealFFTPoly κ, ffLDLLeafRatio κ g00 g10 g11 ≤ 2 := by
    intro κ hκ
    cases κ with
    | zero => omega
    | succ k => exact ffLDLLeafRatio_le_two k
  exact h _ hdepth _ _ _

/-! ## The true tree -/

/-! ### Linear functionals in slot form and the Gram quadratic form -/

theorem RealFFTPoly.coord_ofCoord {k : ℕ} (f : Fin (2 ^ k) → ℂ) (j : Fin (2 ^ k)) :
    RealFFTPoly.coord (RealFFTPoly.ofCoord f) j = f j := by
  rw [RealFFTPoly.ofCoord, RealFFTPoly.coord_pack]
  simp

theorem RealFFTPoly.coord_divFFT {k : ℕ} (a b : RealFFTPoly k) (j : Fin (2 ^ k)) :
    RealFFTPoly.coord (RealFFTPoly.divFFT a b) j =
      RealFFTPoly.coord a j / RealFFTPoly.coord b j :=
  RealFFTPoly.coord_ofCoord _ _

theorem RealFFTPoly.coord_adjFFT {k : ℕ} (a : RealFFTPoly k) (j : Fin (2 ^ k)) :
    RealFFTPoly.coord (RealFFTPoly.adjFFT a) j = conj (RealFFTPoly.coord a j) :=
  RealFFTPoly.coord_ofCoord _ _

/-- The linear functional `x ↦ Σⱼ Re(conj aⱼ · x₀ⱼ + conj bⱼ · x₁ⱼ)`. -/
@[expose] noncomputable def slotForm {k : ℕ} (a b : Fin (2 ^ k) → ℂ) (x : FFTPair k) : ℝ :=
  ∑ j, (conj (a j) * RealFFTPoly.coord x.1 j + conj (b j) * RealFFTPoly.coord x.2 j).re

/-- The first component `a₂ᵢ + a₂ᵢ₊₁` of the adjoint of `mergeFFT`. -/
@[expose] noncomputable def mergeAdjFst {k : ℕ} (a : Fin (2 ^ (k + 1)) → ℂ) :
    Fin (2 ^ k) → ℂ :=
  fun i => a ⟨2 * i.1, by omega⟩ + a ⟨2 * i.1 + 1, by omega⟩

/-- The second component `conj ωᵢ (a₂ᵢ - a₂ᵢ₊₁)` of the adjoint of `mergeFFT`. -/
@[expose] noncomputable def mergeAdjSnd {k : ℕ} (a : Fin (2 ^ (k + 1)) → ℂ) :
    Fin (2 ^ k) → ℂ :=
  fun i => conj (Complex.exp ((Primitives.splitAngle i : ℝ) * Complex.I)) *
    (a ⟨2 * i.1, by omega⟩ - a ⟨2 * i.1 + 1, by omega⟩)

private theorem sum_re_merge {k : ℕ} (c : Fin (2 ^ (k + 1)) → ℂ) (y : FFTPair k) :
    ∑ J, (conj (c J) * RealFFTPoly.coord (Primitives.mergeFFT y.1 y.2) J).re =
      slotForm (mergeAdjFst c) (mergeAdjSnd c) y := by
  rw [sum_two_pow_succ, slotForm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [(RealFFTPoly.coord_mergeFFT_two _ _ i).1, (RealFFTPoly.coord_mergeFFT_two _ _ i).2,
    ← Complex.add_re]
  congr 1
  simp only [mergeAdjFst, mergeAdjSnd, map_add, map_sub, map_mul, Complex.conj_conj]
  ring

theorem slotForm_mergeFFT_zero {k : ℕ} (a b : Fin (2 ^ (k + 1)) → ℂ) :
    (fun x : FFTPair k => slotForm a b (Primitives.mergeFFT x.1 x.2, 0)) =
      slotForm (mergeAdjFst a) (mergeAdjSnd a) := by
  funext x
  rw [← sum_re_merge, slotForm]
  refine Finset.sum_congr rfl fun J _ => ?_
  rw [RealFFTPoly.coord_zero, mul_zero, add_zero]

theorem slotForm_mergeFFT_adjust {k : ℕ} (a b : Fin (2 ^ (k + 1)) → ℂ)
    (ℓ : RealFFTPoly (k + 1)) :
    (fun y : FFTPair k => slotForm a b (-Primitives.mulFFT ℓ (Primitives.mergeFFT y.1 y.2),
        Primitives.mergeFFT y.1 y.2)) =
      slotForm (mergeAdjFst fun J => b J - conj (RealFFTPoly.coord ℓ J) * a J)
        (mergeAdjSnd fun J => b J - conj (RealFFTPoly.coord ℓ J) * a J) := by
  funext y
  rw [← sum_re_merge, slotForm]
  refine Finset.sum_congr rfl fun J _ => ?_
  rw [RealFFTPoly.coord_neg, RealFFTPoly.coord_mulFFT]
  congr 1
  simp only [map_sub, map_mul, Complex.conj_conj]
  ring

/-- The slot quadratic form `(y‖a‖² + x‖b‖² - 2 Re(conj b · conj z · a)) / (xy - ‖z‖²)` of the
inverse of the Hermitian matrix `[[x, z], [conj z, y]]`. -/
@[expose] noncomputable def slotQ (x y : ℝ) (z a b : ℂ) : ℝ :=
  (y * ‖a‖ ^ 2 + x * ‖b‖ ^ 2 - 2 * (conj b * conj z * a).re) / (x * y - ‖z‖ ^ 2)

/-- `‖w‖² = (Re w)² + (Im w)²`. -/
theorem _root_.Complex.sq_norm_eq_re_sq_add_im_sq (w : ℂ) : ‖w‖ ^ 2 = w.re ^ 2 + w.im ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]; ring

/-- The trace bound: `‖a‖² + ‖b‖² ≤ (x + y) · slotQ`. -/
theorem norm_sq_add_le_slotQ {x y : ℝ} {z : ℂ} (hD : 0 < x * y - ‖z‖ ^ 2) (a b : ℂ) :
    ‖a‖ ^ 2 + ‖b‖ ^ 2 ≤ (x + y) * slotQ x y z a b := by
  rw [slotQ, mul_div_assoc', le_div_iff₀ hD]
  rw [Complex.sq_norm_eq_re_sq_add_im_sq] at hD ⊢
  rw [Complex.sq_norm_eq_re_sq_add_im_sq, Complex.sq_norm_eq_re_sq_add_im_sq]
  simp only [Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im]
  nlinarith [sq_nonneg (y * a.re - (z.re * b.re - z.im * b.im)),
    sq_nonneg (y * a.im - (z.re * b.im + z.im * b.re)),
    sq_nonneg (x * b.re - (z.re * a.re + z.im * a.im)),
    sq_nonneg (x * b.im - (z.re * a.im - z.im * a.re))]

theorem slotQ_nonneg {x y : ℝ} {z : ℂ} (hx : 0 < x) (hD : 0 < x * y - ‖z‖ ^ 2) (a b : ℂ) :
    0 ≤ slotQ x y z a b := by
  have hy : 0 < x + y := by nlinarith [sq_nonneg ‖z‖]
  have h := norm_sq_add_le_slotQ hD a b
  by_contra hneg
  push Not at hneg
  nlinarith [sq_nonneg ‖a‖, sq_nonneg ‖b‖]

/-- **LDL⋆ of one slot**: `slotQ = ‖a‖²/x + ‖b - conj(z/x) a‖²/(y - ‖z‖²/x)`. -/
theorem slotQ_eq_ldl {x y : ℝ} {z : ℂ} (hx : 0 < x) (hD : 0 < x * y - ‖z‖ ^ 2) (a b : ℂ) :
    slotQ x y z a b = ‖a‖ ^ 2 / x + ‖b - conj (z / (x : ℂ)) * a‖ ^ 2 / (y - ‖z‖ ^ 2 / x) := by
  have hd : y - ‖z‖ ^ 2 / x = (x * y - ‖z‖ ^ 2) / x := by field_simp
  rw [hd, slotQ]
  rw [Complex.sq_norm_eq_re_sq_add_im_sq] at hD ⊢
  rw [Complex.sq_norm_eq_re_sq_add_im_sq, Complex.sq_norm_eq_re_sq_add_im_sq,
    Complex.sq_norm_eq_re_sq_add_im_sq]
  have hx' : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  simp only [map_div₀, Complex.conj_ofReal, Complex.sub_re, Complex.sub_im, Complex.mul_re,
    Complex.mul_im, Complex.conj_re, Complex.conj_im, Complex.div_re, Complex.div_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.normSq_ofReal]
  have hD' : x * y - z.re ^ 2 - z.im ^ 2 ≠ 0 := by linarith
  have hE : (x * y - z.re ^ 2 - z.im ^ 2)⁻¹ * (x * y - z.re ^ 2 - z.im ^ 2) = 1 :=
    inv_mul_cancel₀ hD'
  field_simp
  linear_combination (x ^ 2 * (a.re ^ 2 + a.im ^ 2)) * hE

/-- **The split of a diagonal slot pair**: for `x₀, x₁ > 0` and `‖ω‖ = 1`,
`‖e₀‖²/x₀ + ‖e₁‖²/x₁ = slotQ(A, A, conj B; e₀ + e₁, conj ω (e₀ - e₁)) / 2` with
`A = (x₀ + x₁)/2`, `B = conj ω (x₀ - x₁)/2`. -/
theorem slotQ_split {x₀ x₁ : ℝ} (h₀ : 0 < x₀) (h₁ : 0 < x₁) {ω : ℂ} (hω : ‖ω‖ = 1)
    (e₀ e₁ : ℂ) :
    ‖e₀‖ ^ 2 / x₀ + ‖e₁‖ ^ 2 / x₁ = slotQ ((x₀ + x₁) / 2) ((x₀ + x₁) / 2)
      (conj (conj ω * (((x₀ - x₁) / 2 : ℝ) : ℂ))) (e₀ + e₁) (conj ω * (e₀ - e₁)) / 2 := by
  have hω2 : ω.re ^ 2 + ω.im ^ 2 = 1 := by rw [← Complex.sq_norm_eq_re_sq_add_im_sq, hω, one_pow]
  have hB : ‖conj (conj ω * (((x₀ - x₁) / 2 : ℝ) : ℂ))‖ ^ 2 = ((x₀ - x₁) / 2) ^ 2 := by
    rw [Complex.norm_conj, norm_mul, Complex.norm_conj, hω, one_mul, Complex.norm_real,
      Real.norm_eq_abs, sq_abs]
  have hb : ‖conj ω * (e₀ - e₁)‖ ^ 2 = ‖e₀ - e₁‖ ^ 2 := by
    rw [norm_mul, Complex.norm_conj, hω, one_mul]
  have hR : (conj (conj ω * (e₀ - e₁)) * conj (conj (conj ω * (((x₀ - x₁) / 2 : ℝ) : ℂ))) *
      (e₀ + e₁)).re = (x₀ - x₁) / 2 * (‖e₀‖ ^ 2 - ‖e₁‖ ^ 2) := by
    rw [Complex.conj_conj, Complex.sq_norm_eq_re_sq_add_im_sq, Complex.sq_norm_eq_re_sq_add_im_sq]
    simp only [map_mul, map_sub, Complex.conj_conj, Complex.mul_re, Complex.mul_im,
      Complex.conj_re, Complex.conj_im, Complex.sub_re, Complex.sub_im, Complex.add_re,
      Complex.add_im, Complex.ofReal_re, Complex.ofReal_im]
    linear_combination (x₀ - x₁) / 2 * (e₀.re ^ 2 + e₀.im ^ 2 - e₁.re ^ 2 - e₁.im ^ 2) * hω2
  rw [slotQ, hB, hb, hR]
  have hD : (x₀ + x₁) / 2 * ((x₀ + x₁) / 2) - ((x₀ - x₁) / 2) ^ 2 = x₀ * x₁ := by ring
  rw [hD, Complex.sq_norm_eq_re_sq_add_im_sq (e₀ + e₁),
    Complex.sq_norm_eq_re_sq_add_im_sq (e₀ - e₁), Complex.sq_norm_eq_re_sq_add_im_sq e₀,
    Complex.sq_norm_eq_re_sq_add_im_sq e₁]
  simp only [Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im]
  field_simp
  ring

/-- Every slot of `g00` and `g11` is real, `g00` is positive and `‖g10‖² < g00 · g11`: the slots of
a Hermitian positive definite `2 × 2` matrix `[[g00, g10], [conj g10, g11]]`. -/
@[expose] def PosGram {k : ℕ} (g00 g10 g11 : RealFFTPoly k) : Prop :=
  ∀ j, (RealFFTPoly.coord g00 j).im = 0 ∧ (RealFFTPoly.coord g11 j).im = 0 ∧
    0 < (RealFFTPoly.coord g00 j).re ∧
    ‖RealFFTPoly.coord g10 j‖ ^ 2 < (RealFFTPoly.coord g00 j).re * (RealFFTPoly.coord g11 j).re

/-- The quadratic form of the inverse Gram matrix, summed over the slots. -/
@[expose] noncomputable def gramQ {k : ℕ} (g00 g10 g11 : RealFFTPoly k) (a b : Fin (2 ^ k) → ℂ) :
    ℝ :=
  ∑ j, slotQ (RealFFTPoly.coord g00 j).re (RealFFTPoly.coord g11 j).re
    (RealFFTPoly.coord g10 j) (a j) (b j)

theorem gramQ_nonneg {k : ℕ} {g00 g10 g11 : RealFFTPoly k} (h : PosGram g00 g10 g11)
    (a b : Fin (2 ^ k) → ℂ) : 0 ≤ gramQ g00 g10 g11 a b :=
  Finset.sum_nonneg fun j _ => slotQ_nonneg (h j).2.2.1 (by linarith [(h j).2.2.2]) _ _

private theorem ofReal_re_of_im {w : ℂ} (h : w.im = 0) : w = (w.re : ℂ) :=
  Complex.ext (by simp) (by simp [h])

private theorem cos_neg_sin_eq (θ : ℝ) :
    (⟨Real.cos θ, -Real.sin θ⟩ : ℂ) = conj (Complex.exp ((θ : ℂ) * Complex.I)) := by
  apply Complex.ext <;> simp [Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]

private theorem norm_exp_splitAngle {k : ℕ} (i : Fin (2 ^ k)) :
    ‖Complex.exp ((Primitives.splitAngle i : ℝ) * Complex.I)‖ = 1 :=
  Complex.norm_exp_ofReal_mul_I _

private theorem coord_splitFFT_snd' {k : ℕ} (g : RealFFTPoly (k + 1)) (i : Fin (2 ^ k))
    {x₀ x₁ : ℝ} (h₀ : RealFFTPoly.coord g ⟨2 * i.1, by omega⟩ = x₀)
    (h₁ : RealFFTPoly.coord g ⟨2 * i.1 + 1, by omega⟩ = x₁) :
    RealFFTPoly.coord (Primitives.splitFFT g).2 i =
      conj (Complex.exp ((Primitives.splitAngle i : ℝ) * Complex.I)) *
        (((x₀ - x₁) / 2 : ℝ) : ℂ) := by
  rw [RealFFTPoly.coord_splitFFT_snd, h₀, h₁, cos_neg_sin_eq]
  push_cast
  ring

/-- The split of a real positive diagonal is a positive Gram matrix `[[a, conj b], [b, a]]`. -/
theorem posGram_split {k : ℕ} (g : RealFFTPoly (k + 1))
    (hg : ∀ J, (RealFFTPoly.coord g J).im = 0 ∧ 0 < (RealFFTPoly.coord g J).re) :
    PosGram (Primitives.splitFFT g).1 (RealFFTPoly.adjFFT (Primitives.splitFFT g).2)
      (Primitives.splitFFT g).1 := by
  intro i
  set x₀ := (RealFFTPoly.coord g ⟨2 * i.1, by omega⟩).re
  set x₁ := (RealFFTPoly.coord g ⟨2 * i.1 + 1, by omega⟩).re
  have h₀ := ofReal_re_of_im (hg ⟨2 * i.1, by omega⟩).1
  have h₁ := ofReal_re_of_im (hg ⟨2 * i.1 + 1, by omega⟩).1
  have hx₀ : 0 < x₀ := (hg _).2
  have hx₁ : 0 < x₁ := (hg _).2
  have hfst : RealFFTPoly.coord (Primitives.splitFFT g).1 i = (((x₀ + x₁) / 2 : ℝ) : ℂ) := by
    rw [RealFFTPoly.coord_splitFFT_fst, h₀, h₁]; push_cast; ring
  rw [hfst, RealFFTPoly.coord_adjFFT, coord_splitFFT_snd' g i h₀ h₁, Complex.norm_conj,
    norm_mul, Complex.norm_conj, norm_exp_splitAngle, one_mul, Complex.norm_real,
    Real.norm_eq_abs, sq_abs, Complex.ofReal_re, Complex.ofReal_im]
  refine ⟨rfl, rfl, by positivity, by nlinarith⟩

/-- **The diagonal split**: `Σⱼ ‖eⱼ‖²/gⱼ` over `2^(k+1)` real positive slots is half the
quadratic form of the split Gram matrix at the adjoint of `mergeFFT`. -/
theorem sum_div_eq_gramQ_split {k : ℕ} (g : RealFFTPoly (k + 1))
    (hg : ∀ J, (RealFFTPoly.coord g J).im = 0 ∧ 0 < (RealFFTPoly.coord g J).re)
    (e : Fin (2 ^ (k + 1)) → ℂ) :
    ∑ J, ‖e J‖ ^ 2 / (RealFFTPoly.coord g J).re = gramQ (Primitives.splitFFT g).1
      (RealFFTPoly.adjFFT (Primitives.splitFFT g).2) (Primitives.splitFFT g).1
        (mergeAdjFst e) (mergeAdjSnd e) / 2 := by
  rw [sum_two_pow_succ, gramQ, Finset.sum_div]
  refine Finset.sum_congr rfl fun i _ => ?_
  set x₀ := (RealFFTPoly.coord g ⟨2 * i.1, by omega⟩).re
  set x₁ := (RealFFTPoly.coord g ⟨2 * i.1 + 1, by omega⟩).re
  have h₀ := ofReal_re_of_im (hg ⟨2 * i.1, by omega⟩).1
  have h₁ := ofReal_re_of_im (hg ⟨2 * i.1 + 1, by omega⟩).1
  have hfst : RealFFTPoly.coord (Primitives.splitFFT g).1 i = (((x₀ + x₁) / 2 : ℝ) : ℂ) := by
    rw [RealFFTPoly.coord_splitFFT_fst, h₀, h₁]; push_cast; ring
  rw [hfst, RealFFTPoly.coord_adjFFT, coord_splitFFT_snd' g i h₀ h₁, Complex.ofReal_re,
    slotQ_split (hg _).2 (hg _).2 (norm_exp_splitAngle i)]
  rfl

/-- The `D11` diagonal `g11 - g10 · conj g10 / g00` of a positive Gram matrix is real and
positive. -/
theorem coord_d11 {k : ℕ} {g00 g10 g11 : RealFFTPoly k} (h : PosGram g00 g10 g11)
    (J : Fin (2 ^ k)) :
    RealFFTPoly.coord (g11 - Primitives.mulFFT g10
        (RealFFTPoly.divFFT (RealFFTPoly.adjFFT g10) g00)) J =
      (((RealFFTPoly.coord g11 J).re - ‖RealFFTPoly.coord g10 J‖ ^ 2 /
        (RealFFTPoly.coord g00 J).re : ℝ) : ℂ) := by
  obtain ⟨h00, h11, hx, -⟩ := h J
  set x := (RealFFTPoly.coord g00 J).re
  set y := (RealFFTPoly.coord g11 J).re
  have e00 := ofReal_re_of_im h00
  have e11 := ofReal_re_of_im h11
  rw [RealFFTPoly.coord_sub, RealFFTPoly.coord_mulFFT, RealFFTPoly.coord_divFFT,
    RealFFTPoly.coord_adjFFT, e00, e11, mul_div_assoc', Complex.mul_conj,
    Complex.normSq_eq_norm_sq]
  push_cast
  ring

theorem d11_pos {k : ℕ} {g00 g10 g11 : RealFFTPoly k} (h : PosGram g00 g10 g11)
    (J : Fin (2 ^ k)) : 0 < (RealFFTPoly.coord g11 J).re - ‖RealFFTPoly.coord g10 J‖ ^ 2 /
      (RealFFTPoly.coord g00 J).re := by
  obtain ⟨-, -, hx, hD⟩ := h J
  rw [sub_pos, div_lt_iff₀ hx]
  linarith

/-- **One level of ffLDL⋆ on the quadratic form**: the parent form is half the sum of the forms
of the two children at the adjoints of `mergeFFT`. -/
theorem gramQ_node {k : ℕ} {g00 g10 g11 : RealFFTPoly (k + 1)} (h : PosGram g00 g10 g11)
    (a b : Fin (2 ^ (k + 1)) → ℂ) :
    gramQ g00 g10 g11 a b =
      (gramQ (Primitives.splitFFT g00).1 (RealFFTPoly.adjFFT (Primitives.splitFFT g00).2)
          (Primitives.splitFFT g00).1 (mergeAdjFst a) (mergeAdjSnd a) +
        gramQ (Primitives.splitFFT (g11 - Primitives.mulFFT g10
            (RealFFTPoly.divFFT (RealFFTPoly.adjFFT g10) g00))).1
          (RealFFTPoly.adjFFT (Primitives.splitFFT (g11 - Primitives.mulFFT g10
            (RealFFTPoly.divFFT (RealFFTPoly.adjFFT g10) g00))).2)
          (Primitives.splitFFT (g11 - Primitives.mulFFT g10
            (RealFFTPoly.divFFT (RealFFTPoly.adjFFT g10) g00))).1
          (mergeAdjFst fun J => b J - conj (RealFFTPoly.coord
            (RealFFTPoly.divFFT g10 g00) J) * a J)
          (mergeAdjSnd fun J => b J - conj (RealFFTPoly.coord
            (RealFFTPoly.divFFT g10 g00) J) * a J)) / 2 := by
  have hg0 : ∀ J, (RealFFTPoly.coord g00 J).im = 0 ∧ 0 < (RealFFTPoly.coord g00 J).re :=
    fun J => ⟨(h J).1, (h J).2.2.1⟩
  have hd : ∀ J, (RealFFTPoly.coord (g11 - Primitives.mulFFT g10
      (RealFFTPoly.divFFT (RealFFTPoly.adjFFT g10) g00)) J).im = 0 ∧
      0 < (RealFFTPoly.coord (g11 - Primitives.mulFFT g10
        (RealFFTPoly.divFFT (RealFFTPoly.adjFFT g10) g00)) J).re := fun J => by
    rw [coord_d11 h J, Complex.ofReal_im, Complex.ofReal_re]
    exact ⟨rfl, d11_pos h J⟩
  rw [add_div, ← sum_div_eq_gramQ_split _ hg0, ← sum_div_eq_gramQ_split _ hd, gramQ,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun J _ => ?_
  obtain ⟨h00, -, hx, hD⟩ := h J
  have e := ofReal_re_of_im h00
  rw [slotQ_eq_ldl hx (by linarith) (a J) (b J), coord_d11 h J, Complex.ofReal_re,
    RealFFTPoly.coord_divFFT, ← e]

/-- The leaf of `devVar` on a slot form: `σ² (‖a₀‖² + ‖b₀‖²)`. -/
theorem devVar_leaf_slotForm (σ : ℝ) (a b : Fin (2 ^ 0) → ℂ) :
    (FalconTree.leaf σ).devVar (slotForm a b) =
      σ ^ 2 * (‖a ⟨0, by norm_num⟩‖ ^ 2 + ‖b ⟨0, by norm_num⟩‖ ^ 2) := by
  have hs : ∀ x : FFTPair 0, slotForm a b x = (conj (a ⟨0, by norm_num⟩) *
      RealFFTPoly.coord x.1 ⟨0, by norm_num⟩ + conj (b ⟨0, by norm_num⟩) *
        RealFFTPoly.coord x.2 ⟨0, by norm_num⟩).re := fun x => by
    rw [slotForm, Fintype.sum_eq_single ⟨0, by norm_num⟩ fun j hj => absurd (slot_zero j) hj]
  have hw : ∀ c d e f : ℝ, slotForm a b (leafPair c d e f) =
      c * (a ⟨0, by norm_num⟩).re + d * (a ⟨0, by norm_num⟩).im +
        e * (b ⟨0, by norm_num⟩).re + f * (b ⟨0, by norm_num⟩).im := fun c d e f => by
    rw [hs]
    simp only [leafPair, RealFFTPoly.coord_pack, Vector.get_ofFn, Complex.add_re,
      Complex.mul_re, Complex.conj_re, Complex.conj_im]
    ring
  rw [FalconTree.devVar, hw, hw, hw, hw, Complex.sq_norm_eq_re_sq_add_im_sq,
    Complex.sq_norm_eq_re_sq_add_im_sq]
  ring

/-- **Variance proxies of ffLDL⋆ trees**: for a positive Gram matrix, the variance proxy of a slot
form under its ffLDL⋆ tree is at most `ρ σ² 2^κ` times the quadratic form of the inverse Gram
matrix, with `ρ` the leaf ratio. -/
theorem devVar_ffLDL_le (σ : ℝ) : ∀ (κ : ℕ) (g00 g10 g11 : RealFFTPoly κ),
    PosGram g00 g10 g11 → ∀ a b : Fin (2 ^ κ) → ℂ,
      (ffLDL σ κ g00 g10 g11).devVar (slotForm a b) ≤
        ffLDLLeafRatio κ g00 g10 g11 * σ ^ 2 * 2 ^ κ * gramQ g00 g10 g11 a b
  | 0, g00, g10, g11, h, a, b => by
    obtain ⟨-, -, hx, hD⟩ := h ⟨0, by norm_num⟩
    have hsum : gramQ g00 g10 g11 a b = slotQ (RealFFTPoly.coord g00 ⟨0, by norm_num⟩).re
        (RealFFTPoly.coord g11 ⟨0, by norm_num⟩).re (RealFFTPoly.coord g10 ⟨0, by norm_num⟩)
        (a ⟨0, by norm_num⟩) (b ⟨0, by norm_num⟩) := by
      rw [gramQ, Fintype.sum_eq_single ⟨0, by norm_num⟩ fun j hj => absurd (slot_zero j) hj]
    have htr := norm_sq_add_le_slotQ (by linarith) (a ⟨0, by norm_num⟩) (b ⟨0, by norm_num⟩)
      (x := (RealFFTPoly.coord g00 ⟨0, by norm_num⟩).re)
      (y := (RealFFTPoly.coord g11 ⟨0, by norm_num⟩).re)
      (z := RealFFTPoly.coord g10 ⟨0, by norm_num⟩)
    rw [ffLDL, devVar_leaf_slotForm, ffLDLLeafRatio, hsum, div_pow,
      show (2 : ℝ) ^ 0 = 1 from pow_zero 2, mul_one]
    simp only [RealFFTPoly.coord_re] at htr hx ⊢
    rw [Real.sq_sqrt hx.le]
    calc σ ^ 2 / _ * (‖a ⟨0, by norm_num⟩‖ ^ 2 + ‖b ⟨0, by norm_num⟩‖ ^ 2) ≤
        σ ^ 2 / _ * ((_ + _) * slotQ _ _ _ _ _) := by gcongr
      _ = _ := by ring
  | k + 1, g00, g10, g11, h, a, b => by
    have hg0 : ∀ J, (RealFFTPoly.coord g00 J).im = 0 ∧ 0 < (RealFFTPoly.coord g00 J).re :=
      fun J => ⟨(h J).1, (h J).2.2.1⟩
    have hd : ∀ J, (RealFFTPoly.coord (g11 - Primitives.mulFFT g10
        (RealFFTPoly.divFFT (RealFFTPoly.adjFFT g10) g00)) J).im = 0 ∧
        0 < (RealFFTPoly.coord (g11 - Primitives.mulFFT g10
          (RealFFTPoly.divFFT (RealFFTPoly.adjFFT g10) g00)) J).re := fun J => by
      rw [coord_d11 h J, Complex.ofReal_im, Complex.ofReal_re]
      exact ⟨rfl, d11_pos h J⟩
    have hL := posGram_split g00 hg0
    have hR := posGram_split _ hd
    rw [ffLDL, FalconTree.devVar, slotForm_mergeFFT_zero, slotForm_mergeFFT_adjust,
      ffLDLLeafRatio, gramQ_node h]
    have ihL := devVar_ffLDL_le σ k _ _ _ hL (mergeAdjFst a) (mergeAdjSnd a)
    have ihR := devVar_ffLDL_le σ k _ _ _ hR
      (mergeAdjFst fun J => b J - conj (RealFFTPoly.coord (RealFFTPoly.divFFT g10 g00) J) * a J)
      (mergeAdjSnd fun J => b J - conj (RealFFTPoly.coord (RealFFTPoly.divFFT g10 g00) J) * a J)
    have hQL := gramQ_nonneg hL (mergeAdjFst a) (mergeAdjSnd a)
    have hQR := gramQ_nonneg hR
      (mergeAdjFst fun J => b J - conj (RealFFTPoly.coord (RealFFTPoly.divFFT g10 g00) J) * a J)
      (mergeAdjSnd fun J => b J - conj (RealFFTPoly.coord (RealFFTPoly.divFFT g10 g00) J) * a J)
    refine (add_le_add ihL ihR).trans ?_
    have hc : 0 ≤ σ ^ 2 * 2 ^ k := by positivity
    calc _ ≤ max (ffLDLLeafRatio k _ _ _) (ffLDLLeafRatio k _ _ _) * σ ^ 2 * 2 ^ k *
          gramQ _ _ _ (mergeAdjFst a) (mergeAdjSnd a) +
        max (ffLDLLeafRatio k _ _ _) (ffLDLLeafRatio k _ _ _) * σ ^ 2 * 2 ^ k *
          gramQ _ _ _ _ _ := by
          gcongr
          · exact le_max_left _ _
          · exact le_max_right _ _
      _ = _ := by ring

theorem ffLDLLeafRatio_nonneg : ∀ (κ : ℕ) (g00 g10 g11 : RealFFTPoly κ),
    PosGram g00 g10 g11 → 0 ≤ ffLDLLeafRatio κ g00 g10 g11
  | 0, g00, g10, g11, h => by
    obtain ⟨-, -, hx, hD⟩ := h ⟨0, by norm_num⟩
    simp only [RealFFTPoly.coord_re] at hx hD
    rw [ffLDLLeafRatio]
    have hy : 0 < RealFFTPoly.re g11 ⟨0, by norm_num⟩ := by
      by_contra hy
      push Not at hy
      nlinarith [sq_nonneg ‖RealFFTPoly.coord g10 ⟨0, by norm_num⟩‖]
    positivity
  | k + 1, g00, g10, g11, h => by
    rw [ffLDLLeafRatio]
    exact le_max_of_le_left (ffLDLLeafRatio_nonneg k _ _ _
      (posGram_split g00 fun J => ⟨(h J).1, (h J).2.2.1⟩))

/-- Coefficient `m` of a packed FFT polynomial is a slot form whose weights all have squared norm
`1/4^k`. -/
theorem toCoeffs_eq_slotSum : ∀ (k : ℕ) (m : Fin (2 * 2 ^ k)), ∃ α : Fin (2 ^ k) → ℂ,
    (∀ j, ‖α j‖ ^ 2 = 1 / 4 ^ k) ∧ ∀ v : RealFFTPoly k,
      RealFFTPoly.toCoeffs k v m = ∑ j, (conj (α j) * RealFFTPoly.coord v j).re
  | 0, m => by
    refine ⟨fun _ => if m.1 = 0 then 1 else Complex.I, fun j => by split_ifs <;> simp,
      fun v => ?_⟩
    rw [Fintype.sum_eq_single ⟨0, by norm_num⟩ fun j hj => absurd (slot_zero j) hj]
    obtain ⟨m, hm⟩ := m
    rcases (show m = 0 ∨ m = 1 by simp at hm; omega) with rfl | rfl <;>
      simp [RealFFTPoly.toCoeffs, RealFFTPoly.coord, RealFFTPoly.re, RealFFTPoly.im,
        RealFFTPoly.get_eq_getElem]
  | k + 1, m => by
    have h2 := RealFFTPoly.two_pow_succ_eq k
    obtain ⟨β, hβ, hrep⟩ := toCoeffs_eq_slotSum k ⟨m.1 / 2, by have := m.2; omega⟩
    have hh₀ : ∀ (i : Fin (2 ^ k)) (h : 2 * i.1 / 2 < 2 ^ k),
        (⟨2 * i.1 / 2, h⟩ : Fin (2 ^ k)) = i := fun i _ => Fin.ext (by simp)
    have hh₁ : ∀ (i : Fin (2 ^ k)) (h : (2 * i.1 + 1) / 2 < 2 ^ k),
        (⟨(2 * i.1 + 1) / 2, h⟩ : Fin (2 ^ k)) = i := fun i _ => Fin.ext (by simp; omega)
    by_cases hm : m.1 % 2 = 0
    · refine ⟨fun J => β ⟨J.1 / 2, by have := J.2; omega⟩ / 2, fun J => ?_, fun v => ?_⟩
      · rw [norm_div, div_pow, hβ, Complex.norm_ofNat, pow_succ]; ring
      · simp only [RealFFTPoly.toCoeffs, hm, ite_true]
        rw [hrep, sum_two_pow_succ]
        refine Finset.sum_congr rfl fun i _ => ?_
        simp only [hh₀, hh₁]
        rw [RealFFTPoly.coord_splitFFT_fst, ← Complex.add_re]
        congr 1
        simp only [map_div₀, Complex.conj_ofNat]
        ring
    · refine ⟨fun J => if J.1 % 2 = 0 then β ⟨J.1 / 2, by have := J.2; omega⟩ *
          Complex.exp ((Primitives.splitAngle (⟨J.1 / 2, by have := J.2; omega⟩ :
            Fin (2 ^ k)) : ℝ) * Complex.I) / 2
        else -(β ⟨J.1 / 2, by have := J.2; omega⟩ *
          Complex.exp ((Primitives.splitAngle (⟨J.1 / 2, by have := J.2; omega⟩ :
            Fin (2 ^ k)) : ℝ) * Complex.I)) / 2,
        fun J => ?_, fun v => ?_⟩
      · dsimp only
        split_ifs <;>
        · rw [norm_div, div_pow, Complex.norm_ofNat]
          try rw [norm_neg]
          rw [norm_mul, mul_pow, hβ, Complex.norm_exp_ofReal_mul_I, pow_succ]; ring
      · simp only [RealFFTPoly.toCoeffs, hm, ite_false]
        rw [hrep, sum_two_pow_succ]
        refine Finset.sum_congr rfl fun i _ => ?_
        have hev : (2 * i.1) % 2 = 0 := by omega
        have hod : ¬ (2 * i.1 + 1) % 2 = 0 := by omega
        simp only [hev, hod, ite_true, ite_false, hh₀, hh₁]
        rw [RealFFTPoly.coord_splitFFT_snd, cos_neg_sin_eq, ← Complex.add_re]
        congr 1
        simp only [map_div₀, map_mul, map_neg, Complex.conj_ofNat]
        ring

/-- The packed FFT turns the NTRU equation into `f̂ Ĝ - ĝ F̂ = q` at every slot. -/
theorem ntru_coord (hn : 2 * 2 ^ p.fftDepth = p.n) (sk : SecretKey p)
    (hntru : ntruEquation p sk.f sk.g sk.capF sk.capG) (j : Fin (2 ^ p.fftDepth)) :
    RealFFTPoly.coord (Primitives.exactFftInt p sk.f) j *
        RealFFTPoly.coord (Primitives.exactFftInt p sk.capG) j -
      RealFFTPoly.coord (Primitives.exactFftInt p sk.g) j *
        RealFFTPoly.coord (Primitives.exactFftInt p sk.capF) j = ((modulus : ℕ) : ℂ) := by
  have hprod : ∀ u v : IntPoly p.n,
      RealFFTPoly.coord (Primitives.exactFftInt p u) j *
          RealFFTPoly.coord (Primitives.exactFftInt p v) j =
        evalAngle (fun m => (((intPolyMul u v).get (Fin.cast hn m) : ℤ) : ℝ))
          (rootAngle p.fftDepth j.1) := fun u v => by
    rw [Primitives.exactFftInt_eq p hn, Primitives.exactFftInt_eq p hn,
      ← RealFFTPoly.coord_mulFFT, ← RealFFTPoly.ofCoeffs_negacyclic, RealFFTPoly.coord_ofCoeffs]
    congr 1
    funext m
    rw [negacyclicConvCoeff_cast hn (fun i => ((u.get i : ℤ) : ℝ)) (fun i => ((v.get i : ℤ) : ℝ)),
      ← intCast_negacyclicConvCoeff, IntPoly.get_mul]
  rw [hprod, hprod, sub_eq_add_neg, ← evalAngle_neg, ← evalAngle_add]
  have hfun : (fun m : Fin (2 * 2 ^ p.fftDepth) =>
      (((intPolyMul sk.f sk.capG).get (Fin.cast hn m) : ℤ) : ℝ) +
        -(((intPolyMul sk.g sk.capF).get (Fin.cast hn m) : ℤ) : ℝ)) =
      fun m => if m.1 = 0 then ((modulus : ℕ) : ℝ) else 0 := by
    funext m
    have h := congrArg (fun P : IntPoly p.n => ((P.get (Fin.cast hn m) : ℤ) : ℝ)) hntru
    simp only [Poly.get_sub, Int.cast_sub] at h
    rw [← sub_eq_add_neg, h]
    simp [intPolyConst, integralLift, vectorIntegralLift, constPoly]
  rw [hfun, evalAngle,
    Fintype.sum_eq_single ⟨0, by positivity⟩ fun m hm => by
      rw [ite_eq_right_iff.2 (fun h => absurd (Fin.ext h) hm), Complex.ofReal_zero, zero_mul]]
  simp

private theorem lagrange (f g F G : ℂ) :
    (‖g‖ ^ 2 + ‖f‖ ^ 2) * (‖G‖ ^ 2 + ‖F‖ ^ 2) - ‖G * conj g + F * conj f‖ ^ 2 =
      ‖f * G - g * F‖ ^ 2 := by
  simp only [Complex.sq_norm_eq_re_sq_add_im_sq, Complex.add_re, Complex.add_im, Complex.sub_re,
    Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im]
  ring

/-- Slot `j` of `u u⋆ + v v⋆` is `‖u_j‖² + ‖v_j‖²`. -/
theorem RealFFTPoly.coord_mulFFT_adjFFT_add {κ' : ℕ} (u v : RealFFTPoly κ') (j : Fin (2 ^ κ')) :
    RealFFTPoly.coord (Primitives.mulFFT u (RealFFTPoly.adjFFT u) +
        Primitives.mulFFT v (RealFFTPoly.adjFFT v)) j =
      ((‖RealFFTPoly.coord u j‖ ^ 2 + ‖RealFFTPoly.coord v j‖ ^ 2 : ℝ) : ℂ) := by
  rw [RealFFTPoly.coord_add, RealFFTPoly.coord_mulFFT, RealFFTPoly.coord_mulFFT,
    RealFFTPoly.coord_adjFFT, RealFFTPoly.coord_adjFFT, Complex.mul_conj, Complex.mul_conj,
    Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq]
  push_cast
  ring

/-- **The Gram matrix of an NTRU basis is positive**: every slot has determinant `q²`
(`ntru_coord`). -/
theorem posGram_gramFFT (hn : 2 * 2 ^ p.fftDepth = p.n) (sk : SecretKey p)
    (hntru : ntruEquation p sk.f sk.g sk.capF sk.capG) :
    PosGram (gramFFT p sk).1 (gramFFT p sk).2.1 (gramFFT p sk).2.2 := by
  set g := Primitives.exactFftInt p sk.g
  set f := Primitives.exactFftInt p sk.f
  set G := Primitives.exactFftInt p sk.capG
  set F := Primitives.exactFftInt p sk.capF
  set q : ℝ := ((modulus : ℕ) : ℝ)
  have hq : 0 < q := by simp only [q]; norm_num [modulus]
  have hgram : gramFFT p sk =
      (Primitives.mulFFT g (RealFFTPoly.adjFFT g) + Primitives.mulFFT f (RealFFTPoly.adjFFT f),
        Primitives.mulFFT G (RealFFTPoly.adjFFT g) + Primitives.mulFFT F (RealFFTPoly.adjFFT f),
        Primitives.mulFFT G (RealFFTPoly.adjFFT G) + Primitives.mulFFT F (RealFFTPoly.adjFFT F)) :=
    rfl
  intro j
  set x : ℝ := ‖RealFFTPoly.coord g j‖ ^ 2 + ‖RealFFTPoly.coord f j‖ ^ 2
  set y : ℝ := ‖RealFFTPoly.coord G j‖ ^ 2 + ‖RealFFTPoly.coord F j‖ ^ 2
  have h00 : RealFFTPoly.coord (gramFFT p sk).1 j = (x : ℂ) := by
    rw [hgram]; exact RealFFTPoly.coord_mulFFT_adjFFT_add g f j
  have h11 : RealFFTPoly.coord (gramFFT p sk).2.2 j = (y : ℂ) := by
    rw [hgram]; exact RealFFTPoly.coord_mulFFT_adjFFT_add G F j
  have h10 : RealFFTPoly.coord (gramFFT p sk).2.1 j =
      RealFFTPoly.coord G j * conj (RealFFTPoly.coord g j) +
        RealFFTPoly.coord F j * conj (RealFFTPoly.coord f j) := by
    rw [hgram, RealFFTPoly.coord_add, RealFFTPoly.coord_mulFFT, RealFFTPoly.coord_mulFFT,
      RealFFTPoly.coord_adjFFT, RealFFTPoly.coord_adjFFT]
  have hD : x * y - ‖RealFFTPoly.coord (gramFFT p sk).2.1 j‖ ^ 2 = q ^ 2 := by
    rw [h10, lagrange, ntru_coord hn sk hntru j, Complex.norm_natCast]
  rw [h00, h11, Complex.ofReal_im, Complex.ofReal_im, Complex.ofReal_re, Complex.ofReal_re]
  have hx0 : 0 ≤ x := by positivity
  have hy0 : 0 ≤ y := by positivity
  have hq2 : 0 < q ^ 2 := by positivity
  refine ⟨rfl, rfl, ?_, by nlinarith⟩
  rcases hx0.lt_or_eq with h | h
  · exact h
  · rw [← h] at hD; nlinarith [sq_nonneg ‖RealFFTPoly.coord (gramFFT p sk).2.1 j‖]

/-- **Variance proxies under the true tree.** For a key satisfying the NTRU equation whose tree is
the true tree, coefficient `i` of the first polynomial of `t - z` has variance proxy at most
`ρ σ² (‖F‖² + ‖G‖²) / q²` and of the second at most `ρ σ² (‖f‖² + ‖g‖²) / q²`, with `ρ` the leaf
ratio of the true tree. -/
theorem devVar_trueTree_le (hn : 2 * 2 ^ p.fftDepth = p.n) (sk : SecretKey p)
    (hntru : ntruEquation p sk.f sk.g sk.capF sk.capG) (htree : sk.tree = trueTree p sk)
    (i : Fin (2 * 2 ^ p.fftDepth)) :
    sk.tree.devVar (coeffFst i) ≤ trueTreeLeafRatio p sk * p.sigma ^ 2 *
        (∑ j, ((sk.capF.get j : ℝ) ^ 2 + (sk.capG.get j : ℝ) ^ 2)) / (modulus : ℝ) ^ 2 ∧
      sk.tree.devVar (coeffSnd i) ≤ trueTreeLeafRatio p sk * p.sigma ^ 2 *
        (∑ j, ((sk.f.get j : ℝ) ^ 2 + (sk.g.get j : ℝ) ^ 2)) / (modulus : ℝ) ^ 2 := by
  set g := Primitives.exactFftInt p sk.g
  set f := Primitives.exactFftInt p sk.f
  set G := Primitives.exactFftInt p sk.capG
  set F := Primitives.exactFftInt p sk.capF
  set q : ℝ := ((modulus : ℕ) : ℝ)
  have hgram : gramFFT p sk =
      (Primitives.mulFFT g (RealFFTPoly.adjFFT g) + Primitives.mulFFT f (RealFFTPoly.adjFFT f),
        Primitives.mulFFT G (RealFFTPoly.adjFFT g) + Primitives.mulFFT F (RealFFTPoly.adjFFT f),
        Primitives.mulFFT G (RealFFTPoly.adjFFT G) + Primitives.mulFFT F (RealFFTPoly.adjFFT F)) :=
    rfl
  set x : Fin (2 ^ p.fftDepth) → ℝ := fun j =>
    ‖RealFFTPoly.coord g j‖ ^ 2 + ‖RealFFTPoly.coord f j‖ ^ 2
  set y : Fin (2 ^ p.fftDepth) → ℝ := fun j =>
    ‖RealFFTPoly.coord G j‖ ^ 2 + ‖RealFFTPoly.coord F j‖ ^ 2
  have h00 : ∀ j, RealFFTPoly.coord (gramFFT p sk).1 j = (x j : ℂ) := fun j => by
    rw [hgram]; exact RealFFTPoly.coord_mulFFT_adjFFT_add g f j
  have h11 : ∀ j, RealFFTPoly.coord (gramFFT p sk).2.2 j = (y j : ℂ) := fun j => by
    rw [hgram]; exact RealFFTPoly.coord_mulFFT_adjFFT_add G F j
  have h10 : ∀ j, RealFFTPoly.coord (gramFFT p sk).2.1 j =
      RealFFTPoly.coord G j * conj (RealFFTPoly.coord g j) +
        RealFFTPoly.coord F j * conj (RealFFTPoly.coord f j) := fun j => by
    rw [hgram, RealFFTPoly.coord_add, RealFFTPoly.coord_mulFFT, RealFFTPoly.coord_mulFFT,
      RealFFTPoly.coord_adjFFT, RealFFTPoly.coord_adjFFT]
  have hD : ∀ j, x j * y j - ‖RealFFTPoly.coord (gramFFT p sk).2.1 j‖ ^ 2 = q ^ 2 := fun j => by
    rw [h10, lagrange, ntru_coord hn sk hntru j, Complex.norm_natCast]
  have hpos := posGram_gramFFT hn sk hntru
  have hρ := ffLDLLeafRatio_nonneg p.fftDepth _ _ _ hpos
  have hpars : ∀ u : IntPoly p.n, ∑ j, ‖RealFFTPoly.coord (Primitives.exactFftInt p u) j‖ ^ 2 ≤
      2 ^ p.fftDepth * ∑ j, (u.get j : ℝ) ^ 2 := fun u => by
    rw [Primitives.exactFftInt_eq p hn, FFTStages.sum_norm_coord_ofCoeffs_sq]
    refine le_of_eq (congrArg _ ?_)
    exact Fintype.sum_equiv (finCongr hn) _ _ fun _ => rfl
  obtain ⟨α, hα, hrep⟩ := toCoeffs_eq_slotSum p.fftDepth i
  have hφ₁ : coeffFst i = slotForm α 0 := funext fun v => by
    rw [coeffFst, hrep, slotForm]
    simp
  have hφ₂ : coeffSnd i = slotForm 0 α := funext fun v => by
    rw [coeffSnd, hrep, slotForm]
    simp
  have hQ₁ : gramQ (gramFFT p sk).1 (gramFFT p sk).2.1 (gramFFT p sk).2.2 α 0 =
      1 / 4 ^ p.fftDepth * (∑ j, y j) / q ^ 2 := by
    rw [gramQ, Finset.mul_sum, Finset.sum_div]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [slotQ, h00, h11, Complex.ofReal_re, Complex.ofReal_re, hD, hα]
    simp
    ring
  have hQ₂ : gramQ (gramFFT p sk).1 (gramFFT p sk).2.1 (gramFFT p sk).2.2 0 α =
      1 / 4 ^ p.fftDepth * (∑ j, x j) / q ^ 2 := by
    rw [gramQ, Finset.mul_sum, Finset.sum_div]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [slotQ, h00, h11, Complex.ofReal_re, Complex.ofReal_re, hD, hα]
    simp
    ring
  have hsy : ∑ j, y j ≤
      2 ^ p.fftDepth * ∑ j, ((sk.capF.get j : ℝ) ^ 2 + (sk.capG.get j : ℝ) ^ 2) := by
    simp only [y, Finset.sum_add_distrib, mul_add]
    rw [add_comm (2 ^ p.fftDepth * _)]
    exact add_le_add (hpars sk.capG) (hpars sk.capF)
  have hsx : ∑ j, x j ≤ 2 ^ p.fftDepth * ∑ j, ((sk.f.get j : ℝ) ^ 2 + (sk.g.get j : ℝ) ^ 2) := by
    simp only [x, Finset.sum_add_distrib, mul_add]
    rw [add_comm (2 ^ p.fftDepth * _)]
    exact add_le_add (hpars sk.g) (hpars sk.f)
  have h4 : (4 : ℝ) ^ p.fftDepth = 2 ^ p.fftDepth * 2 ^ p.fftDepth := by rw [← mul_pow]; norm_num
  rw [htree, hφ₁, hφ₂]
  unfold trueTreeLeafRatio trueTree
  set ρ := ffLDLLeafRatio p.fftDepth (gramFFT p sk).1 (gramFFT p sk).2.1 (gramFFT p sk).2.2
  have hfin : ∀ s S : ℝ, s ≤ 2 ^ p.fftDepth * S →
      ρ * p.sigma ^ 2 * 2 ^ p.fftDepth * (1 / 4 ^ p.fftDepth * s / q ^ 2) ≤
        ρ * p.sigma ^ 2 * S / q ^ 2 := by
    intro s S hs
    have e : ρ * p.sigma ^ 2 * 2 ^ p.fftDepth * (1 / 4 ^ p.fftDepth * s / q ^ 2) =
        ρ * p.sigma ^ 2 * (s / 2 ^ p.fftDepth) / q ^ 2 := by
      rw [h4]; field_simp
    have hs' : s / 2 ^ p.fftDepth ≤ S := by rw [div_le_iff₀ (by positivity)]; linarith
    rw [e]
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hs' (mul_nonneg hρ (sq_nonneg _)))
      (sq_nonneg q)
  exact ⟨(devVar_ffLDL_le p.sigma _ _ _ _ hpos α 0).trans (by rw [hQ₁]; exact hfin _ _ hsy),
    (devVar_ffLDL_le p.sigma _ _ _ _ hpos 0 α).trans (by rw [hQ₂]; exact hfin _ _ hsx)⟩

/-! ## Falcon-512 -/

/-- The bound `n · 12288 · 127 / q` on the target coefficients at Falcon-512. -/
@[expose] noncomputable def falcon512TailT : ℝ := 512 * 12288 * 127 / 12289

/-- The variance proxy `2 σ² · n (127² + 127²) / q²` at Falcon-512: leaf ratio `2`, keys with
coefficients in `[-127, 127]`. -/
@[expose] noncomputable def falcon512TailV : ℝ :=
  2 * falcon512.sigma ^ 2 * (512 * (127 ^ 2 + 127 ^ 2)) / 12289 ^ 2

private theorem sum_sq_le_of_abs_le {n : ℕ} (a b : Fin n → ℤ) (ha : ∀ j, |a j| ≤ 127)
    (hb : ∀ j, |b j| ≤ 127) : ∑ j, ((a j : ℝ) ^ 2 + (b j : ℝ) ^ 2) ≤ n * (127 ^ 2 + 127 ^ 2) := by
  have h : ∀ x : ℤ, |x| ≤ 127 → (x : ℝ) ^ 2 ≤ 127 ^ 2 := fun x hx => by
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) (by exact_mod_cast hx) 2
  calc _ ≤ ∑ _j : Fin n, ((127 : ℝ) ^ 2 + 127 ^ 2) :=
        Finset.sum_le_sum fun j _ => add_le_add (h _ (ha j)) (h _ (hb j))
    _ = _ := by simp; ring

/-- **The preimage tail at Falcon-512 under the true tree**, generic in `Z ≥ T`: for a key
satisfying the NTRU equation, with coefficients in `[-127, 127]`, whose tree is the true tree with
leaves in `[σmin, σmax]`, and the exact FFT fields,
`preimageTailMass ≤ 1024 · 2 (1 + 2⁻³⁶)^1024 · exp(-(Z - T)² / (2V))` with
`T = falcon512TailT ≈ 65018.71` and `V = falcon512TailV ≈ 6008.2`. -/
theorem preimageTailMass_falcon512_le (prims : Primitives falcon512)
    (hfft : prims.fftInt = Primitives.exactFftInt falcon512)
    (htgt : prims.fftTarget = Primitives.exactFftTarget falcon512) (sk : SecretKey falcon512)
    (hntru : ntruEquation falcon512 sk.f sk.g sk.capF sk.capG)
    (htree : sk.tree = trueTree falcon512 sk)
    (hkey : ∀ i, |sk.f.get i| ≤ 127 ∧ |sk.g.get i| ≤ 127 ∧ |sk.capF.get i| ≤ 127 ∧
      |sk.capG.get i| ≤ 127)
    (hleaves : sk.tree.LeavesIn falcon512.sigmaMin falcon512.sigmaMax) (Z : ℝ)
    (hZ : falcon512TailT ≤ Z) :
    preimageTailMass falcon512 prims sk Z ≤ ENNReal.ofReal (1024 * (2 * (1 + 1 / 2 ^ 36) ^ 1024) *
      Real.exp (-((Z - falcon512TailT) ^ 2 / (2 * falcon512TailV)))) := by
  have hdepth : falcon512.fftDepth = 8 := by decide
  have hn : 2 * 2 ^ falcon512.fftDepth = falcon512.n := by decide
  have hσmin : (1277 / 1000 : ℝ) ≤ falcon512.sigmaMin := by
    change (1277 / 1000 : ℝ) ≤ (12778336969128337 : ℝ) / 10000000000000000
    norm_num
  have hσ : falcon512.sigma = 1657366171829776 / 10000000000000 := rfl
  have hq : ((modulus : ℕ) : ℝ) = 12289 := by norm_num [modulus]
  have hρ := trueTreeLeafRatio_le_two (by rw [hdepth]; norm_num) sk
  have hV0 : 0 < falcon512TailV := by rw [falcon512TailV]; positivity
  have hvar : ∀ i, sk.tree.devVar (coeffFst i) ≤ falcon512TailV ∧
      sk.tree.devVar (coeffSnd i) ≤ falcon512TailV := fun i => by
    obtain ⟨h1, h2⟩ := devVar_trueTree_le hn sk hntru htree i
    have hs1 := sum_sq_le_of_abs_le _ _ (fun j => (hkey j).2.2.1) (fun j => (hkey j).2.2.2)
    have hs2 := sum_sq_le_of_abs_le _ _ (fun j => (hkey j).1) (fun j => (hkey j).2.1)
    have hn512 : (falcon512.n : ℝ) = 512 := by norm_num [falcon512, ParameterSet.params]
    rw [hn512] at hs1 hs2
    have hX : ∀ X : ℝ, 0 ≤ X → X ≤ 512 * (127 ^ 2 + 127 ^ 2) →
        trueTreeLeafRatio falcon512 sk * falcon512.sigma ^ 2 * X / (modulus : ℝ) ^ 2 ≤
          falcon512TailV := fun X hX0 hX => by
      rw [hq, falcon512TailV, div_le_div_iff_of_pos_right (by positivity)]
      calc _ ≤ 2 * falcon512.sigma ^ 2 * X := by gcongr
        _ ≤ _ := by gcongr
    have hpos : ∀ (a b : Fin falcon512.n → ℤ), 0 ≤ ∑ j, ((a j : ℝ) ^ 2 + (b j : ℝ) ^ 2) :=
      fun a b => Finset.sum_nonneg fun _ _ => by positivity
    exact ⟨h1.trans (hX _ (hpos (fun j => sk.capF.get j) (fun j => sk.capG.get j)) hs1),
      h2.trans (hX _ (hpos (fun j => sk.f.get j) (fun j => sk.g.get j)) hs2)⟩
  have htarget : ∀ c i, |coeffFst i (toFFTTarget falcon512 prims c sk)| ≤ falcon512TailT ∧
      |coeffSnd i (toFFTTarget falcon512 prims c sk)| ≤ falcon512TailT := fun c i => by
    have h := abs_coeff_toFFTTarget_le hn prims hfft htgt sk (fun j => ⟨(hkey j).1,
      (hkey j).2.2.1⟩) c i
    have hn512 : (falcon512.n : ℝ) = 512 := by norm_num [falcon512, ParameterSet.params]
    rw [hn512] at h
    exact h
  have h := preimageTailMass_le prims sk hσmin hleaves falcon512TailT falcon512TailV Z hZ
    htarget hvar hV0
  rw [hdepth, show (4 * 2 ^ 8 : ℝ) = 1024 by norm_num, show 4 * 2 ^ 8 = 1024 by norm_num] at h
  exact h

private theorem one_add_pow_le : (1 + 1 / 2 ^ 36 : ℝ) ^ 1024 ≤ 1 + 1 / 2 ^ 25 := by
  have ht : |(1024 / 2 ^ 36 : ℝ)| ≤ 1 := by rw [abs_of_pos (by norm_num)]; norm_num
  have hq := Real.abs_exp_sub_one_sub_id_le ht
  calc (1 + 1 / 2 ^ 36 : ℝ) ^ 1024 ≤ Real.exp (1 / 2 ^ 36) ^ 1024 := by
        gcongr; linarith [Real.add_one_le_exp (1 / 2 ^ 36 : ℝ)]
    _ = Real.exp (1024 / 2 ^ 36) := by rw [← Real.exp_nat_mul]; norm_num
    _ ≤ 1 + 1024 / 2 ^ 36 + (1024 / 2 ^ 36) ^ 2 := by linarith [(abs_le.1 hq).2]
    _ ≤ _ := by norm_num

private theorem exp_nat_ge_two_pow (m : ℕ) : (2 : ℝ) ^ m ≤ Real.exp m := by
  rw [← Real.exp_one_pow]
  exact pow_le_pow_left₀ (by norm_num) (by linarith [Real.exp_one_gt_d9]) m

/-- **The Falcon-512 preimage tail at `Z = 2^33`**: at most `2⁻¹⁰⁰⁰` per signing attempt, for keys
and trees as in `preimageTailMass_falcon512_le`. The bound proved there is about
`2^(-8.9 · 10^15)`. -/
theorem preimageTailMass_falcon512_two_pow_33_le (prims : Primitives falcon512)
    (hfft : prims.fftInt = Primitives.exactFftInt falcon512)
    (htgt : prims.fftTarget = Primitives.exactFftTarget falcon512) (sk : SecretKey falcon512)
    (hntru : ntruEquation falcon512 sk.f sk.g sk.capF sk.capG)
    (htree : sk.tree = trueTree falcon512 sk)
    (hkey : ∀ i, |sk.f.get i| ≤ 127 ∧ |sk.g.get i| ≤ 127 ∧ |sk.capF.get i| ≤ 127 ∧
      |sk.capG.get i| ≤ 127)
    (hleaves : sk.tree.LeavesIn falcon512.sigmaMin falcon512.sigmaMax) :
    preimageTailMass falcon512 prims sk (2 ^ 33) ≤ ENNReal.ofReal (1 / 2 ^ 1000) := by
  have hσ : falcon512.sigma = 1657366171829776 / 10000000000000 := rfl
  have hT : falcon512TailT ≤ 2 ^ 33 := by rw [falcon512TailT]; norm_num
  refine (preimageTailMass_falcon512_le prims hfft htgt sk hntru htree hkey hleaves _ hT).trans
    (ENNReal.ofReal_le_ofReal ?_)
  have hx : (1013 : ℝ) ≤ (2 ^ 33 - falcon512TailT) ^ 2 / (2 * falcon512TailV) := by
    rw [falcon512TailT, falcon512TailV, hσ]; norm_num
  have he : Real.exp (-((2 ^ 33 - falcon512TailT) ^ 2 / (2 * falcon512TailV))) ≤
      1 / 2 ^ 13 * (1 / 2 ^ 1000) := by
    rw [Real.exp_neg, ← one_div, one_div_mul_one_div, ← pow_add]
    gcongr
    calc (2 : ℝ) ^ (13 + 1000) ≤ Real.exp ((13 + 1000 : ℕ) : ℝ) := exp_nat_ge_two_pow _
      _ ≤ _ := Real.exp_le_exp.2 (by push_cast; linarith)
  calc _ ≤ 1024 * (2 * (1 + 1 / 2 ^ 25)) * (1 / 2 ^ 13 * (1 / 2 ^ 1000) : ℝ) := by
        gcongr
        exact one_add_pow_le
    _ = 1024 * (2 * (1 + 1 / 2 ^ 25)) / 2 ^ 13 * (1 / 2 ^ 1000) := by
        generalize (2 : ℝ) ^ 1000 = y
        ring
    _ ≤ 1 * (1 / 2 ^ 1000) := by gcongr; norm_num
    _ = _ := one_mul _

/-- **The Falcon-512 preimage tail at `Z = 80000`**: at most `2⁻¹⁰⁰⁰` per signing attempt, for keys
and trees as in `preimageTailMass_falcon512_le`. The bound proved there is about `2^(-26935)`. -/
theorem preimageTailMass_falcon512_80000_le (prims : Primitives falcon512)
    (hfft : prims.fftInt = Primitives.exactFftInt falcon512)
    (htgt : prims.fftTarget = Primitives.exactFftTarget falcon512) (sk : SecretKey falcon512)
    (hntru : ntruEquation falcon512 sk.f sk.g sk.capF sk.capG)
    (htree : sk.tree = trueTree falcon512 sk)
    (hkey : ∀ i, |sk.f.get i| ≤ 127 ∧ |sk.g.get i| ≤ 127 ∧ |sk.capF.get i| ≤ 127 ∧
      |sk.capG.get i| ≤ 127)
    (hleaves : sk.tree.LeavesIn falcon512.sigmaMin falcon512.sigmaMax) :
    preimageTailMass falcon512 prims sk 80000 ≤ ENNReal.ofReal (1 / 2 ^ 1000) := by
  have hσ : falcon512.sigma = 1657366171829776 / 10000000000000 := rfl
  have hT : falcon512TailT ≤ 80000 := by rw [falcon512TailT]; norm_num
  refine (preimageTailMass_falcon512_le prims hfft htgt sk hntru htree hkey hleaves _ hT).trans
    (ENNReal.ofReal_le_ofReal ?_)
  have hx : (1013 : ℝ) ≤ (80000 - falcon512TailT) ^ 2 / (2 * falcon512TailV) := by
    rw [falcon512TailT, falcon512TailV, hσ]; norm_num
  have he : Real.exp (-((80000 - falcon512TailT) ^ 2 / (2 * falcon512TailV))) ≤
      1 / 2 ^ 13 * (1 / 2 ^ 1000) := by
    rw [Real.exp_neg, ← one_div, one_div_mul_one_div, ← pow_add]
    gcongr
    calc (2 : ℝ) ^ (13 + 1000) ≤ Real.exp ((13 + 1000 : ℕ) : ℝ) := exp_nat_ge_two_pow _
      _ ≤ _ := Real.exp_le_exp.2 (by push_cast; linarith)
  calc _ ≤ 1024 * (2 * (1 + 1 / 2 ^ 25)) * (1 / 2 ^ 13 * (1 / 2 ^ 1000) : ℝ) := by
        gcongr
        exact one_add_pow_le
    _ = 1024 * (2 * (1 + 1 / 2 ^ 25)) / 2 ^ 13 * (1 / 2 ^ 1000) := by
        generalize (2 : ℝ) ^ 1000 = y
        ring
    _ ≤ 1 * (1 / 2 ^ 1000) := by gcongr; norm_num
    _ = _ := one_mul _

end Falcon
