/-
Copyright (c) 2026 XC0R. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XC0R
-/

module
public import LatticeCrypto.Falcon.BasisCoords
import all LatticeCrypto.Falcon.PackedFFT
import LatticeCrypto.Falcon.FFTStagesL2
import ToMathlib.Probability.SecondMoment

/-!
# Variance proxies, far event and rejection of the basis coordinates

Under the true tree and the ideal sampler, for the basis coordinates `ψ` of
`LatticeCrypto.Falcon.BasisCoords`:

* every coordinate of `ψ` has variance proxy at most `2σ²` (`devVar_trueTree_basisCoeff_le`), so
  the far event `BasisFar` has mass at most `4 · 2^κ · 2K · exp(-((q + 1) / 2)² / (4σ²))` with
  `K = (1 + 2⁻³⁶)^(4 · 2^κ)` (`prob_basisFar_ideal_le`);
* the variance proxies of the `4 · 2^κ` coordinates sum to exactly `4 · 2^κ σ²`
  (`sum_devVar_trueTree_basisCoeff`), through the quadratic form `gramForm` of the Gram matrix,
  its LDL⋆ and split identities (`gramForm_ldl`, `gramForm_mergeFFT`) and Parseval
  (`sum_sq_basisCoeff`);
* Markov's inequality with the second moment bound `MeasureTheory.lintegral_sq_le_of_mgf` bounds
  the probability that `‖ψ(t - z)‖²` exceeds `⌊β²⌋` by
  `4 · 2^κ σ² (1 + η) / (⌊β²⌋ + 1)` (`prob_basisNormSq_ge_ideal_le`), about `0.827` at
  Falcon-512 and Falcon-1024.
-/

public section

open OracleComp LatticeCrypto MeasureTheory
open scoped ENNReal ComplexConjugate

namespace Falcon

variable {p : Params}

/-! ## Variance proxies of the basis coordinates -/

/-- A slot form whose weights are `α` times a column of `B⋆`, with `‖α j‖² = 4^(-k)`, has
inverse-Gram form `2^k / 4^k` under the positive Gram matrix of `B = [[g, -f], [G, -F]]`. -/
private theorem gramQ_basis_eq {k : ℕ} (g f G F : RealFFTPoly k)
    (hpos : PosGram (Primitives.mulFFT g (RealFFTPoly.adjFFT g) +
        Primitives.mulFFT f (RealFFTPoly.adjFFT f))
      (Primitives.mulFFT G (RealFFTPoly.adjFFT g) + Primitives.mulFFT F (RealFFTPoly.adjFFT f))
      (Primitives.mulFFT G (RealFFTPoly.adjFFT G) + Primitives.mulFFT F (RealFFTPoly.adjFFT F)))
    (α : Fin (2 ^ k) → ℂ) (hα : ∀ j, ‖α j‖ ^ 2 = 1 / 4 ^ k) (a b : Fin (2 ^ k) → ℂ)
    (hab : (∀ j, a j = α j * conj (RealFFTPoly.coord g j) ∧
        b j = α j * conj (RealFFTPoly.coord G j)) ∨
      (∀ j, a j = -(α j * conj (RealFFTPoly.coord f j)) ∧
        b j = -(α j * conj (RealFFTPoly.coord F j)))) :
    gramQ (Primitives.mulFFT g (RealFFTPoly.adjFFT g) +
        Primitives.mulFFT f (RealFFTPoly.adjFFT f))
      (Primitives.mulFFT G (RealFFTPoly.adjFFT g) + Primitives.mulFFT F (RealFFTPoly.adjFFT f))
      (Primitives.mulFFT G (RealFFTPoly.adjFFT G) + Primitives.mulFFT F (RealFFTPoly.adjFFT F))
      a b = 2 ^ k * (1 / 4 ^ k) := by
  rw [gramQ]
  calc _ = ∑ _j : Fin (2 ^ k), (1 / 4 ^ k : ℝ) := Finset.sum_congr rfl fun j _ => by
        have e10 : RealFFTPoly.coord (Primitives.mulFFT G (RealFFTPoly.adjFFT g) +
            Primitives.mulFFT F (RealFFTPoly.adjFFT f)) j =
            RealFFTPoly.coord G j * conj (RealFFTPoly.coord g j) +
              RealFFTPoly.coord F j * conj (RealFFTPoly.coord f j) := by
          rw [RealFFTPoly.coord_add, RealFFTPoly.coord_mulFFT, RealFFTPoly.coord_mulFFT,
            RealFFTPoly.coord_adjFFT, RealFFTPoly.coord_adjFFT]
        obtain ⟨-, -, -, hD⟩ := hpos j
        rw [RealFFTPoly.coord_mulFFT_adjFFT_add, RealFFTPoly.coord_mulFFT_adjFFT_add, e10,
          Complex.ofReal_re, Complex.ofReal_re] at hD
        rw [slotQ, RealFFTPoly.coord_mulFFT_adjFFT_add, RealFFTPoly.coord_mulFFT_adjFFT_add, e10,
          Complex.ofReal_re, Complex.ofReal_re, div_eq_iff (sub_pos.2 hD).ne', ← hα j]
        rcases hab with h | h <;> rw [(h j).1, (h j).2] <;>
          simp only [Complex.sq_norm_eq_re_sq_add_im_sq, Complex.mul_re, Complex.mul_im,
            Complex.add_re, Complex.add_im, Complex.neg_re, Complex.neg_im, Complex.conj_re,
            Complex.conj_im, map_add, map_mul, map_neg, Complex.conj_conj] <;>
          ring
    _ = _ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        push_cast
        ring

private theorem toCoeffs_add_mulFFT_eq_slotForm {k : ℕ} (u v : RealFFTPoly k)
    (m : Fin (2 * 2 ^ k)) (α : Fin (2 ^ k) → ℂ)
    (hrep : ∀ x : RealFFTPoly k, RealFFTPoly.toCoeffs k x m =
      ∑ j, (conj (α j) * RealFFTPoly.coord x j).re) :
    (fun w : FFTPair k => RealFFTPoly.toCoeffs k
        (Primitives.mulFFT w.1 u + Primitives.mulFFT w.2 v) m) =
      slotForm (fun j => α j * conj (RealFFTPoly.coord u j))
        (fun j => α j * conj (RealFFTPoly.coord v j)) := funext fun w => by
  rw [hrep, slotForm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [RealFFTPoly.coord_add, RealFFTPoly.coord_mulFFT, RealFFTPoly.coord_mulFFT]
  congr 1
  simp only [map_mul, Complex.conj_conj]
  ring

private theorem toCoeffs_neg_add_mulFFT_eq_slotForm {k : ℕ} (u v : RealFFTPoly k)
    (m : Fin (2 * 2 ^ k)) (α : Fin (2 ^ k) → ℂ)
    (hrep : ∀ x : RealFFTPoly k, RealFFTPoly.toCoeffs k x m =
      ∑ j, (conj (α j) * RealFFTPoly.coord x j).re) :
    (fun w : FFTPair k => RealFFTPoly.toCoeffs k
        (-(Primitives.mulFFT w.1 u + Primitives.mulFFT w.2 v)) m) =
      slotForm (fun j => -(α j * conj (RealFFTPoly.coord u j)))
        (fun j => -(α j * conj (RealFFTPoly.coord v j))) := funext fun w => by
  rw [hrep, slotForm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [RealFFTPoly.coord_neg, RealFFTPoly.coord_add, RealFFTPoly.coord_mulFFT,
    RealFFTPoly.coord_mulFFT]
  congr 1
  simp only [map_neg, map_mul, Complex.conj_conj]
  ring

/-- **Variance proxy of a basis coordinate.** Under the true tree every coordinate of `ψ` has
variance proxy at most `2σ²`: its inverse-Gram form is `2^(-κ)` (`det = q²` at every slot), and
the leaf ratio below the root is at most `2`. -/
theorem devVar_trueTree_basisCoeff_le (hn : 2 * 2 ^ p.fftDepth = p.n)
    (hdepth : 1 ≤ p.fftDepth) (sk : SecretKey p)
    (hntru : ntruEquation p sk.f sk.g sk.capF sk.capG) (i : Fin (2 * 2 ^ p.fftDepth)) :
    (trueTree p sk).devVar (basisCoeffFst sk i) ≤ 2 * p.sigma ^ 2 ∧
      (trueTree p sk).devVar (basisCoeffSnd sk i) ≤ 2 * p.sigma ^ 2 := by
  have hpos := posGram_gramFFT hn sk hntru
  have hρ2 := trueTreeLeafRatio_le_two hdepth sk
  obtain ⟨α, hα, hrep⟩ := toCoeffs_eq_slotSum p.fftDepth i
  have h4 : (4 : ℝ) ^ p.fftDepth = 2 ^ p.fftDepth * 2 ^ p.fftDepth := by
    rw [← mul_pow]; norm_num
  have hfin : ∀ a b : Fin (2 ^ p.fftDepth) → ℂ,
      gramQ (gramFFT p sk).1 (gramFFT p sk).2.1 (gramFFT p sk).2.2 a b =
        2 ^ p.fftDepth * (1 / 4 ^ p.fftDepth) →
      (trueTree p sk).devVar (slotForm a b) ≤ 2 * p.sigma ^ 2 := by
    intro a b hab
    refine (devVar_ffLDL_le p.sigma _ _ _ _ hpos a b).trans ?_
    have e : ∀ ρ : ℝ, ρ * p.sigma ^ 2 * 2 ^ p.fftDepth *
        (2 ^ p.fftDepth * (1 / 4 ^ p.fftDepth)) = ρ * p.sigma ^ 2 := fun ρ => by
      rw [h4]; field_simp
    rw [hab, e]
    exact mul_le_mul_of_nonneg_right hρ2 (sq_nonneg _)
  refine ⟨?_, ?_⟩
  · rw [show basisCoeffFst sk i = _ from toCoeffs_add_mulFFT_eq_slotForm _ _ i α hrep]
    exact hfin _ _ (gramQ_basis_eq (Primitives.exactFftInt p sk.g)
      (Primitives.exactFftInt p sk.f) (Primitives.exactFftInt p sk.capG)
      (Primitives.exactFftInt p sk.capF) hpos α hα _ _
      (Or.inl fun j => ⟨rfl, rfl⟩))
  · rw [show basisCoeffSnd sk i = _ from toCoeffs_neg_add_mulFFT_eq_slotForm _ _ i α hrep]
    exact hfin _ _ (gramQ_basis_eq (Primitives.exactFftInt p sk.g)
      (Primitives.exactFftInt p sk.f) (Primitives.exactFftInt p sk.capG)
      (Primitives.exactFftInt p sk.capF) hpos α hα _ _
      (Or.inr fun j => ⟨rfl, rfl⟩))

/-- `4 · 2^κ · 2 (1 + 2⁻³⁶)^(4 · 2^κ) · exp(-((q + 1) / 2)² / (4σ²))`: the ideal mass of the far
event. -/
@[expose] noncomputable def idealFarBound (p : Params) : ℝ :=
  4 * 2 ^ p.fftDepth * (2 * (1 + 1 / 2 ^ 36) ^ (4 * 2 ^ p.fftDepth)) *
    Real.exp (-(farRadius ^ 2 / (4 * p.sigma ^ 2)))

/-- **The far event under the ideal sampler**, from `prob_abs_dev_ge_le` at `V = 2σ²` and a union
bound over the `4 · 2^κ` coordinates. -/
theorem prob_basisFar_ideal_le (hn : 2 * 2 ^ p.fftDepth = p.n) (hdepth : 1 ≤ p.fftDepth)
    (hσ : 1277 / 1000 ≤ p.sigmaMin) (sk : SecretKey p)
    (hntru : ntruEquation p sk.f sk.g sk.capF sk.capG) (htree : sk.tree = trueTree p sk)
    (hleaves : sk.tree.LeavesIn p.sigmaMin p.sigmaMax) (t : FFTPair p.fftDepth) :
    Pr{let z ← ffSamplingWith idealSamplerQuery p.fftDepth t sk.tree}[BasisFar sk (t - z)] ≤
      ENNReal.ofReal (idealFarBound p) := by
  rw [htree] at hleaves ⊢
  have hK : (1 : ℝ) ≤ (1 + 1 / 2 ^ 36) ^ (4 * 2 ^ p.fftDepth) := one_le_pow₀ (by norm_num)
  rcases (sq_nonneg p.sigma).eq_or_lt with hσ0 | hσpos
  · refine (prEvent_le_one _).trans ?_
    rw [idealFarBound, ← hσ0, mul_zero, div_zero, neg_zero, Real.exp_zero, mul_one,
      ← ENNReal.ofReal_one]
    have h2 : (1 : ℝ) ≤ 2 ^ p.fftDepth := one_le_pow₀ (by norm_num)
    exact ENNReal.ofReal_le_ofReal (by nlinarith)
  let : MeasurableSpace (FFTPair p.fftDepth) := ⊤
  have : DiscreteMeasurableSpace (FFTPair p.fftDepth) := ⟨fun _ => trivial⟩
  have hV0 : 0 < 2 * p.sigma ^ 2 := by linarith
  have hR : 0 ≤ farRadius := by unfold farRadius; positivity
  set oa := ffSamplingWith idealSamplerQuery p.fftDepth t (trueTree p sk)
  set B : ℝ := 2 * (1 + 1 / 2 ^ 36) ^ (4 * 2 ^ p.fftDepth) *
    Real.exp (-(farRadius ^ 2 / (2 * (2 * p.sigma ^ 2))))
  have hev : ∀ i : Fin (2 * 2 ^ p.fftDepth),
      𝒟[oa] {z | farRadius ≤ |basisCoeffFst sk i (t - z)|} ≤ ENNReal.ofReal B ∧
        𝒟[oa] {z | farRadius ≤ |basisCoeffSnd sk i (t - z)|} ≤ ENNReal.ofReal B := fun i => by
    have hv := devVar_trueTree_basisCoeff_le hn hdepth sk hntru i
    constructor
    · rw [← prEvent_eq_evalDist_of_discrete]
      exact prob_abs_dev_ge_le hσ p.fftDepth t _ hleaves _ (fftPairLinear_basisCoeffFst sk i)
        hv.1 hV0 hR
    · rw [← prEvent_eq_evalDist_of_discrete]
      exact prob_abs_dev_ge_le hσ p.fftDepth t _ hleaves _ (fftPairLinear_basisCoeffSnd sk i)
        hv.2 hV0 hR
  rw [prEvent_eq_evalDist_of_discrete]
  have hset : {z : FFTPair p.fftDepth | BasisFar sk (t - z)} =
      ⋃ i, ({z | farRadius ≤ |basisCoeffFst sk i (t - z)|} ∪
        {z | farRadius ≤ |basisCoeffSnd sk i (t - z)|}) := by
    ext z; simp [BasisFar]
  rw [hset]
  refine (measure_iUnion_fintype_le _ _).trans ?_
  calc ∑ i, 𝒟[oa] ({z | farRadius ≤ |basisCoeffFst sk i (t - z)|} ∪
        {z | farRadius ≤ |basisCoeffSnd sk i (t - z)|})
      ≤ ∑ _i : Fin (2 * 2 ^ p.fftDepth), (ENNReal.ofReal B + ENNReal.ofReal B) :=
        Finset.sum_le_sum fun i _ => (measure_union_le _ _).trans (add_le_add (hev i).1 (hev i).2)
    _ = _ := by
        have hB : 0 ≤ B := by positivity
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
          ← ENNReal.ofReal_add hB hB, ← ENNReal.ofReal_natCast,
          ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        simp only [B, idealFarBound]
        rw [show 2 * (2 * p.sigma ^ 2) = 4 * p.sigma ^ 2 by ring]
        push_cast
        ring

/-! ## The trace of the variance proxies -/

/-- The quadratic form `Σⱼ (g00ⱼ ‖w₀ⱼ‖² + g11ⱼ ‖w₁ⱼ‖² + 2 Re(w₀ⱼ conj w₁ⱼ conj g10ⱼ))` of the
self-adjoint Gram matrix `[[g00, g10⋆], [g10, g11]]`. -/
@[expose] noncomputable def gramForm {k : ℕ} (g00 g10 g11 : RealFFTPoly k) (w : FFTPair k) : ℝ :=
  ∑ j, ((RealFFTPoly.coord g00 j).re * ‖RealFFTPoly.coord w.1 j‖ ^ 2 +
    (RealFFTPoly.coord g11 j).re * ‖RealFFTPoly.coord w.2 j‖ ^ 2 +
    2 * (RealFFTPoly.coord w.1 j * conj (RealFFTPoly.coord w.2 j) *
      conj (RealFFTPoly.coord g10 j)).re)

/-- The variance proxy of a quadratic form `Q` of the deviation `t - z`: `devVar` with `φ²`
replaced by `Q`. -/
@[expose] noncomputable def FalconTree.devVarForm :
    {κ : ℕ} → FalconTree κ → (FFTPair κ → ℝ) → ℝ
  | _, .leaf σ, Q => σ ^ 2 * (Q (leafPair 1 0 0 0) + Q (leafPair 0 1 0 0) +
      Q (leafPair 0 0 1 0) + Q (leafPair 0 0 0 1))
  | _, .node ℓ left right, Q =>
      left.devVarForm (fun x => Q (Primitives.mergeFFT x.1 x.2, 0)) +
        right.devVarForm (fun y => Q (-Primitives.mulFFT ℓ (Primitives.mergeFFT y.1 y.2),
          Primitives.mergeFFT y.1 y.2))

/-- The variance proxy of a sum of squares is the sum of the variance proxies. -/
theorem FalconTree.devVarForm_sum_sq {ι : Type} [Fintype ι] :
    ∀ {κ : ℕ} (tree : FalconTree κ) (φ : ι → FFTPair κ → ℝ),
      tree.devVarForm (fun w => ∑ i, φ i w ^ 2) = ∑ i, tree.devVar (φ i)
  | _, .leaf σ, φ => by
    simp only [FalconTree.devVarForm, FalconTree.devVar, Finset.sum_add_distrib, Finset.mul_sum,
      mul_add]
  | _, .node ℓ left right, φ => by
    simp only [FalconTree.devVarForm, FalconTree.devVar, Finset.sum_add_distrib]
    exact congrArg₂ (· + ·) (FalconTree.devVarForm_sum_sq left _)
      (FalconTree.devVarForm_sum_sq right _)

/-- The variance proxy is homogeneous in the quadratic form. -/
theorem FalconTree.devVarForm_const_mul (c : ℝ) :
    ∀ {κ : ℕ} (tree : FalconTree κ) (Q : FFTPair κ → ℝ),
      tree.devVarForm (fun w => c * Q w) = c * tree.devVarForm Q
  | _, .leaf σ, Q => by
    simp only [FalconTree.devVarForm]
    ring
  | _, .node ℓ left right, Q => by
    simp only [FalconTree.devVarForm]
    rw [FalconTree.devVarForm_const_mul c left (fun x => Q (Primitives.mergeFFT x.1 x.2, 0)),
      FalconTree.devVarForm_const_mul c right (fun y =>
        Q (-Primitives.mulFFT ℓ (Primitives.mergeFFT y.1 y.2), Primitives.mergeFFT y.1 y.2))]
    ring

/-- **The LDL⋆ identity of the direct form**: with `ℓ = g10 / g00` and
`D11 = g11 - g10 g10⋆ / g00`, the form at `(E₀ - ℓ E₁, E₁)` is `g00 ‖E₀‖² + D11 ‖E₁‖²`. -/
theorem gramForm_ldl {k : ℕ} {g00 g10 g11 : RealFFTPoly k} (h : PosGram g00 g10 g11)
    (E : FFTPair k) :
    gramForm g00 g10 g11
        (E.1 - Primitives.mulFFT (RealFFTPoly.divFFT g10 g00) E.2, E.2) =
      gramForm g00 0 (g11 - Primitives.mulFFT g10
        (RealFFTPoly.divFFT (RealFFTPoly.adjFFT g10) g00)) E := by
  rw [gramForm, gramForm]
  refine Finset.sum_congr rfl fun j _ => ?_
  obtain ⟨h00, -, hx, -⟩ := h j
  rw [coord_d11 h j, RealFFTPoly.coord_zero, RealFFTPoly.coord_sub, RealFFTPoly.coord_mulFFT,
    RealFFTPoly.coord_divFFT]
  simp only [map_zero, mul_zero, Complex.zero_re, add_zero, Complex.ofReal_re,
    Complex.sq_norm_eq_re_sq_add_im_sq, Complex.sub_re, Complex.sub_im, Complex.mul_re,
    Complex.mul_im, Complex.div_re, Complex.div_im, Complex.normSq_apply, Complex.conj_re,
    Complex.conj_im, h00]
  field_simp
  ring

/-- **The split identity of the direct form**: for real slot weights `x`, the weighted squared
norm of `mergeFFT y` is twice the form of the split Gram matrix at `y`. -/
theorem gramForm_mergeFFT {k : ℕ} (x : RealFFTPoly (k + 1))
    (hx : ∀ J, (RealFFTPoly.coord x J).im = 0) (y : FFTPair k) :
    gramForm x 0 0 (Primitives.mergeFFT y.1 y.2, 0) =
      2 * gramForm (Primitives.splitFFT x).1 (RealFFTPoly.adjFFT (Primitives.splitFFT x).2)
        (Primitives.splitFFT x).1 y := by
  rw [gramForm, gramForm, sum_two_pow_succ, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [(RealFFTPoly.coord_mergeFFT_two _ _ i).1, (RealFFTPoly.coord_mergeFFT_two _ _ i).2,
    RealFFTPoly.coord_splitFFT_fst, RealFFTPoly.coord_adjFFT, RealFFTPoly.coord_splitFFT_snd]
  have h0 := hx ⟨2 * i.1, by omega⟩
  have h1 := hx ⟨2 * i.1 + 1, by omega⟩
  have hcs := Real.cos_sq_add_sin_sq (Primitives.splitAngle i)
  simp only [RealFFTPoly.coord_zero, map_zero, mul_zero, Complex.zero_re, add_zero,
    Complex.sq_norm_eq_re_sq_add_im_sq, Complex.zero_im, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.conj_re,
    Complex.conj_im, Complex.conj_conj, Complex.div_ofNat_re, Complex.div_ofNat_im,
    Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im, h0, h1]
  linear_combination ((RealFFTPoly.coord x ⟨2 * i.1, by omega⟩).re +
    (RealFFTPoly.coord x ⟨2 * i.1 + 1, by omega⟩).re) *
      ((RealFFTPoly.coord y.2 i).re ^ 2 + (RealFFTPoly.coord y.2 i).im ^ 2) * hcs

/-- The merge recursion inverts the split recursion. -/
theorem RealFFTPoly.ofCoeffs_toCoeffs :
    ∀ (k : ℕ) (v : RealFFTPoly k), RealFFTPoly.ofCoeffs k (RealFFTPoly.toCoeffs k v) = v
  | 0, v => by
    refine RealFFTPoly.ext_coord fun j => ?_
    rw [slot_zero j, RealFFTPoly.ofCoeffs, RealFFTPoly.coord_pack]
    apply Complex.ext <;>
      simp [RealFFTPoly.toCoeffs, RealFFTPoly.coord, RealFFTPoly.re, RealFFTPoly.im]
  | k + 1, v => by
    rw [RealFFTPoly.ofCoeffs]
    conv_rhs => rw [← RealFFTPoly.mergeFFT_splitFFT v]
    congr 1
    · conv_rhs => rw [← RealFFTPoly.ofCoeffs_toCoeffs k (Primitives.splitFFT v).1]
      congr 1
      funext i
      simp only [RealFFTPoly.toCoeffs]
      split_ifs with hc
      · congr 1
        ext
        simp
      · exact absurd (by omega) hc
    · conv_rhs => rw [← RealFFTPoly.ofCoeffs_toCoeffs k (Primitives.splitFFT v).2]
      congr 1
      funext i
      simp only [RealFFTPoly.toCoeffs]
      split_ifs with hc
      · exact absurd hc (by omega)
      · congr 1
        ext
        simp only
        omega

/-- Parseval for the coefficients of `w · B`, `B = [[g, -f], [G, -F]]`. -/
private theorem sum_sq_toCoeffs_basis {k : ℕ} (g f G F : RealFFTPoly k) (w : FFTPair k) :
    ∑ i, (RealFFTPoly.toCoeffs k (Primitives.mulFFT w.1 g + Primitives.mulFFT w.2 G) i ^ 2 +
        RealFFTPoly.toCoeffs k (-(Primitives.mulFFT w.1 f + Primitives.mulFFT w.2 F)) i ^ 2) =
      gramForm (Primitives.mulFFT g (RealFFTPoly.adjFFT g) +
          Primitives.mulFFT f (RealFFTPoly.adjFFT f))
        (Primitives.mulFFT G (RealFFTPoly.adjFFT g) + Primitives.mulFFT F (RealFFTPoly.adjFFT f))
        (Primitives.mulFFT G (RealFFTPoly.adjFFT G) + Primitives.mulFFT F (RealFFTPoly.adjFFT F))
        w / 2 ^ k := by
  have hpar : ∀ v : RealFFTPoly k, ∑ i, RealFFTPoly.toCoeffs k v i ^ 2 =
      (∑ j, ‖RealFFTPoly.coord v j‖ ^ 2) / 2 ^ k := fun v => by
    rw [eq_div_iff (by positivity)]
    conv_rhs => rw [← RealFFTPoly.ofCoeffs_toCoeffs k v]
    rw [FFTStages.sum_norm_coord_ofCoeffs_sq]
    ring
  rw [Finset.sum_add_distrib, hpar, hpar, ← add_div, ← Finset.sum_add_distrib, gramForm]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [RealFFTPoly.coord_neg, RealFFTPoly.coord_add, RealFFTPoly.coord_mulFFT,
    RealFFTPoly.coord_adjFFT, norm_neg, Complex.sq_norm_eq_re_sq_add_im_sq, Complex.add_re,
    Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im, map_add,
    map_mul, Complex.conj_conj]
  ring

/-- **Parseval for the basis coordinates**: `Σᵢ ψᵢ(w)² = 2^(-κ) · w (B B⋆) w⋆`. -/
theorem sum_sq_basisCoeff (sk : SecretKey p) (w : FFTPair p.fftDepth) :
    ∑ i, (basisCoeffFst sk i w ^ 2 + basisCoeffSnd sk i w ^ 2) =
      gramForm (gramFFT p sk).1 (gramFFT p sk).2.1 (gramFFT p sk).2.2 w / 2 ^ p.fftDepth :=
  sum_sq_toCoeffs_basis _ _ _ _ w

private theorem d11_real_pos {k : ℕ} {g00 g10 g11 : RealFFTPoly k} (h : PosGram g00 g10 g11)
    (J : Fin (2 ^ k)) :
    (RealFFTPoly.coord (g11 - Primitives.mulFFT g10
        (RealFFTPoly.divFFT (RealFFTPoly.adjFFT g10) g00)) J).im = 0 ∧
      0 < (RealFFTPoly.coord (g11 - Primitives.mulFFT g10
        (RealFFTPoly.divFFT (RealFFTPoly.adjFFT g10) g00)) J).re := by
  rw [coord_d11 h J, Complex.ofReal_im, Complex.ofReal_re]
  exact ⟨rfl, d11_pos h J⟩

/-- One level of ffLDL⋆ on its own direct form: twice the forms of the two children. -/
private theorem devVarForm_ffLDL_succ (σ : ℝ) {k : ℕ} {g00 g10 g11 : RealFFTPoly (k + 1)}
    (h : PosGram g00 g10 g11) (D : RealFFTPoly (k + 1))
    (hD : D = g11 - Primitives.mulFFT g10 (RealFFTPoly.divFFT (RealFFTPoly.adjFFT g10) g00)) :
    (ffLDL σ (k + 1) g00 g10 g11).devVarForm (gramForm g00 g10 g11) =
      2 * (ffLDL σ k (Primitives.splitFFT g00).1 (RealFFTPoly.adjFFT (Primitives.splitFFT g00).2)
          (Primitives.splitFFT g00).1).devVarForm (gramForm (Primitives.splitFFT g00).1
            (RealFFTPoly.adjFFT (Primitives.splitFFT g00).2) (Primitives.splitFFT g00).1) +
        2 * (ffLDL σ k (Primitives.splitFFT D).1 (RealFFTPoly.adjFFT (Primitives.splitFFT D).2)
          (Primitives.splitFFT D).1).devVarForm (gramForm (Primitives.splitFFT D).1
            (RealFFTPoly.adjFFT (Primitives.splitFFT D).2) (Primitives.splitFFT D).1) := by
  subst hD
  have hL : (fun x : FFTPair k => gramForm g00 g10 g11 (Primitives.mergeFFT x.1 x.2, 0)) =
      fun x => 2 * gramForm (Primitives.splitFFT g00).1
        (RealFFTPoly.adjFFT (Primitives.splitFFT g00).2) (Primitives.splitFFT g00).1 x :=
    funext fun x => by
      rw [← gramForm_mergeFFT g00 (fun J => (h J).1) x]
      simp [gramForm, RealFFTPoly.coord_zero]
  have hR : (fun y : FFTPair k => gramForm g00 g10 g11
      (-Primitives.mulFFT (RealFFTPoly.divFFT g10 g00) (Primitives.mergeFFT y.1 y.2),
        Primitives.mergeFFT y.1 y.2)) =
      fun y => 2 * gramForm (Primitives.splitFFT (g11 - Primitives.mulFFT g10
          (RealFFTPoly.divFFT (RealFFTPoly.adjFFT g10) g00))).1
        (RealFFTPoly.adjFFT (Primitives.splitFFT (g11 - Primitives.mulFFT g10
          (RealFFTPoly.divFFT (RealFFTPoly.adjFFT g10) g00))).2)
        (Primitives.splitFFT (g11 - Primitives.mulFFT g10
          (RealFFTPoly.divFFT (RealFFTPoly.adjFFT g10) g00))).1 y :=
    funext fun y => by
      rw [← gramForm_mergeFFT _ (fun J => (d11_real_pos h J).1) y]
      have e1 := gramForm_ldl h (0, Primitives.mergeFFT y.1 y.2)
      have e2 : gramForm g00 g10 g11
          (-Primitives.mulFFT (RealFFTPoly.divFFT g10 g00) (Primitives.mergeFFT y.1 y.2),
            Primitives.mergeFFT y.1 y.2) =
          gramForm g00 g10 g11 ((0 : RealFFTPoly (k + 1)) -
            Primitives.mulFFT (RealFFTPoly.divFFT g10 g00) (Primitives.mergeFFT y.1 y.2),
              Primitives.mergeFFT y.1 y.2) := by
        simp only [gramForm, RealFFTPoly.coord_neg, RealFFTPoly.coord_sub,
          RealFFTPoly.coord_zero, zero_sub]
      rw [e2]
      refine e1.trans ?_
      simp [gramForm, RealFFTPoly.coord_zero]
  rw [ffLDL, FalconTree.devVarForm, hL, hR, FalconTree.devVarForm_const_mul,
    FalconTree.devVarForm_const_mul]

/-- ffLDL⋆ of a self-split Gram matrix `[[a, b⋆], [b, a]]` on its own direct form. -/
private theorem devVarForm_ffLDL_self (σ : ℝ) :
    ∀ (k : ℕ) (a b : RealFFTPoly k), PosGram a b a →
      (ffLDL σ k a b a).devVarForm (gramForm a b a) = 4 * 4 ^ k * σ ^ 2
  | 0, a, b, h => by
    obtain ⟨-, -, hx, -⟩ := h ⟨0, by norm_num⟩
    have hs : ∀ w : FFTPair 0, gramForm a b a w =
        (RealFFTPoly.coord a ⟨0, by norm_num⟩).re *
            (‖RealFFTPoly.coord w.1 ⟨0, by norm_num⟩‖ ^ 2 +
              ‖RealFFTPoly.coord w.2 ⟨0, by norm_num⟩‖ ^ 2) +
          2 * (RealFFTPoly.coord w.1 ⟨0, by norm_num⟩ *
            conj (RealFFTPoly.coord w.2 ⟨0, by norm_num⟩) *
              conj (RealFFTPoly.coord b ⟨0, by norm_num⟩)).re := fun w => by
      rw [gramForm, Fintype.sum_eq_single ⟨0, by norm_num⟩ fun j hj => absurd (slot_zero j) hj]
      ring
    rw [ffLDL, FalconTree.devVarForm, hs, hs, hs, hs]
    simp only [RealFFTPoly.coord_re] at hx
    simp only [leafPair, RealFFTPoly.coord_pack, Vector.get_ofFn,
      Complex.sq_norm_eq_re_sq_add_im_sq, Complex.mul_re, Complex.mul_im, Complex.conj_re,
      Complex.conj_im, RealFFTPoly.coord_re, div_pow, Real.sq_sqrt hx.le]
    field_simp
    ring
  | k + 1, a, b, h => by
    have hg0 : ∀ J, (RealFFTPoly.coord a J).im = 0 ∧ 0 < (RealFFTPoly.coord a J).re :=
      fun J => ⟨(h J).1, (h J).2.2.1⟩
    rw [devVarForm_ffLDL_succ σ h _ rfl, devVarForm_ffLDL_self σ k _ _ (posGram_split a hg0),
      devVarForm_ffLDL_self σ k _ _ (posGram_split _ (d11_real_pos h))]
    ring

/-- **ffLDL⋆ diagonalises the direct form**: below a positive Gram matrix, the variance proxy of
its own form is `4 · 4^κ σ²`; every leaf contributes `4σ²`, every merge a factor `2`. -/
theorem devVarForm_ffLDL (σ : ℝ) (k : ℕ) {g00 g10 g11 : RealFFTPoly (k + 1)}
    (h : PosGram g00 g10 g11) :
    (ffLDL σ (k + 1) g00 g10 g11).devVarForm (gramForm g00 g10 g11) =
      4 * 4 ^ (k + 1) * σ ^ 2 := by
  have hg0 : ∀ J, (RealFFTPoly.coord g00 J).im = 0 ∧ 0 < (RealFFTPoly.coord g00 J).re :=
    fun J => ⟨(h J).1, (h J).2.2.1⟩
  rw [devVarForm_ffLDL_succ σ h _ rfl, devVarForm_ffLDL_self σ k _ _ (posGram_split g00 hg0),
    devVarForm_ffLDL_self σ k _ _ (posGram_split _ (d11_real_pos h))]
  ring

private theorem devVarForm_ffLDL_of_one_le (σ : ℝ) :
    ∀ (κ : ℕ), 1 ≤ κ → ∀ {g00 g10 g11 : RealFFTPoly κ}, PosGram g00 g10 g11 →
      (ffLDL σ κ g00 g10 g11).devVarForm (gramForm g00 g10 g11) = 4 * 4 ^ κ * σ ^ 2
  | 0, h, _, _, _, _ => absurd h (by norm_num)
  | k + 1, _, _, _, _, hp => devVarForm_ffLDL σ k hp

/-- **Trace of the variance proxies**: under the true tree the variance proxies of the `4 · 2^κ`
basis coordinates sum to exactly `4 · 2^κ σ²`. -/
theorem sum_devVar_trueTree_basisCoeff (hn : 2 * 2 ^ p.fftDepth = p.n)
    (hdepth : 1 ≤ p.fftDepth) (sk : SecretKey p)
    (hntru : ntruEquation p sk.f sk.g sk.capF sk.capG) :
    ∑ i, ((trueTree p sk).devVar (basisCoeffFst sk i) +
      (trueTree p sk).devVar (basisCoeffSnd sk i)) = 4 * 2 ^ p.fftDepth * p.sigma ^ 2 := by
  have h1 := FalconTree.devVarForm_sum_sq (trueTree p sk)
    (Sum.elim (basisCoeffFst sk) (basisCoeffSnd sk))
  simp only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr] at h1
  have h2 : (fun w => ∑ i, basisCoeffFst sk i w ^ 2 + ∑ i, basisCoeffSnd sk i w ^ 2) =
      fun w => 1 / 2 ^ p.fftDepth *
        gramForm (gramFFT p sk).1 (gramFFT p sk).2.1 (gramFFT p sk).2.2 w := funext fun w => by
    rw [← Finset.sum_add_distrib, sum_sq_basisCoeff]
    ring
  rw [Finset.sum_add_distrib, ← h1, h2, FalconTree.devVarForm_const_mul, trueTree,
    devVarForm_ffLDL_of_one_le p.sigma p.fftDepth hdepth (posGram_gramFFT hn sk hntru),
    show (4 : ℝ) ^ p.fftDepth = 2 ^ p.fftDepth * 2 ^ p.fftDepth by rw [← mul_pow]; norm_num]
  field_simp

/-! ## Rejection under the ideal sampler -/

/-- The slack `η = K - 1 + (1 + K) √(K - 1)` of the second moment at
`K = (1 + 2⁻³⁶)^(4 · 2^κ)`. -/
@[expose] noncomputable def mgfSlack (κ : ℕ) : ℝ :=
  (1 + 1 / 2 ^ 36) ^ (4 * 2 ^ κ) - 1 +
    (1 + (1 + 1 / 2 ^ 36) ^ (4 * 2 ^ κ)) * Real.sqrt ((1 + 1 / 2 ^ 36) ^ (4 * 2 ^ κ) - 1)

/-- `4 · 2^κ σ² (1 + η) / (⌊β²⌋ + 1)`: the ideal rejection bound. -/
@[expose] noncomputable def idealRejectBound (p : Params) : ℝ :=
  4 * 2 ^ p.fftDepth * p.sigma ^ 2 * (1 + mgfSlack p.fftDepth) / ((p.betaSquared : ℝ) + 1)

/-- **Rejection under the ideal sampler**: the squared norm of `ψ(t - z)` exceeds `⌊β²⌋` with
probability at most `idealRejectBound`, by Markov's inequality and the trace of the variance
proxies. -/
theorem prob_basisNormSq_ge_ideal_le (hn : 2 * 2 ^ p.fftDepth = p.n)
    (hdepth : 1 ≤ p.fftDepth) (hσ : 1277 / 1000 ≤ p.sigmaMin) (sk : SecretKey p)
    (hntru : ntruEquation p sk.f sk.g sk.capF sk.capG) (htree : sk.tree = trueTree p sk)
    (hleaves : sk.tree.LeavesIn p.sigmaMin p.sigmaMax) (t : FFTPair p.fftDepth) :
    Pr{let z ← ffSamplingWith idealSamplerQuery p.fftDepth t sk.tree}[
      (p.betaSquared : ℝ) + 1 ≤
        ∑ i, (basisCoeffFst sk i (t - z) ^ 2 + basisCoeffSnd sk i (t - z) ^ 2)] ≤
      ENNReal.ofReal (idealRejectBound p) := by
  rw [htree] at hleaves ⊢
  let : MeasurableSpace (FFTPair p.fftDepth) := ⊤
  have : DiscreteMeasurableSpace (FFTPair p.fftDepth) := ⟨fun _ => trivial⟩
  set μ := 𝒟[ffSamplingWith idealSamplerQuery p.fftDepth t (trueTree p sk)]
  have hK : (1 : ℝ) ≤ (1 + 1 / 2 ^ 36) ^ (4 * 2 ^ p.fftDepth) := one_le_pow₀ (by norm_num)
  have hη : 0 ≤ 1 + mgfSlack p.fftDepth := by
    have := Real.sqrt_nonneg ((1 + 1 / 2 ^ 36 : ℝ) ^ (4 * 2 ^ p.fftDepth) - 1)
    unfold mgfSlack
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 1 + (1 + 1 / 2 ^ 36) ^ (4 * 2 ^ p.fftDepth))
      this]
  have hsec : ∀ φ : FFTPair p.fftDepth → ℝ, FFTPairLinear φ →
      ∫⁻ z, ENNReal.ofReal (φ (t - z) ^ 2) ∂μ ≤
        ENNReal.ofReal ((trueTree p sk).devVar φ * (1 + mgfSlack p.fftDepth)) := fun φ hφ =>
    lintegral_sq_le_of_mgf μ (fun z => φ (t - z)) Measurable.of_discrete hK
      (FalconTree.devVar_nonneg _ _)
      (lintegral_exp_dev_le hσ p.fftDepth t (trueTree p sk) hleaves φ hφ)
  have hsplit : ∀ z, ENNReal.ofReal
      (∑ i, (basisCoeffFst sk i (t - z) ^ 2 + basisCoeffSnd sk i (t - z) ^ 2)) =
      ∑ i, (ENNReal.ofReal (basisCoeffFst sk i (t - z) ^ 2) +
        ENNReal.ofReal (basisCoeffSnd sk i (t - z) ^ 2)) := fun z => by
    rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => by positivity)]
    exact Finset.sum_congr rfl fun i _ => ENNReal.ofReal_add (sq_nonneg _) (sq_nonneg _)
  have hint : ∫⁻ z, ENNReal.ofReal
      (∑ i, (basisCoeffFst sk i (t - z) ^ 2 + basisCoeffSnd sk i (t - z) ^ 2)) ∂μ ≤
      ENNReal.ofReal (4 * 2 ^ p.fftDepth * p.sigma ^ 2 * (1 + mgfSlack p.fftDepth)) := by
    calc _ = ∑ i, (∫⁻ z, ENNReal.ofReal (basisCoeffFst sk i (t - z) ^ 2) ∂μ +
          ∫⁻ z, ENNReal.ofReal (basisCoeffSnd sk i (t - z) ^ 2) ∂μ) := by
          simp_rw [hsplit]
          rw [lintegral_finsetSum _ (fun i _ => Measurable.of_discrete)]
          exact Finset.sum_congr rfl fun i _ => lintegral_add_left Measurable.of_discrete _
      _ ≤ ∑ i, (ENNReal.ofReal ((trueTree p sk).devVar (basisCoeffFst sk i) *
            (1 + mgfSlack p.fftDepth)) + ENNReal.ofReal ((trueTree p sk).devVar
              (basisCoeffSnd sk i) * (1 + mgfSlack p.fftDepth))) :=
          Finset.sum_le_sum fun i _ => add_le_add (hsec _ (fftPairLinear_basisCoeffFst sk i))
            (hsec _ (fftPairLinear_basisCoeffSnd sk i))
      _ = ENNReal.ofReal ((∑ i, ((trueTree p sk).devVar (basisCoeffFst sk i) +
            (trueTree p sk).devVar (basisCoeffSnd sk i))) * (1 + mgfSlack p.fftDepth)) := by
          rw [Finset.sum_mul, ENNReal.ofReal_sum_of_nonneg (fun i _ => mul_nonneg
            (add_nonneg (FalconTree.devVar_nonneg _ _) (FalconTree.devVar_nonneg _ _)) hη)]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [add_mul, ENNReal.ofReal_add (mul_nonneg (FalconTree.devVar_nonneg _ _) hη)
            (mul_nonneg (FalconTree.devVar_nonneg _ _) hη)]
      _ = _ := by rw [sum_devVar_trueTree_basisCoeff hn hdepth sk hntru]
  have hB : 0 < (p.betaSquared : ℝ) + 1 := by positivity
  have hB0 : ENNReal.ofReal ((p.betaSquared : ℝ) + 1) ≠ 0 := (ENNReal.ofReal_pos.2 hB).ne'
  have hmk := mul_meas_ge_le_lintegral₀ (μ := μ) (Measurable.of_discrete (f := fun z =>
    ENNReal.ofReal (∑ i, (basisCoeffFst sk i (t - z) ^ 2 +
      basisCoeffSnd sk i (t - z) ^ 2)))).aemeasurable (ENNReal.ofReal ((p.betaSquared : ℝ) + 1))
  rw [prEvent_eq_evalDist_of_discrete]
  calc μ {z | (p.betaSquared : ℝ) + 1 ≤
        ∑ i, (basisCoeffFst sk i (t - z) ^ 2 + basisCoeffSnd sk i (t - z) ^ 2)}
      ≤ μ {z | ENNReal.ofReal ((p.betaSquared : ℝ) + 1) ≤ ENNReal.ofReal
          (∑ i, (basisCoeffFst sk i (t - z) ^ 2 + basisCoeffSnd sk i (t - z) ^ 2))} :=
        measure_mono fun z hz => ENNReal.ofReal_le_ofReal hz
    _ = (ENNReal.ofReal ((p.betaSquared : ℝ) + 1))⁻¹ * (ENNReal.ofReal ((p.betaSquared : ℝ) + 1) *
          μ {z | ENNReal.ofReal ((p.betaSquared : ℝ) + 1) ≤ ENNReal.ofReal
            (∑ i, (basisCoeffFst sk i (t - z) ^ 2 + basisCoeffSnd sk i (t - z) ^ 2))}) := by
        rw [← mul_assoc, ENNReal.inv_mul_cancel hB0 ENNReal.ofReal_ne_top, one_mul]
    _ ≤ (ENNReal.ofReal ((p.betaSquared : ℝ) + 1))⁻¹ *
          ENNReal.ofReal (4 * 2 ^ p.fftDepth * p.sigma ^ 2 * (1 + mgfSlack p.fftDepth)) := by
        gcongr
        exact hmk.trans hint
    _ = _ := by rw [idealRejectBound, ENNReal.ofReal_div_of_pos hB, ENNReal.div_eq_inv_mul]

end Falcon

end
