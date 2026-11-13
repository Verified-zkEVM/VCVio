/-
Copyright (c) 2026 XC0R. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XC0R
-/

module
import all LatticeCrypto.Falcon.PackedFFT
import all LatticeCrypto.Falcon.SamplerMinEntropy
import LatticeCrypto.Falcon.FFTStagesL2
import LatticeCrypto.Falcon.Coset
public import LatticeCrypto.Falcon.Precision
public import LatticeCrypto.DiscreteGaussian.SubGaussian
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov

/-!
# The preimage tail of ffSampling with an ideal sampler

`preimageTailMass prims sk Z` is the largest probability, over hash targets, that `ffSampling`
with the ideal sampler returns a pair with a coefficient above `Z`. The sampled pair is `z = t - d`,
and the deviation `d` is a fixed linear image of the leaf deviations of the sampler calls: at a
node `d = (merge d_left - ℓ · merge d_right, merge d_right)`. Each leaf deviation is sub-Gaussian
with proxy its leaf `σ` given the earlier calls (`LatticeCrypto.Theta.lintegral_exp_le`), so a
linear functional `φ` of `d` has moment generating function at most
`(1 + 2⁻³⁶)^(4 · 2^κ) exp(s² devVar tree φ / 2)` (`lintegral_exp_dev_le`), for any tree with
leaves at least `1.277`, and the Chernoff bound `prob_abs_dev_ge_le` follows. Every output is the
packed FFT of an integer pair (`ffSamplingWith_idealSamplerQuery_ofCoeffs`), so a union bound over
the coefficients gives `preimageTailMass_le`, generic in `Z`: target coefficients at most `T`,
variance proxies at most `V`. `abs_coeff_toFFTTarget_le` bounds the target coefficients at the
exact FFT fields by `n · 12288 · 127 / q` for keys with coefficients in `[-127, 127]`.

Two lemmas discharge the other hypotheses of `idealExperiment_precision` against an exact bundle,
for any perturbed FFT fields: `slotsSqDist_toFFTTarget_le` bounds the squared target distance from
an `ℓ²` error of `fftTarget` and a slotwise error of `fftInt`, and `fromFFTPreimage_eq_of_exactFFT`
gives `hpost` from the rounding of the basis application to the lattice point.
-/

public section

open OracleComp OracleSpec LatticeCrypto MeasureTheory
open scoped ENNReal ComplexConjugate

namespace Falcon

variable {p : Params}

/-! ## Slotwise operations -/

namespace RealFFTPoly

variable {k : ℕ}

theorem coord_scaleFFT (c : ℝ) (v : RealFFTPoly k) (j : Fin (2 ^ k)) :
    coord (Primitives.scaleFFT c v) j = (c : ℂ) * coord v j := by
  apply Complex.ext <;> simp [Primitives.scaleFFT, re, im, get_eq_getElem]

theorem coord_zero (j : Fin (2 ^ k)) : coord (0 : RealFFTPoly k) j = 0 := by
  apply Complex.ext <;> simp [coord, re, im, get_eq_getElem]

/-- Two packed FFT polynomials agreeing on every even and odd slot are equal. -/
theorem ext_coord_two {a b : RealFFTPoly (k + 1)}
    (h : ∀ i : Fin (2 ^ k), coord a ⟨2 * i.1, by omega⟩ = coord b ⟨2 * i.1, by omega⟩ ∧
      coord a ⟨2 * i.1 + 1, by omega⟩ = coord b ⟨2 * i.1 + 1, by omega⟩) : a = b := by
  refine ext_coord fun j => ?_
  have hj := j.2
  have h2 := two_pow_succ_eq k
  rcases (show j.1 = 2 * (j.1 / 2) ∨ j.1 = 2 * (j.1 / 2) + 1 by omega) with he | he
  · have := (h ⟨j.1 / 2, by omega⟩).1
    rwa [show (⟨2 * (j.1 / 2), by omega⟩ : Fin (2 ^ (k + 1))) = j from Fin.ext he.symm] at this
  · have := (h ⟨j.1 / 2, by omega⟩).2
    rwa [show (⟨2 * (j.1 / 2) + 1, by omega⟩ : Fin (2 ^ (k + 1))) = j from Fin.ext he.symm] at this

theorem coord_mergeFFT_two (f₀ f₁ : RealFFTPoly k) (i : Fin (2 ^ k)) :
    coord (Primitives.mergeFFT f₀ f₁) ⟨2 * i.1, by omega⟩ =
        coord f₀ i + Complex.exp ((Primitives.splitAngle i : ℝ) * Complex.I) * coord f₁ i ∧
      coord (Primitives.mergeFFT f₀ f₁) ⟨2 * i.1 + 1, by omega⟩ =
        coord f₀ i - Complex.exp ((Primitives.splitAngle i : ℝ) * Complex.I) * coord f₁ i :=
  ⟨coord_mergeFFT_even f₀ f₁ i.1 i.2, coord_mergeFFT_odd f₀ f₁ i.1 i.2⟩

theorem mergeFFT_add (a b c d : RealFFTPoly k) :
    Primitives.mergeFFT (a + c) (b + d) = Primitives.mergeFFT a b + Primitives.mergeFFT c d := by
  refine ext_coord_two fun i => ?_
  simp only [coord_add, (coord_mergeFFT_two _ _ i).1, (coord_mergeFFT_two _ _ i).2]
  constructor <;> ring

theorem mergeFFT_sub (a b c d : RealFFTPoly k) :
    Primitives.mergeFFT (a - c) (b - d) = Primitives.mergeFFT a b - Primitives.mergeFFT c d := by
  refine ext_coord_two fun i => ?_
  simp only [coord_sub, (coord_mergeFFT_two _ _ i).1, (coord_mergeFFT_two _ _ i).2]
  constructor <;> ring

private theorem exp_mul_cos_neg_sin (θ : ℝ) :
    Complex.exp ((θ : ℂ) * Complex.I) * ⟨Real.cos θ, -Real.sin θ⟩ = 1 := by
  apply Complex.ext <;>
    simp [Complex.mul_re, Complex.mul_im, Complex.exp_ofReal_mul_I_re,
      Complex.exp_ofReal_mul_I_im]
  · nlinarith [Real.cos_sq_add_sin_sq θ]
  · ring

/-- `mergeFFT` inverts `splitFFT`. -/
theorem mergeFFT_splitFFT (f : RealFFTPoly (k + 1)) :
    Primitives.mergeFFT (Primitives.splitFFT f).1 (Primitives.splitFFT f).2 = f := by
  refine ext_coord_two fun i => ?_
  rw [(coord_mergeFFT_two _ _ i).1, (coord_mergeFFT_two _ _ i).2, coord_splitFFT_fst,
    coord_splitFFT_snd]
  have h := exp_mul_cos_neg_sin (Primitives.splitAngle i)
  constructor
  · linear_combination (coord f ⟨2 * i.1, by omega⟩ - coord f ⟨2 * i.1 + 1, by omega⟩) / 2 * h
  · linear_combination -(coord f ⟨2 * i.1, by omega⟩ - coord f ⟨2 * i.1 + 1, by omega⟩) / 2 * h

theorem splitFFT_add (f g : RealFFTPoly (k + 1)) :
    Primitives.splitFFT (f + g) = Primitives.splitFFT f + Primitives.splitFFT g := by
  refine Prod.ext (ext_coord fun i => ?_) (ext_coord fun i => ?_)
  · rw [Prod.fst_add, coord_add, coord_splitFFT_fst, coord_splitFFT_fst, coord_splitFFT_fst,
      coord_add, coord_add]
    ring
  · rw [Prod.snd_add, coord_add, coord_splitFFT_snd, coord_splitFFT_snd, coord_splitFFT_snd,
      coord_add, coord_add]
    ring

theorem splitFFT_scaleFFT (c : ℝ) (f : RealFFTPoly (k + 1)) :
    Primitives.splitFFT (Primitives.scaleFFT c f) =
      (Primitives.scaleFFT c (Primitives.splitFFT f).1,
        Primitives.scaleFFT c (Primitives.splitFFT f).2) := by
  refine Prod.ext (ext_coord fun i => ?_) (ext_coord fun i => ?_)
  · rw [coord_splitFFT_fst, coord_scaleFFT, coord_scaleFFT, coord_scaleFFT, coord_splitFFT_fst]
    ring
  · rw [coord_splitFFT_snd, coord_scaleFFT, coord_scaleFFT, coord_scaleFFT, coord_splitFFT_snd]
    ring

theorem toCoeffs_add : ∀ (k : ℕ) (x y : RealFFTPoly k) (i : Fin (2 * 2 ^ k)),
    toCoeffs k (x + y) i = toCoeffs k x i + toCoeffs k y i
  | 0, x, y, i => LatticeCrypto.Poly.get_add (Coeff := ℝ) x y i
  | k + 1, x, y, i => by
    simp only [toCoeffs, splitFFT_add, Prod.fst_add, Prod.snd_add]
    split_ifs <;> exact toCoeffs_add k _ _ _

theorem toCoeffs_scaleFFT : ∀ (k : ℕ) (c : ℝ) (x : RealFFTPoly k) (i : Fin (2 * 2 ^ k)),
    toCoeffs k (Primitives.scaleFFT c x) i = c * toCoeffs k x i
  | 0, c, x, i => by simp [toCoeffs, Primitives.scaleFFT]
  | k + 1, c, x, i => by
    simp only [toCoeffs, splitFFT_scaleFFT]
    split_ifs <;> exact toCoeffs_scaleFFT k c _ _

end RealFFTPoly

/-! ## Variance proxies along the tree -/

/-- A leaf pair with coordinates `(a, b)` and `(c, d)`. -/
@[expose] noncomputable def leafPair (a b c d : ℝ) : FFTPair 0 :=
  (RealFFTPoly.pack (Vector.ofFn fun _ => a) (Vector.ofFn fun _ => b),
    RealFFTPoly.pack (Vector.ofFn fun _ => c) (Vector.ofFn fun _ => d))

/-- `φ` is additive and commutes with scaling. -/
@[expose] def FFTPairLinear {κ : ℕ} (φ : FFTPair κ → ℝ) : Prop :=
  (∀ x y, φ (x + y) = φ x + φ y) ∧
    ∀ (c : ℝ) x, φ (Primitives.scaleFFT c x.1, Primitives.scaleFFT c x.2) = c * φ x

/-- **The variance proxy of a linear functional `φ` of the deviation `t - z`** of `ffSampling`
on `tree`: at a leaf `σ²` times the sum of the squared weights of the four coordinates; at a node
the proxies of `x ↦ φ (merge x, 0)` on the left subtree and of
`y ↦ φ (-ℓ · merge y, merge y)` on the right one. -/
@[expose] noncomputable def FalconTree.devVar : {κ : ℕ} → FalconTree κ → (FFTPair κ → ℝ) → ℝ
  | _, .leaf σ, φ => σ ^ 2 * (φ (leafPair 1 0 0 0) ^ 2 + φ (leafPair 0 1 0 0) ^ 2 +
      φ (leafPair 0 0 1 0) ^ 2 + φ (leafPair 0 0 0 1) ^ 2)
  | _, .node ℓ left right, φ =>
      left.devVar (fun x => φ (Primitives.mergeFFT x.1 x.2, 0)) +
        right.devVar (fun y => φ (-Primitives.mulFFT ℓ (Primitives.mergeFFT y.1 y.2),
          Primitives.mergeFFT y.1 y.2))

/-- Coefficient `i` of the first polynomial of a pair. -/
@[expose] noncomputable def coeffFst {κ : ℕ} (i : Fin (2 * 2 ^ κ)) (x : FFTPair κ) : ℝ :=
  RealFFTPoly.toCoeffs κ x.1 i

/-- Coefficient `i` of the second polynomial of a pair. -/
@[expose] noncomputable def coeffSnd {κ : ℕ} (i : Fin (2 * 2 ^ κ)) (x : FFTPair κ) : ℝ :=
  RealFFTPoly.toCoeffs κ x.2 i

theorem fftPairLinear_coeffFst {κ : ℕ} (i : Fin (2 * 2 ^ κ)) : FFTPairLinear (coeffFst i) :=
  ⟨fun x y => RealFFTPoly.toCoeffs_add κ x.1 y.1 i,
    fun c x => RealFFTPoly.toCoeffs_scaleFFT κ c x.1 i⟩

theorem fftPairLinear_coeffSnd {κ : ℕ} (i : Fin (2 * 2 ^ κ)) : FFTPairLinear (coeffSnd i) :=
  ⟨fun x y => RealFFTPoly.toCoeffs_add κ x.2 y.2 i,
    fun c x => RealFFTPoly.toCoeffs_scaleFFT κ c x.2 i⟩

/-! ## Moment generating functions along the tree -/

theorem FalconTree.devVar_nonneg : ∀ {κ : ℕ} (tree : FalconTree κ) (φ : FFTPair κ → ℝ),
    0 ≤ tree.devVar φ
  | _, .leaf _, _ => by rw [FalconTree.devVar]; positivity
  | _, .node _ left right, _ => by
    rw [FalconTree.devVar]
    exact add_nonneg (devVar_nonneg left _) (devVar_nonneg right _)

theorem slot_zero (j : Fin (2 ^ 0)) : j = ⟨0, by norm_num⟩ :=
  Fin.ext (by have := j.2; simp only [pow_zero, Nat.lt_one_iff] at this; exact this)

theorem sub_leafPair (t : FFTPair 0) (a b c d : ℝ) :
    t - leafPair a b c d = leafPair (RealFFTPoly.re t.1 ⟨0, by norm_num⟩ - a)
      (RealFFTPoly.im t.1 ⟨0, by norm_num⟩ - b) (RealFFTPoly.re t.2 ⟨0, by norm_num⟩ - c)
      (RealFFTPoly.im t.2 ⟨0, by norm_num⟩ - d) := by
  refine Prod.ext (RealFFTPoly.ext_coord fun j => ?_) (RealFFTPoly.ext_coord fun j => ?_) <;>
  · rw [slot_zero j]
    simp [leafPair, RealFFTPoly.coord_sub, RealFFTPoly.coord_pack, Complex.ext_iff]

theorem FFTPairLinear.leafPair {φ : FFTPair 0 → ℝ} (hφ : FFTPairLinear φ) (a b c d : ℝ) :
    φ (leafPair a b c d) = a * φ (leafPair 1 0 0 0) + b * φ (leafPair 0 1 0 0) +
      c * φ (leafPair 0 0 1 0) + d * φ (leafPair 0 0 0 1) := by
  have hdec : Falcon.leafPair a b c d =
      (((Primitives.scaleFFT a (Falcon.leafPair 1 0 0 0).1,
          Primitives.scaleFFT a (Falcon.leafPair 1 0 0 0).2) +
        (Primitives.scaleFFT b (Falcon.leafPair 0 1 0 0).1,
          Primitives.scaleFFT b (Falcon.leafPair 0 1 0 0).2)) +
        (Primitives.scaleFFT c (Falcon.leafPair 0 0 1 0).1,
          Primitives.scaleFFT c (Falcon.leafPair 0 0 1 0).2)) +
        (Primitives.scaleFFT d (Falcon.leafPair 0 0 0 1).1,
          Primitives.scaleFFT d (Falcon.leafPair 0 0 0 1).2) := by
    refine Prod.ext (RealFFTPoly.ext_coord fun j => ?_) (RealFFTPoly.ext_coord fun j => ?_) <;>
    · rw [slot_zero j]
      simp [Falcon.leafPair, RealFFTPoly.coord_add, RealFFTPoly.coord_scaleFFT,
        RealFFTPoly.coord_pack, Complex.ext_iff]
  rw [hdec, hφ.1, hφ.1, hφ.1, hφ.2, hφ.2, hφ.2, hφ.2]

theorem FFTPairLinear.map_sub {κ : ℕ} {φ : FFTPair κ → ℝ} (hφ : FFTPairLinear φ)
    (x y : FFTPair κ) : φ (x - y) = φ x - φ y := by
  have e : x - y + y = x := Prod.ext
    (RealFFTPoly.ext_coord fun j => by
      rw [Prod.fst_add, Prod.fst_sub, RealFFTPoly.coord_add, RealFFTPoly.coord_sub]; ring)
    (RealFFTPoly.ext_coord fun j => by
      rw [Prod.snd_add, Prod.snd_sub, RealFFTPoly.coord_add, RealFFTPoly.coord_sub]; ring)
  have h := hφ.1 (x - y) y
  rw [e] at h
  linarith

/-- `x ↦ φ (merge x, 0)`, the functional of the left subtree in `devVar`, is linear. -/
theorem FFTPairLinear.comp_mergeFFT_left {k : ℕ} {φ : FFTPair (k + 1) → ℝ}
    (hφ : FFTPairLinear φ) :
    FFTPairLinear fun x : FFTPair k => φ (Primitives.mergeFFT x.1 x.2, 0) := by
  refine ⟨fun x y => ?_, fun c x => ?_⟩
  · dsimp only
    rw [← hφ.1]
    congr 1
    refine Prod.ext ?_ ?_
    · simp only [Prod.fst_add, Prod.snd_add]
      exact RealFFTPoly.mergeFFT_add _ _ _ _
    · simp only [Prod.snd_add]
      exact RealFFTPoly.ext_coord fun j => by
        rw [RealFFTPoly.coord_add, RealFFTPoly.coord_zero]; ring
  · dsimp only
    rw [← hφ.2]
    congr 1
    refine Prod.ext (RealFFTPoly.ext_coord_two fun i => ?_)
      (RealFFTPoly.ext_coord fun j => ?_)
    · simp only [RealFFTPoly.coord_scaleFFT, (RealFFTPoly.coord_mergeFFT_two _ _ i).1,
        (RealFFTPoly.coord_mergeFFT_two _ _ i).2]
      constructor <;> ring
    · rw [RealFFTPoly.coord_scaleFFT, RealFFTPoly.coord_zero]; ring

/-- `y ↦ φ (-ℓ · merge y, merge y)`, the functional of the right subtree in `devVar`, is
linear. -/
theorem FFTPairLinear.comp_mergeFFT_right {k : ℕ} {φ : FFTPair (k + 1) → ℝ}
    (hφ : FFTPairLinear φ) (ℓ : RealFFTPoly (k + 1)) :
    FFTPairLinear fun y : FFTPair k =>
      φ (-Primitives.mulFFT ℓ (Primitives.mergeFFT y.1 y.2), Primitives.mergeFFT y.1 y.2) := by
  refine ⟨fun x y => ?_, fun c x => ?_⟩
  · dsimp only
    rw [← hφ.1]
    congr 1
    refine Prod.ext ?_ ?_
    · simp only [Prod.fst_add, Prod.snd_add, RealFFTPoly.mergeFFT_add]
      exact RealFFTPoly.ext_coord fun j => by
        rw [RealFFTPoly.coord_add, RealFFTPoly.coord_neg, RealFFTPoly.coord_neg,
          RealFFTPoly.coord_neg, RealFFTPoly.coord_mulFFT, RealFFTPoly.coord_mulFFT,
          RealFFTPoly.coord_mulFFT, RealFFTPoly.coord_add]
        ring
    · simp only [Prod.fst_add, Prod.snd_add]
      exact RealFFTPoly.mergeFFT_add _ _ _ _
  · dsimp only
    rw [← hφ.2]
    congr 1
    refine Prod.ext (RealFFTPoly.ext_coord_two fun i => ?_)
      (RealFFTPoly.ext_coord_two fun i => ?_)
    · simp only [RealFFTPoly.coord_scaleFFT, RealFFTPoly.coord_neg,
        RealFFTPoly.coord_mulFFT, (RealFFTPoly.coord_mergeFFT_two _ _ i).1,
        (RealFFTPoly.coord_mergeFFT_two _ _ i).2]
      constructor <;> ring
    · simp only [RealFFTPoly.coord_scaleFFT, (RealFFTPoly.coord_mergeFFT_two _ _ i).1,
        (RealFFTPoly.coord_mergeFFT_two _ _ i).2]
      constructor <;> ring

/-- One sampler call: a continuation whose moment is `exp(u(z - c))` times `B` gives the bound
`(1 + 2⁻³⁶) exp(σ²u²/2) B`. -/
theorem lintegral_idealSamplerQuery_bind_le {β : Type} [MeasurableSpace β] {σ c u : ℝ}
    (hσ : 1277 / 1000 ≤ σ) (g : ℤ → OracleComp (unifSpec + idealSamplerSpec) β)
    {F : β → ℝ≥0∞} (hF : Measurable F) {B : ℝ}
    (hg : ∀ z : ℤ, ∫⁻ x, F x ∂𝒟[g z] ≤ ENNReal.ofReal (Real.exp (u * (z - c)) * B)) :
    ∫⁻ x, F x ∂𝒟[idealSamplerQuery c σ >>= g] ≤
      ENNReal.ofReal ((1 + 1 / 2 ^ 36) * Real.exp (σ ^ 2 * u ^ 2 / 2) * B) := by
  have hσ0 : 0 < σ := by linarith
  obtain ⟨hT, hk⟩ := Theta.kappa_le_of_le σ hσ
  rw [evalDist_bind_of_discrete, Measure.lintegral_bind Measurable.of_discrete.aemeasurable
    hF.aemeasurable]
  have hq : 𝒟[idealSamplerQuery c σ] = discreteGaussianMeasure σ c := by
    rw [← idealSamplerMeasure_of_pos hσ0]; exact evalDist_idealSamplerQuery c σ
  calc _ ≤ ∫⁻ z, ENNReal.ofReal (Real.exp (u * (z - c))) * ENNReal.ofReal B
          ∂𝒟[idealSamplerQuery c σ] := lintegral_mono fun z =>
            (hg z).trans_eq (ENNReal.ofReal_mul (Real.exp_pos _).le)
    _ = (∫⁻ z, ENNReal.ofReal (Real.exp (u * (z - c))) ∂𝒟[idealSamplerQuery c σ]) *
          ENNReal.ofReal B := lintegral_mul_const _ Measurable.of_discrete
    _ ≤ ENNReal.ofReal (Theta.kappa σ * Real.exp (σ ^ 2 * u ^ 2 / 2)) * ENNReal.ofReal B := by
        gcongr
        rw [hq]
        exact Theta.lintegral_exp_le σ c u hσ0 hT
    _ ≤ ENNReal.ofReal ((1 + 1 / 2 ^ 36) * Real.exp (σ ^ 2 * u ^ 2 / 2)) * ENNReal.ofReal B := by
        gcongr
    _ = _ := (ENNReal.ofReal_mul (by positivity)).symm

/-- **The moment generating function of a linear functional of the deviation** of ffSampling with
the ideal sampler: `E[exp(s φ(t - z))] ≤ (1 + 2⁻³⁶)^(4 · 2^κ) exp(s² devVar tree φ / 2)`. -/
theorem lintegral_exp_dev_le {σlo σhi : ℝ} (hσlo : 1277 / 1000 ≤ σlo) :
    ∀ (κ : ℕ) [MeasurableSpace (FFTPair κ)] [DiscreteMeasurableSpace (FFTPair κ)]
      (t : FFTPair κ) (tree : FalconTree κ), tree.LeavesIn σlo σhi → ∀ (φ : FFTPair κ → ℝ),
      FFTPairLinear φ → ∀ s : ℝ,
      ∫⁻ z, ENNReal.ofReal (Real.exp (s * φ (t - z)))
          ∂𝒟[ffSamplingWith idealSamplerQuery κ t tree] ≤
        ENNReal.ofReal ((1 + 1 / 2 ^ 36) ^ (4 * 2 ^ κ) *
          Real.exp (s ^ 2 * tree.devVar φ / 2)) := by
  intro κ
  induction κ with
  | zero =>
    intro _ _ t tree hleaves φ hφ s
    match t, tree with
    | (t₀, t₁), .leaf σ =>
      obtain ⟨hσ, -⟩ : σlo ≤ σ ∧ σ ≤ σhi := hleaves
      have hσ' := hσlo.trans hσ
      set K : ℝ := 1 + 1 / 2 ^ 36
      set a := RealFFTPoly.re t₀ ⟨0, by norm_num⟩
      set b := RealFFTPoly.im t₀ ⟨0, by norm_num⟩
      set c := RealFFTPoly.re t₁ ⟨0, by norm_num⟩
      set d := RealFFTPoly.im t₁ ⟨0, by norm_num⟩
      set w₁ := φ (leafPair 1 0 0 0)
      set w₂ := φ (leafPair 0 1 0 0)
      set w₃ := φ (leafPair 0 0 1 0)
      set w₄ := φ (leafPair 0 0 0 1)
      set e₁ := Real.exp (σ ^ 2 * (-(s * w₁)) ^ 2 / 2)
      set e₂ := Real.exp (σ ^ 2 * (-(s * w₂)) ^ 2 / 2)
      set e₃ := Real.exp (σ ^ 2 * (-(s * w₃)) ^ 2 / 2)
      set e₄ := Real.exp (σ ^ 2 * (-(s * w₄)) ^ 2 / 2)
      have hF : Measurable fun z : FFTPair 0 => ENNReal.ofReal (Real.exp (s * φ ((t₀, t₁) - z))) :=
        Measurable.of_discrete
      have hdev : ∀ z₀ z₁ z₂ z₃ : ℤ, s * φ ((t₀, t₁) - leafPair z₀ z₁ z₂ z₃) =
          -(s * w₁) * (z₀ - a) + -(s * w₂) * (z₁ - b) + -(s * w₃) * (z₂ - c) +
            -(s * w₄) * (z₃ - d) := by
        intro z₀ z₁ z₂ z₃
        rw [sub_leafPair, hφ.leafPair]
        ring
      simp only [ffSamplingWith]
      refine (lintegral_idealSamplerQuery_bind_le hσ' _ hF (u := -(s * w₁))
        (B := K * e₂ * (K * e₃ * (K * e₄))) fun z₀ => ?_).trans (le_of_eq ?_)
      · refine (lintegral_idealSamplerQuery_bind_le hσ' _ hF
          (u := -(s * w₂))
          (B := K * e₃ * (K * e₄) * Real.exp (-(s * w₁) * (z₀ - a))) fun z₁ => ?_).trans
            (le_of_eq ?_)
        · refine (lintegral_idealSamplerQuery_bind_le hσ' _ hF
            (u := -(s * w₃)) (B := K * e₄ * (Real.exp (-(s * w₁) * (z₀ - a)) *
              Real.exp (-(s * w₂) * (z₁ - b)))) fun z₂ => ?_).trans
                (le_of_eq ?_)
          · refine (lintegral_idealSamplerQuery_bind_le hσ' _ hF
              (u := -(s * w₄))
              (B := Real.exp (-(s * w₁) * (z₀ - a)) * Real.exp (-(s * w₂) * (z₁ - b)) *
                Real.exp (-(s * w₃) * (z₂ - c))) fun z₃ => ?_).trans
                  (le_of_eq ?_)
            · rw [evalDist_pure, lintegral_dirac]
              refine le_of_eq (congrArg ENNReal.ofReal ?_)
              rw [show (RealFFTPoly.pack (Vector.ofFn fun _ => ((z₀ : ℤ) : ℝ))
                  (Vector.ofFn fun _ => ((z₁ : ℤ) : ℝ)),
                RealFFTPoly.pack (Vector.ofFn fun _ => ((z₂ : ℤ) : ℝ))
                  (Vector.ofFn fun _ => ((z₃ : ℤ) : ℝ))) = leafPair z₀ z₁ z₂ z₃ from rfl, hdev]
              simp only [← Real.exp_add]
              congr 1
              simp only [a, b, c, d]
              ring
            · congr 1; ring
          · congr 1; ring
        · congr 1; ring
      · congr 1
        rw [FalconTree.devVar]
        have : Real.exp (s ^ 2 * (σ ^ 2 * (w₁ ^ 2 + w₂ ^ 2 + w₃ ^ 2 + w₄ ^ 2)) / 2) =
            e₁ * e₂ * e₃ * e₄ := by
          simp only [e₁, e₂, e₃, e₄, ← Real.exp_add]
          ring_nf
        rw [this]
        ring
  | succ k ih =>
    intro _ _ t tree hleaves φ hφ s
    match t, tree with
    | (t₀, t₁), .node ℓ left right =>
      obtain ⟨hlo, hro⟩ : left.LeavesIn σlo σhi ∧ right.LeavesIn σlo σhi := hleaves
      let : MeasurableSpace (FFTPair k) := ⊤
      have : DiscreteMeasurableSpace (FFTPair k) := ⟨fun _ => trivial⟩
      set K : ℝ := 1 + 1 / 2 ^ 36
      set φL : FFTPair k → ℝ := fun x => φ (Primitives.mergeFFT x.1 x.2, 0)
      set φR : FFTPair k → ℝ := fun y => φ (-Primitives.mulFFT ℓ (Primitives.mergeFFT y.1 y.2),
        Primitives.mergeFFT y.1 y.2)
      have hφL : FFTPairLinear φL := hφ.comp_mergeFFT_left
      have hφR : FFTPairLinear φR := hφ.comp_mergeFFT_right ℓ
      have hsplit : ∀ (x : RealFFTPoly (k + 1)) (y : FFTPair k),
          Primitives.mergeFFT (Primitives.splitFFT x - y).1 (Primitives.splitFFT x - y).2 =
            x - Primitives.mergeFFT y.1 y.2 := fun x y => by
        rw [Prod.fst_sub, Prod.snd_sub, RealFFTPoly.mergeFFT_sub, RealFFTPoly.mergeFFT_splitFFT]
      have key : ∀ z₁ z₀ : FFTPair k, φ ((t₀, t₁) - (Primitives.mergeFFT z₀.1 z₀.2,
          Primitives.mergeFFT z₁.1 z₁.2)) =
          φL (Primitives.splitFFT (t₀ + Primitives.adjustTarget ℓ t₁
            (Primitives.mergeFFT z₁.1 z₁.2)) - z₀) + φR (Primitives.splitFFT t₁ - z₁) := by
        intro z₁ z₀
        simp only [φL, φR, hsplit]
        rw [← hφ.1]
        congr 1
        refine Prod.ext (RealFFTPoly.ext_coord fun j => ?_) (RealFFTPoly.ext_coord fun j => ?_)
        · simp only [Prod.fst_sub, Prod.fst_add, Primitives.adjustTarget, RealFFTPoly.coord_sub,
            RealFFTPoly.coord_add, RealFFTPoly.coord_neg, RealFFTPoly.coord_mulFFT]
          ring
        · simp only [Prod.snd_sub, Prod.snd_add, RealFFTPoly.coord_sub, RealFFTPoly.coord_add,
            RealFFTPoly.coord_zero]
          ring
      have hFm : ∀ (f : FFTPair (k + 1) → ℝ≥0∞), Measurable f := fun _ => Measurable.of_discrete
      simp only [ffSamplingWith]
      rw [evalDist_bind_of_discrete, Measure.lintegral_bind Measurable.of_discrete.aemeasurable
        (hFm _).aemeasurable]
      have hinner : ∀ z₁ : FFTPair k,
          ∫⁻ z, ENNReal.ofReal (Real.exp (s * φ ((t₀, t₁) - z)))
            ∂𝒟[ffSamplingWith idealSamplerQuery k (Primitives.splitFFT (t₀ +
              Primitives.adjustTarget ℓ t₁ (Primitives.mergeFFT z₁.1 z₁.2))) left >>= fun z₀ =>
                pure (Primitives.mergeFFT z₀.1 z₀.2, Primitives.mergeFFT z₁.1 z₁.2)] ≤
            ENNReal.ofReal (Real.exp (s * φR (Primitives.splitFFT t₁ - z₁))) *
              ENNReal.ofReal (K ^ (4 * 2 ^ k) * Real.exp (s ^ 2 * left.devVar φL / 2)) := by
        intro z₁
        rw [evalDist_bind_of_discrete, Measure.lintegral_bind Measurable.of_discrete.aemeasurable
          (hFm _).aemeasurable]
        simp only [evalDist_pure, lintegral_dirac, key, mul_add, Real.exp_add]
        calc _ = ∫⁻ z₀, ENNReal.ofReal (Real.exp (s * φL (Primitives.splitFFT (t₀ +
                Primitives.adjustTarget ℓ t₁ (Primitives.mergeFFT z₁.1 z₁.2)) - z₀))) *
                  ENNReal.ofReal (Real.exp (s * φR (Primitives.splitFFT t₁ - z₁)))
              ∂𝒟[ffSamplingWith idealSamplerQuery k (Primitives.splitFFT (t₀ +
                Primitives.adjustTarget ℓ t₁ (Primitives.mergeFFT z₁.1 z₁.2))) left] :=
              lintegral_congr fun z₀ => ENNReal.ofReal_mul (Real.exp_pos _).le
          _ = _ * _ := lintegral_mul_const _ Measurable.of_discrete
          _ ≤ _ := by
              rw [mul_comm]
              gcongr
              exact ih _ left hlo φL hφL s
      calc _ ≤ ∫⁻ z₁, ENNReal.ofReal (Real.exp (s * φR (Primitives.splitFFT t₁ - z₁))) *
              ENNReal.ofReal (K ^ (4 * 2 ^ k) * Real.exp (s ^ 2 * left.devVar φL / 2))
            ∂𝒟[ffSamplingWith idealSamplerQuery k (Primitives.splitFFT t₁) right] :=
            lintegral_mono hinner
        _ = _ * _ := lintegral_mul_const _ Measurable.of_discrete
        _ ≤ ENNReal.ofReal (K ^ (4 * 2 ^ k) * Real.exp (s ^ 2 * right.devVar φR / 2)) *
              ENNReal.ofReal (K ^ (4 * 2 ^ k) * Real.exp (s ^ 2 * left.devVar φL / 2)) := by
            gcongr
            exact ih _ right hro φR hφR s
        _ = _ := by
            rw [← ENNReal.ofReal_mul (by positivity), FalconTree.devVar]
            congr 1
            rw [show 4 * 2 ^ (k + 1) = 4 * 2 ^ k + 4 * 2 ^ k by ring, pow_add]
            simp only [mul_add, add_div, Real.exp_add]
            ring

/-- A Chernoff bound from a moment bound. -/
theorem measure_le_of_lintegral_exp {α : Type} [MeasurableSpace α] (μ : Measure α)
    (X : α → ℝ) (hX : Measurable X) (s a M : ℝ) (A : Set α) (hA : ∀ z ∈ A, a ≤ s * X z)
    (hM : ∫⁻ z, ENNReal.ofReal (Real.exp (s * X z)) ∂μ ≤ ENNReal.ofReal M) :
    μ A ≤ ENNReal.ofReal (M * Real.exp (-a)) := by
  have hm : Measurable fun z => ENNReal.ofReal (Real.exp (s * X z)) :=
    ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (hX.const_mul s))
  have hMk := mul_meas_ge_le_lintegral₀ hm.aemeasurable (μ := μ) (ENNReal.ofReal (Real.exp a))
  have hsub : A ⊆
      {z | ENNReal.ofReal (Real.exp a) ≤ ENNReal.ofReal (Real.exp (s * X z))} :=
    fun z hz => ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 (hA z hz))
  have h1 : ENNReal.ofReal (Real.exp a) * μ A ≤ ENNReal.ofReal M :=
    (by gcongr : _ ≤ ENNReal.ofReal (Real.exp a) * _).trans (hMk.trans hM)
  have he : ENNReal.ofReal (Real.exp (-a)) * ENNReal.ofReal (Real.exp a) = 1 := by
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add, neg_add_cancel, Real.exp_zero,
      ENNReal.ofReal_one]
  calc μ A = ENNReal.ofReal (Real.exp (-a)) * (ENNReal.ofReal (Real.exp a) * μ A) := by
        rw [← mul_assoc, he, one_mul]
    _ ≤ ENNReal.ofReal (Real.exp (-a)) * ENNReal.ofReal M := by gcongr
    _ = ENNReal.ofReal (M * Real.exp (-a)) := by
        rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, mul_comm]

/-! ## Tails -/

/-- **Sub-Gaussian deviation of ffSampling with the ideal sampler**, for any tree with leaves at
least `σlo ≥ 1.277`, any linear functional `φ` and any `V > 0` at least its variance proxy:
`Pr[|φ(t - z)| ≥ r] ≤ 2 (1 + 2⁻³⁶)^(4 · 2^κ) exp(-r² / (2V))`. -/
theorem prob_abs_dev_ge_le {σlo σhi : ℝ} (hσlo : 1277 / 1000 ≤ σlo) (κ : ℕ) (t : FFTPair κ)
    (tree : FalconTree κ) (hleaves : tree.LeavesIn σlo σhi) (φ : FFTPair κ → ℝ)
    (hφ : FFTPairLinear φ) {V : ℝ} (hV : tree.devVar φ ≤ V) (hV0 : 0 < V) {r : ℝ}
    (hr : 0 ≤ r) :
    Pr{let z ← ffSamplingWith idealSamplerQuery κ t tree}[r ≤ |φ (t - z)|] ≤
      ENNReal.ofReal (2 * (1 + 1 / 2 ^ 36) ^ (4 * 2 ^ κ) * Real.exp (-(r ^ 2 / (2 * V)))) := by
  let : MeasurableSpace (FFTPair κ) := ⊤
  have : DiscreteMeasurableSpace (FFTPair κ) := ⟨fun _ => trivial⟩
  set K : ℝ := (1 + 1 / 2 ^ 36) ^ (4 * 2 ^ κ)
  set μ := 𝒟[ffSamplingWith idealSamplerQuery κ t tree]
  rw [prEvent_eq_evalDist_of_discrete]
  have hmgf : ∀ s : ℝ, ∫⁻ z, ENNReal.ofReal (Real.exp (s * φ (t - z))) ∂μ ≤
      ENNReal.ofReal (K * Real.exp (s ^ 2 * V / 2)) := fun s =>
    (lintegral_exp_dev_le hσlo κ t tree hleaves φ hφ s).trans (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (by gcongr)) (by positivity)))
  have hexp : ∀ s : ℝ, s = r / V ∨ s = -(r / V) →
      Real.exp (s ^ 2 * V / 2) * Real.exp (-(r / V * r)) = Real.exp (-(r ^ 2 / (2 * V))) := by
    rintro s (rfl | rfl) <;>
    · rw [← Real.exp_add]
      congr 1
      field_simp
      ring
  have hrV : 0 ≤ r / V := div_nonneg hr hV0.le
  have hup := measure_le_of_lintegral_exp μ (fun z => φ (t - z)) Measurable.of_discrete (r / V)
    (r / V * r) (K * Real.exp ((r / V) ^ 2 * V / 2)) {z | r ≤ φ (t - z)}
    (fun z (hz : r ≤ φ (t - z)) => show r / V * r ≤ r / V * φ (t - z) from
      mul_le_mul_of_nonneg_left hz hrV) (hmgf _)
  have hlo := measure_le_of_lintegral_exp μ (fun z => φ (t - z)) Measurable.of_discrete
    (-(r / V)) (r / V * r) (K * Real.exp ((-(r / V)) ^ 2 * V / 2)) {z | r ≤ -φ (t - z)}
    (fun z (hz : r ≤ -φ (t - z)) => show r / V * r ≤ -(r / V) * φ (t - z) by
      rw [neg_mul, ← mul_neg]; exact mul_le_mul_of_nonneg_left hz hrV) (hmgf _)
  rw [mul_assoc, hexp _ (Or.inl rfl)] at hup
  rw [mul_assoc, hexp _ (Or.inr rfl)] at hlo
  have hsub : {z | r ≤ |φ (t - z)|} ⊆ {z | r ≤ φ (t - z)} ∪ {z | r ≤ -φ (t - z)} :=
    fun z (hz : r ≤ |φ (t - z)|) => (le_abs'.1 hz).elim
      (fun h => Or.inr (show r ≤ -φ (t - z) by linarith)) (fun h => Or.inl h)
  have h0 : 0 ≤ K * Real.exp (-(r ^ 2 / (2 * V))) := by positivity
  refine (measure_mono hsub).trans ((measure_union_le _ _).trans ?_)
  refine (add_le_add hup hlo).trans ?_
  rw [← ENNReal.ofReal_add h0 h0]
  exact ENNReal.ofReal_le_ofReal (by linarith)

/-- Every output of ffSampling with the ideal sampler is the packed FFT of a pair of integer
polynomials. -/
theorem ffSamplingWith_idealSamplerQuery_ofCoeffs (κ : ℕ) (t : FFTPair κ) (tree : FalconTree κ)
    (z : FFTPair κ) (hz : z ∈ support (ffSamplingWith idealSamplerQuery κ t tree)) :
    ∃ a b : Fin (2 * 2 ^ κ) → ℤ, z.1 = RealFFTPoly.ofCoeffs κ (fun i => (a i : ℝ)) ∧
      z.2 = RealFFTPoly.ofCoeffs κ (fun i => (b i : ℝ)) := by
  induction κ with
  | zero =>
    match t, tree with
    | (t₀, t₁), .leaf σ =>
      simp only [ffSamplingWith, mem_support_bind_iff, support_pure,
        Set.mem_singleton_iff] at hz
      obtain ⟨z₀Re, -, z₀Im, -, z₁Re, -, z₁Im, -, rfl⟩ := hz
      exact ⟨fun i => if i.1 = 0 then z₀Re else z₀Im, fun i => if i.1 = 0 then z₁Re else z₁Im,
        by simp [RealFFTPoly.ofCoeffs], by simp [RealFFTPoly.ofCoeffs]⟩
  | succ k ih =>
    match t, tree with
    | (t₀, t₁), .node ℓ left right =>
      simp only [ffSamplingWith, mem_support_bind_iff, support_pure,
        Set.mem_singleton_iff] at hz
      obtain ⟨z₁Split, hz₁, z₀Split, hz₀, rfl⟩ := hz
      obtain ⟨a₁, b₁, ea₁, eb₁⟩ := ih _ right z₁Split hz₁
      obtain ⟨a₀, b₀, ea₀, eb₀⟩ := ih _ left z₀Split hz₀
      refine ⟨RealFFTPoly.interleave k a₀ b₀, RealFFTPoly.interleave k a₁ b₁, ?_, ?_⟩
      · rw [RealFFTPoly.interleave_cast, RealFFTPoly.ofCoeffs_interleave, ← ea₀, ← eb₀]
      · rw [RealFFTPoly.interleave_cast, RealFFTPoly.ofCoeffs_interleave, ← ea₁, ← eb₁]

/-- **The preimage tail, generic in `Z`.** If every coefficient of the `ffSampling` targets is at
most `T ≤ Z` and every coefficient functional has variance proxy at most `V` under the key's tree
(with leaves at least `σlo ≥ 1.277`), then
`preimageTailMass ≤ 4 · 2^κ · 2 (1 + 2⁻³⁶)^(4 · 2^κ) · exp(-(Z - T)² / (2V))`. -/
theorem preimageTailMass_le (prims : Primitives p) (sk : SecretKey p) {σlo σhi : ℝ}
    (hσlo : 1277 / 1000 ≤ σlo) (hleaves : sk.tree.LeavesIn σlo σhi) (T V Z : ℝ) (hTZ : T ≤ Z)
    (htarget : ∀ c i, |coeffFst i (toFFTTarget p prims c sk)| ≤ T ∧
      |coeffSnd i (toFFTTarget p prims c sk)| ≤ T)
    (hvar : ∀ i, sk.tree.devVar (coeffFst i) ≤ V ∧ sk.tree.devVar (coeffSnd i) ≤ V)
    (hV0 : 0 < V) :
    preimageTailMass p prims sk Z ≤
      ENNReal.ofReal (4 * 2 ^ p.fftDepth * (2 * (1 + 1 / 2 ^ 36) ^ (4 * 2 ^ p.fftDepth)) *
        Real.exp (-((Z - T) ^ 2 / (2 * V)))) := by
  refine iSup_le fun c => ?_
  set κ := p.fftDepth
  set t := toFFTTarget p prims c sk
  set oa := ffSamplingWith idealSamplerQuery κ t sk.tree
  set B : ℝ := 2 * (1 + 1 / 2 ^ 36) ^ (4 * 2 ^ κ) * Real.exp (-((Z - T) ^ 2 / (2 * V)))
  let : MeasurableSpace (FFTPair κ) := ⊤
  have : DiscreteMeasurableSpace (FFTPair κ) := ⟨fun _ => trivial⟩
  have hev : ∀ i : Fin (2 * 2 ^ κ),
      𝒟[oa] {z | Z - T ≤ |coeffFst i (t - z)|} ≤ ENNReal.ofReal B ∧
        𝒟[oa] {z | Z - T ≤ |coeffSnd i (t - z)|} ≤ ENNReal.ofReal B := fun i => by
    constructor
    · rw [← prEvent_eq_evalDist_of_discrete]
      exact prob_abs_dev_ge_le hσlo κ t sk.tree hleaves _ (fftPairLinear_coeffFst i)
        (hvar i).1 hV0 (by linarith)
    · rw [← prEvent_eq_evalDist_of_discrete]
      exact prob_abs_dev_ge_le hσlo κ t sk.tree hleaves _ (fftPairLinear_coeffSnd i)
        (hvar i).2 hV0 (by linarith)
  have hmono : Pr{let z ← oa}[¬ PreimageCoeffsLe κ Z z] ≤
      Pr{let z ← oa}[∃ i, Z - T ≤ |coeffFst i (t - z)| ∨ Z - T ≤ |coeffSnd i (t - z)|] := by
    refine prEvent_mono_of_support oa _ _ fun z hz hbad => ?_
    obtain ⟨a, b, ha, hb⟩ := ffSamplingWith_idealSamplerQuery_ofCoeffs κ t sk.tree z hz
    have hza : ∀ i, coeffFst i z = a i := fun i => by
      rw [coeffFst, ha, RealFFTPoly.toCoeffs_ofCoeffs]
    have hzb : ∀ i, coeffSnd i z = b i := fun i => by
      rw [coeffSnd, hb, RealFFTPoly.toCoeffs_ofCoeffs]
    by_contra hall
    push Not at hall
    refine hbad ⟨a, b, fun i => ?_, fun i => ?_, ha, hb⟩
    · have h1 := (hall i).1
      have h2 := (htarget c i).1
      rw [(fftPairLinear_coeffFst i).map_sub, hza] at h1
      have := abs_sub_abs_le_abs_sub (a i : ℝ) (coeffFst i t)
      rw [abs_sub_comm] at h1
      linarith
    · have h1 := (hall i).2
      have h2 := (htarget c i).2
      rw [(fftPairLinear_coeffSnd i).map_sub, hzb] at h1
      have := abs_sub_abs_le_abs_sub (b i : ℝ) (coeffSnd i t)
      rw [abs_sub_comm] at h1
      linarith
  refine hmono.trans ?_
  rw [prEvent_eq_evalDist_of_discrete]
  have hset : {z : FFTPair κ | ∃ i, Z - T ≤ |coeffFst i (t - z)| ∨
      Z - T ≤ |coeffSnd i (t - z)|} = ⋃ i, ({z | Z - T ≤ |coeffFst i (t - z)|} ∪
        {z | Z - T ≤ |coeffSnd i (t - z)|}) := by
    ext z; simp
  rw [hset]
  refine (measure_iUnion_fintype_le _ _).trans ?_
  calc ∑ i, 𝒟[oa] ({z | Z - T ≤ |coeffFst i (t - z)|} ∪ {z | Z - T ≤ |coeffSnd i (t - z)|})
      ≤ ∑ _i : Fin (2 * 2 ^ κ), (ENNReal.ofReal B + ENNReal.ofReal B) :=
        Finset.sum_le_sum fun i _ => (measure_union_le _ _).trans (add_le_add (hev i).1 (hev i).2)
    _ = _ := by
        have hB : 0 ≤ B := by positivity
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
          ← ENNReal.ofReal_add hB hB, ← ENNReal.ofReal_natCast,
          ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        simp only [B]
        push_cast
        ring

/-- A negacyclic convolution coefficient of `f` and `g` bounded by `A` and `B` is at most
`n A B`: each `f i` meets exactly one `g j` at a given coefficient. -/
theorem abs_negacyclicConvCoeff_le {n : ℕ} (f g : Fin n → ℝ) {A B : ℝ} (hf : ∀ i, |f i| ≤ A)
    (hg : ∀ j, |g j| ≤ B) (k : Fin n) : |negacyclicConvCoeff f g k| ≤ n * (A * B) := by
  have hB : 0 ≤ B := (abs_nonneg _).trans (hg k)
  have hinner : ∀ i : Fin n, ∑ j : Fin n, (if (i.1 + j.1) % n = k.1 then |f i| * |g j| else 0) ≤
      |f i| * B := fun i => by
    rw [← Finset.sum_filter]
    have hcard : (Finset.univ.filter fun j : Fin n => (i.1 + j.1) % n = k.1).card ≤ 1 := by
      refine Finset.card_le_one.2 fun a ha b hb => Fin.ext ?_
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
      have h : a.1 ≡ b.1 [MOD n] := Nat.ModEq.add_left_cancel' i.1 (ha.trans hb.symm)
      rwa [Nat.ModEq, Nat.mod_eq_of_lt a.2, Nat.mod_eq_of_lt b.2] at h
    calc _ ≤ ∑ _j ∈ Finset.univ.filter fun j : Fin n => (i.1 + j.1) % n = k.1, |f i| * B :=
          Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hg j) (abs_nonneg _)
      _ = _ * (|f i| * B) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ 1 * (|f i| * B) := mul_le_mul_of_nonneg_right (by exact_mod_cast hcard)
          (mul_nonneg (abs_nonneg _) hB)
      _ = _ := one_mul _
  unfold negacyclicConvCoeff
  calc _ ≤ ∑ ij : Fin n × Fin n, |if (ij.1.val + ij.2.val) % n = k.val then
          (if ij.1.val + ij.2.val < n then f ij.1 * g ij.2 else -(f ij.1 * g ij.2)) else 0| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ ij : Fin n × Fin n,
          (if (ij.1.val + ij.2.val) % n = k.val then |f ij.1| * |g ij.2| else 0) :=
        Finset.sum_le_sum fun ij _ => by split_ifs <;> simp [abs_mul]
    _ = ∑ i : Fin n, ∑ j : Fin n, (if (i.1 + j.1) % n = k.1 then |f i| * |g j| else 0) :=
        Fintype.sum_prod_type _
    _ ≤ ∑ i : Fin n, |f i| * B := Finset.sum_le_sum fun i _ => hinner i
    _ ≤ ∑ _i : Fin n, A * B := Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (hf i) hB
    _ = n * (A * B) := by simp

/-- The coefficients of the exact `ffSampling` targets of a hash target, for keys with
coefficients in `[-127, 127]`, are at most `n · 12288 · 127 / q`. -/
theorem abs_coeff_toFFTTarget_le (hn : 2 * 2 ^ p.fftDepth = p.n) (prims : Primitives p)
    (hfft : prims.fftInt = Primitives.exactFftInt p)
    (htgt : prims.fftTarget = Primitives.exactFftTarget p) (sk : SecretKey p)
    (hkey : ∀ i, |sk.f.get i| ≤ 127 ∧ |sk.capF.get i| ≤ 127) (c : Rq p.n)
    (i : Fin (2 * 2 ^ p.fftDepth)) :
    |coeffFst i (toFFTTarget p prims c sk)| ≤ p.n * 12288 * 127 / 12289 ∧
      |coeffSnd i (toFFTTarget p prims c sk)| ≤ p.n * 12288 * 127 / 12289 := by
  have hq : ((modulus : ℕ) : ℝ) = 12289 := by norm_num [modulus]
  have hC : ∀ j : Fin (2 * 2 ^ p.fftDepth), |(((c.get (Fin.cast hn j)).val : ℕ) : ℝ)| ≤ 12288 :=
    fun j => by
      have hlt : (c.get (Fin.cast hn j)).val < 12289 := ZMod.val_lt _
      rw [abs_of_nonneg (by positivity)]
      exact_mod_cast (show (c.get (Fin.cast hn j)).val ≤ 12288 by omega)
  have hF : ∀ j : Fin (2 * 2 ^ p.fftDepth), |((-sk.capF).get (Fin.cast hn j) : ℝ)| ≤ 127 :=
    fun j => by rw [Poly.get_neg, Int.cast_neg, abs_neg]; exact_mod_cast (hkey _).2
  have hf : ∀ j : Fin (2 * 2 ^ p.fftDepth), |((-sk.f).get (Fin.cast hn j) : ℝ)| ≤ 127 :=
    fun j => by rw [Poly.get_neg, Int.cast_neg, abs_neg]; exact_mod_cast (hkey _).1
  have htg : prims.fftTarget c = RealFFTPoly.ofCoeffs p.fftDepth
      fun j => (((c.get (Fin.cast hn j)).val : ℕ) : ℝ) := by
    simp [htgt, Primitives.exactFftTarget, hn]
  have hn' : (p.n : ℝ) = 2 * 2 ^ p.fftDepth := by rw [← hn]; push_cast; ring
  simp only [coeffFst, coeffSnd, toFFTTarget, RealFFTPoly.toCoeffs_scaleFFT, htg, hfft,
    Primitives.exactFftInt_eq p hn, ← RealFFTPoly.ofCoeffs_negacyclic,
    RealFFTPoly.toCoeffs_ofCoeffs, abs_mul]
  rw [hq, hn']
  constructor
  · calc |1 / (12289 : ℝ)| * |negacyclicConvCoeff _ _ i| ≤ 1 / 12289 *
          ((2 * 2 ^ p.fftDepth : ℕ) * (12288 * 127)) := by
          rw [abs_of_pos (by norm_num)]
          gcongr
          exact abs_negacyclicConvCoeff_le _ _ hC hF i
      _ = _ := by push_cast; ring
  · calc |-(1 / (12289 : ℝ))| * |negacyclicConvCoeff _ _ i| ≤ 1 / 12289 *
          ((2 * 2 ^ p.fftDepth : ℕ) * (127 * 12288)) := by
          rw [abs_neg, abs_of_pos (by norm_num)]
          gcongr
          exact abs_negacyclicConvCoeff_le _ _ hf hC i
      _ = _ := by push_cast; ring


/-! ## The targets from the errors of the FFT fields -/

/-- **The `ffSampling` targets from the errors of the FFT fields.** Let `prims` compute `fftInt`
and `fftTarget` exactly, and let `primsB` compute `fftTarget` within `L` of the exact packed FFT in
`ℓ²` and `fftInt` within `e` slot by slot on polynomials with coefficients in `[-127, 127]`. For
keys with `f` and `F` in `[-127, 127]`, the two `toFFTTarget` are within squared slotwise distance
`2 · ((L · (2^(k+1) · 127 + e) + 2^k · 17379 · e) / q)²`, `k = logn - 1`. -/
theorem slotsSqDist_toFFTTarget_le (hn : 2 * 2 ^ p.fftDepth = p.n) (prims primsB : Primitives p)
    (hfft : ∀ u : IntPoly p.n,
      prims.fftInt u = RealFFTPoly.ofCoeffs p.fftDepth fun i => (u.get (Fin.cast hn i) : ℝ))
    (htgt : ∀ c : Rq p.n, prims.fftTarget c =
      RealFFTPoly.ofCoeffs p.fftDepth fun i => (((c.get (Fin.cast hn i)).val : ℕ) : ℝ))
    {L e : ℝ} (hL : 0 ≤ L) (he : 0 ≤ e)
    (htB : ∀ c : Rq p.n, ∑ j, ‖RealFFTPoly.coord (primsB.fftTarget c) j -
      RealFFTPoly.coord (prims.fftTarget c) j‖ ^ 2 ≤ L ^ 2)
    (hiB : ∀ u : IntPoly p.n, (∀ i, |u.get i| ≤ 127) → ∀ j,
      ‖RealFFTPoly.coord (primsB.fftInt u) j - RealFFTPoly.coord (prims.fftInt u) j‖ ≤ e)
    (sk : SecretKey p) (hkey : ∀ i, |sk.f.get i| ≤ 127 ∧ |sk.capF.get i| ≤ 127) (c : Rq p.n) :
    slotsSqDist (toFFTTarget p primsB c sk).1 (toFFTTarget p prims c sk).1 +
      slotsSqDist (toFFTTarget p primsB c sk).2 (toFFTTarget p prims c sk).2 ≤
      2 * ((L * (2 ^ (p.fftDepth + 1) * 127 + e) + 2 ^ p.fftDepth * 17379 * e) / 12289) ^ 2 := by
  have hq : ((modulus : ℕ) : ℝ) = 12289 := by norm_num [modulus]
  have hTn : ∑ j, ‖RealFFTPoly.coord (prims.fftTarget c) j‖ ^ 2 ≤ (2 ^ p.fftDepth * 17379) ^ 2 := by
    rw [htgt, FFTStages.sum_norm_coord_ofCoeffs_sq]
    have hc : ∀ i : Fin (2 * 2 ^ p.fftDepth),
        (((c.get (Fin.cast hn i)).val : ℕ) : ℝ) ^ 2 ≤ 12288 ^ 2 := fun i => by
      have hlt : (c.get (Fin.cast hn i)).val < 12289 := ZMod.val_lt _
      exact pow_le_pow_left₀ (Nat.cast_nonneg _) (by exact_mod_cast (show
        (c.get (Fin.cast hn i)).val ≤ 12288 by omega)) 2
    calc _ ≤ 2 ^ p.fftDepth * ∑ _i : Fin (2 * 2 ^ p.fftDepth), (12288 : ℝ) ^ 2 :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => hc i) (by positivity)
      _ ≤ _ := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          push_cast
          nlinarith [pow_pos (by norm_num : (0 : ℝ) < 2) p.fftDepth]
  have hF : ∀ u : IntPoly p.n, (∀ i, |u.get i| ≤ 127) → ∀ j,
      ‖RealFFTPoly.coord (primsB.fftInt u) j‖ ≤ 2 ^ (p.fftDepth + 1) * 127 + e := by
    intro u hu j
    have h1 : ‖RealFFTPoly.coord (prims.fftInt u) j‖ ≤ 2 ^ (p.fftDepth + 1) * 127 := by
      rw [hfft]
      exact RealFFTPoly.norm_coord_ofCoeffs_le p.fftDepth _ 127 (fun i => by exact_mod_cast hu _) j
    calc _ ≤ ‖RealFFTPoly.coord (prims.fftInt u) j‖ + ‖RealFFTPoly.coord (primsB.fftInt u) j -
          RealFFTPoly.coord (prims.fftInt u) j‖ := norm_le_insert' _ _
      _ ≤ _ := add_le_add h1 (hiB u hu j)
  have key : ∀ s : ℝ, |s| = 1 / 12289 → ∀ u : IntPoly p.n, (∀ i, |u.get i| ≤ 127) →
      ∀ Xh X : Fin (2 ^ p.fftDepth) → ℂ,
      (∀ j, Xh j - X j = RealFFTPoly.coord (primsB.fftTarget c) j *
          RealFFTPoly.coord (primsB.fftInt u) j -
        RealFFTPoly.coord (prims.fftTarget c) j * RealFFTPoly.coord (prims.fftInt u) j) →
      ∑ j, ‖(s : ℂ) * Xh j - (s : ℂ) * X j‖ ^ 2 ≤
        ((L * (2 ^ (p.fftDepth + 1) * 127 + e) + 2 ^ p.fftDepth * 17379 * e) / 12289) ^ 2 := by
    intro s hs u hu Xh X hX
    have hprod := FFTStages.sum_sq_mul_sub_le _ _ _ _ L (2 ^ p.fftDepth * 17379)
      (2 ^ (p.fftDepth + 1) * 127 + e) e hL (by positivity) (by positivity) he (htB c) hTn
      (hF u hu) (hiB u hu)
    calc ∑ j, ‖(s : ℂ) * Xh j - (s : ℂ) * X j‖ ^ 2 = s ^ 2 * ∑ j, ‖Xh j - X j‖ ^ 2 := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [← mul_sub, norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]
      _ ≤ s ^ 2 * (L * (2 ^ (p.fftDepth + 1) * 127 + e) + 2 ^ p.fftDepth * 17379 * e) ^ 2 := by
          simp only [hX]
          exact mul_le_mul_of_nonneg_left hprod (sq_nonneg _)
      _ = _ := by rw [← sq_abs s, hs]; ring
  have hnF : ∀ i, |(-sk.capF).get i| ≤ 127 := fun i => by
    rw [Poly.get_neg, abs_neg]; exact (hkey i).2
  have hnf : ∀ i, |(-sk.f).get i| ≤ 127 := fun i => by
    rw [Poly.get_neg, abs_neg]; exact (hkey i).1
  have hs1 : |1 / ((modulus : ℕ) : ℝ)| = 1 / 12289 := by rw [hq]; norm_num
  have hs2 : |-(1 / ((modulus : ℕ) : ℝ))| = 1 / 12289 := by rw [abs_neg, hq]; norm_num
  simp only [slotsSqDist, toFFTTarget, RealFFTPoly.coord_scaleFFT, RealFFTPoly.coord_mulFFT]
  calc _ ≤ ((L * (2 ^ (p.fftDepth + 1) * 127 + e) + 2 ^ p.fftDepth * 17379 * e) / 12289) ^ 2 +
        ((L * (2 ^ (p.fftDepth + 1) * 127 + e) + 2 ^ p.fftDepth * 17379 * e) / 12289) ^ 2 :=
        add_le_add (key _ hs1 _ hnF _ _ fun j => rfl) (key _ hs2 _ hnf _ _ fun j => by ring)
    _ = _ := by ring


/-- **`fromFFTPreimage` against an exact bundle.** If `prims` computes the FFT fields exactly and
the basis application of `primsB` on the packed FFT of every integer pair with coefficients at most
`Z` rounds to the lattice point of that pair, the two bundles' `fromFFTPreimage` agree on such
pairs. -/
theorem fromFFTPreimage_eq_of_exactFFT (hn : 2 * 2 ^ p.fftDepth = p.n)
    (prims primsB : Primitives p) (hex : prims.ExactFFT hn) (sk : SecretKey p) (Z : ℝ)
    (hB : ∀ a b : Fin (2 * 2 ^ p.fftDepth) → ℤ, (∀ i, |(a i : ℝ)| ≤ Z) →
      (∀ i, |(b i : ℝ)| ≤ Z) →
      primsB.ifftRound (Primitives.mulFFT (RealFFTPoly.ofCoeffs p.fftDepth fun i => (a i : ℝ))
          (primsB.fftInt sk.g) +
        Primitives.mulFFT (RealFFTPoly.ofCoeffs p.fftDepth fun i => (b i : ℝ))
          (primsB.fftInt sk.capG)) =
        intPolyMul (Poly.ofPi fun i => a (Fin.cast hn.symm i)) sk.g +
          intPolyMul (Poly.ofPi fun i => b (Fin.cast hn.symm i)) sk.capG ∧
      primsB.ifftRound (-(Primitives.mulFFT (RealFFTPoly.ofCoeffs p.fftDepth fun i => (a i : ℝ))
          (primsB.fftInt sk.f) +
        Primitives.mulFFT (RealFFTPoly.ofCoeffs p.fftDepth fun i => (b i : ℝ))
          (primsB.fftInt sk.capF))) =
        -(intPolyMul (Poly.ofPi fun i => a (Fin.cast hn.symm i)) sk.f +
          intPolyMul (Poly.ofPi fun i => b (Fin.cast hn.symm i)) sk.capF))
    (c : Rq p.n) (z : FFTPair p.fftDepth) (hz : PreimageCoeffsLe p.fftDepth Z z) :
    fromFFTPreimage p primsB c sk z = fromFFTPreimage p prims c sk z := by
  obtain ⟨z₁, z₂⟩ := z
  obtain ⟨a, b, ha, hb, rfl, rfl⟩ := hz
  obtain ⟨hB0, hB1⟩ := hB a b ha hb
  have hX0 : prims.ifftRound
      (Primitives.mulFFT (RealFFTPoly.ofCoeffs p.fftDepth fun i => (a i : ℝ)) (prims.fftInt sk.g) +
        Primitives.mulFFT (RealFFTPoly.ofCoeffs p.fftDepth fun i => (b i : ℝ))
          (prims.fftInt sk.capG)) =
      intPolyMul (Poly.ofPi fun i => a (Fin.cast hn.symm i)) sk.g +
        intPolyMul (Poly.ofPi fun i => b (Fin.cast hn.symm i)) sk.capG := by
    rw [hex.fftInt_eq, hex.fftInt_eq, ← ofCoeffs_latticePoint p hn a b sk.g sk.capG,
      hex.ifftRound_eq, RealFFTPoly.toCoeffs_ofCoeffs]
    apply Poly.ext_get_eq
    intro i
    simp [round_intCast]
  have hX1 : prims.ifftRound
      (-(Primitives.mulFFT (RealFFTPoly.ofCoeffs p.fftDepth fun i => (a i : ℝ))
          (prims.fftInt sk.f) +
        Primitives.mulFFT (RealFFTPoly.ofCoeffs p.fftDepth fun i => (b i : ℝ))
          (prims.fftInt sk.capF))) =
      -(intPolyMul (Poly.ofPi fun i => a (Fin.cast hn.symm i)) sk.f +
        intPolyMul (Poly.ofPi fun i => b (Fin.cast hn.symm i)) sk.capF) := by
    rw [hex.fftInt_eq, hex.fftInt_eq, ← ofCoeffs_latticePoint p hn a b sk.f sk.capF,
      ← RealFFTPoly.ofCoeffs_neg, hex.ifftRound_eq, RealFFTPoly.toCoeffs_ofCoeffs]
    apply Poly.ext_get_eq
    intro i
    rw [Poly.get_ofPi, Poly.get_neg, Fin.cast_cast, Fin.cast_eq_self, ← Int.cast_neg,
      round_intCast]
  simp only [fromFFTPreimage, hB0, hB1, hX0, hX1]

end Falcon
