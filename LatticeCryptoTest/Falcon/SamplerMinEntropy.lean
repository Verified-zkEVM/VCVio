/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module
public import LatticeCrypto.Falcon.SamplerMinEntropy
public import LatticeCrypto.Falcon.Concrete.NTT
public import VCVio.OracleComp.Constructions.SampleableType.Basic
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Finite sampler witnesses and a modular point-mass counterexample

A fair bit gives a concrete finite leaf sampler with a nontrivial point-mass bound. The
resulting Falcon sampler satisfies the product bound without an exact Gaussian assumption.
A second fixture shows why a bound before modular reduction needs a fiber argument: two
distinct integers collapse to the same short residue, doubling its point mass.

The sampler laws are satisfiable and have content: a uniform draw from `{0, 1, 2, 3}` meets
`SamplerEnvelope 0` for Falcon-512, which gives the product bound a nontrivial instance, and
returning `round μ` meets `SamplerQuality` at every order `a > 1` with an explicit constant but
violates `SamplerEnvelope 0`.
-/

public section

open OracleComp OracleSpec MeasureTheory ProbabilityTheory Falcon LatticeCrypto InformationTheory
open scoped ENNReal

namespace LatticeCryptoTest.FalconSamplerMinEntropy

/-- A finite sampler with equal mass on zero and one. -/
def coinInt : ProbComp ℤ :=
  (fun bit : Bool => if bit then (1 : ℤ) else 0) <$> ($ᵗ Bool)

theorem coinInt_pointMass_le (v : ℤ) :
    Pr{let outcome ← coinInt}[outcome = v] ≤ (2 : ℝ≥0∞)⁻¹ := by
  rw [coinInt, prEvent_map, prEvent_eq_evalDist_of_discrete,
    SampleableType.evalDist_uniformSample, uniformOn_univ_apply_setOf]
  by_cases h0 : v = 0
  · subst v
    norm_num [Finset.filter_insert, Finset.filter_singleton]
  by_cases h1 : v = 1
  · subst v
    norm_num [Finset.filter_insert, Finset.filter_singleton]
  simp [Finset.filter_insert, Finset.filter_singleton, Ne.symm h0, Ne.symm h1]

/-- Only the leaf sampler is relevant to the product-bound theorem. -/
noncomputable def coinPrimitives : Primitives falcon512 where
  publicKeyBytes _ := default
  hashToPoint _ _ _ := 0
  samplerZ _ _ := coinInt
  fftTarget _ := 0
  fftInt _ := 0
  ifftRound _ := 0
  compress _ _ := none
  decompress _ _ := none
  nttOps := Falcon.Concrete.concreteNTTRingOps 9

/-- A concrete finite model satisfies the nontrivial product-bound hypotheses. -/
example (κ : ℕ) (target : FFTPair κ) (tree : FalconTree κ) (σmin σmax : ℝ)
    (hleaves : tree.LeavesIn σmin σmax) (output : FFTPair κ) :
    Pr{let outcome ← coinPrimitives.ffSampling κ target tree}[outcome = output] ≤
      (2 : ℝ≥0∞)⁻¹ ^ (4 * 2 ^ κ) :=
  coinPrimitives.ffSampling_pointMass_le
    (fun _ _ _ _ v => coinInt_pointMass_le v) κ target tree hleaves output

/-! ## The sampler laws are satisfiable and not trivial -/

/-- A uniform draw from `{0, 1, 2, 3}`. -/
def quarterInt : ProbComp ℤ :=
  (fun i : Fin 4 => (i : ℤ)) <$> ($ᵗ Fin 4)

theorem quarterInt_pointMass_le (v : ℤ) :
    Pr{let outcome ← quarterInt}[outcome = v] ≤ (4 : ℝ≥0∞)⁻¹ := by
  rw [quarterInt, prEvent_map, prEvent_eq_evalDist_of_discrete,
    SampleableType.evalDist_uniformSample, uniformOn_univ_apply_setOf]
  have hcard : (Finset.univ.filter fun i : Fin 4 => (i : ℤ) = v).card ≤ 1 :=
    Finset.card_le_one.2 fun i hi j hj => by
      simp only [Finset.mem_filter] at hi hj
      exact Fin.ext (by exact_mod_cast hi.2.trans hj.2.symm)
  simp only [Fintype.card_fin, Nat.cast_ofNat]
  calc ((Finset.univ.filter fun i : Fin 4 => (i : ℤ) = v).card : ℝ≥0∞) / 4 ≤ 1 / 4 := by
        gcongr; exact_mod_cast hcard
    _ = 4⁻¹ := one_div 4

/-- Only the leaf sampler differs from `coinPrimitives`. -/
noncomputable def quarterPrimitives : Primitives falcon512 :=
  { coinPrimitives with samplerZ := fun _ _ => quarterInt }

/-- `quarterInt` meets the Falcon-512 envelope with no slack: `σ' √(2π) - 1 ≤ 4` on
`[σ_min, σ_max]`. -/
theorem quarterPrimitives_samplerEnvelope : quarterPrimitives.SamplerEnvelope 0 := by
  refine ⟨fun _ σ' h1 h2 v => ?_⟩
  rw [add_zero]
  refine (quarterInt_pointMass_le v).trans ?_
  have h3 := falcon512_sigmaMin_sqrt_two_pi_ge_three
  have hσ : σ' * Real.sqrt (2 * Real.pi) ≤ 5 := by
    have hpi := Real.pi_lt_d2
    have hs : Real.sqrt (2 * Real.pi) ≤ 2.74 := by
      rw [Real.sqrt_le_left (by norm_num)]
      nlinarith
    have hmax : σ' ≤ 18205 / 10000 := h2
    calc σ' * Real.sqrt (2 * Real.pi) ≤ 18205 / 10000 * 2.74 :=
          mul_le_mul hmax hs (Real.sqrt_nonneg _) (by norm_num)
      _ ≤ 5 := by norm_num
  have hlo : 3 ≤ σ' * Real.sqrt (2 * Real.pi) :=
    h3.trans (mul_le_mul_of_nonneg_right h1 (Real.sqrt_nonneg _))
  rw [← ENNReal.ofReal_ofNat 4, ← ENNReal.ofReal_inv_of_pos (by norm_num)]
  exact ENNReal.ofReal_le_ofReal (by rw [inv_eq_one_div]; gcongr <;> linarith)

/-- A nontrivial instance of the product bound: `1/2` per leaf draw. -/
example (κ : ℕ) (target : FFTPair κ) (tree : FalconTree κ)
    (hleaves : tree.LeavesIn falcon512.sigmaMin falcon512.sigmaMax) (output : FFTPair κ) :
    Pr{let outcome ← quarterPrimitives.ffSampling κ target tree}[outcome = output] ≤
      (ENNReal.ofReal (1 / 2) + 0) ^ (4 * 2 ^ κ) :=
  quarterPrimitives.ffSampling_pointMass_le_half_add_pow falcon512_sigmaMin_sqrt_two_pi_ge_three
    quarterPrimitives_samplerEnvelope κ target tree hleaves output

/-- A sampler that returns the integer nearest the center. -/
noncomputable def roundPrimitives : Primitives falcon512 :=
  { coinPrimitives with samplerZ := fun μ _ => pure (round μ) }

private theorem discreteGaussianWeight_le_shift_round {σmin σmax σ μ : ℝ} (h0 : 0 < σmin)
    (h1 : σmin ≤ σ) (h2 : σ ≤ σmax) (k : ℤ) :
    discreteGaussianWeight σ μ k ≤
      Real.exp (1 / (8 * σmin ^ 2)) *
        discreteGaussianWeight (Real.sqrt 2 * σmax) 0 (k - round μ) := by
  have hσ : 0 < σ := h0.trans_le h1
  have hf := abs_sub_round μ
  set j : ℝ := (k : ℝ) - round μ
  set f : ℝ := μ - round μ
  have hkμ : (k : ℝ) - μ = j - f := by simp only [j, f]; ring
  have hA : j ^ 2 / 2 - 1 / 4 ≤ (j - f) ^ 2 := by nlinarith [sq_nonneg (j - 2 * f), abs_le.1 hf]
  rw [discreteGaussianWeight, discreteGaussianWeight, ← Real.exp_add]
  apply Real.exp_le_exp.2
  rw [hkμ, Int.cast_sub, sub_zero, mul_pow, Real.sq_sqrt zero_le_two]
  have e1 : -(j - f) ^ 2 / (2 * σ ^ 2) ≤ 1 / (8 * σ ^ 2) - j ^ 2 / (4 * σ ^ 2) := by
    rw [show 1 / (8 * σ ^ 2) - j ^ 2 / (4 * σ ^ 2) = -(j ^ 2 / 2 - 1 / 4) / (2 * σ ^ 2) by
      field_simp; ring]
    exact div_le_div_of_nonneg_right (by linarith) (by positivity)
  have e2 : 1 / (8 * σ ^ 2) ≤ 1 / (8 * σmin ^ 2) :=
    one_div_le_one_div_of_le (by positivity) (by nlinarith)
  have e3 : j ^ 2 / (4 * σmax ^ 2) ≤ j ^ 2 / (4 * σ ^ 2) :=
    div_le_div_of_nonneg_left (sq_nonneg j) (by positivity) (by nlinarith)
  have e4 : -((j : ℝ)) ^ 2 / (2 * (2 * σmax ^ 2)) = -(j ^ 2 / (4 * σmax ^ 2)) := by ring
  rw [show ((k : ℝ) - (round μ : ℤ)) = j from rfl, e4]
  linarith

private theorem discreteGaussianSum_le_uniform {σmin σmax σ : ℝ} (h0 : 0 < σmin) (h1 : σmin ≤ σ)
    (h2 : σ ≤ σmax) (μ : ℝ) :
    discreteGaussianSum σ μ ≤
      Real.exp (1 / (8 * σmin ^ 2)) * discreteGaussianSum (Real.sqrt 2 * σmax) 0 := by
  have hσmax : 0 < σmax := (h0.trans_le h1).trans_le h2
  have hsum := discreteGaussianSum_summable (Real.sqrt 2 * σmax) 0 (by positivity)
  calc discreteGaussianSum σ μ
      ≤ ∑' k : ℤ, Real.exp (1 / (8 * σmin ^ 2)) *
          discreteGaussianWeight (Real.sqrt 2 * σmax) 0 (k - round μ) :=
        Summable.tsum_le_tsum (discreteGaussianWeight_le_shift_round h0 h1 h2)
          (discreteGaussianSum_summable σ μ (h0.trans_le h1))
          (((Equiv.subRight (round μ)).summable_iff.2 hsum).mul_left _)
    _ = _ := by
      rw [tsum_mul_left, discreteGaussianSum]
      exact congrArg _ ((Equiv.subRight (round μ)).tsum_eq (discreteGaussianWeight _ 0))

/-- The point mass at `round μ` is at most an explicit multiple of `D_{ℤ,σ,μ}`, uniformly over
`μ` and `σ ∈ [σmin, σmax]`. -/
private theorem dirac_round_le_smul {σmin σmax σ : ℝ} (h0 : 0 < σmin) (h1 : σmin ≤ σ)
    (h2 : σ ≤ σmax) (μ : ℝ) :
    Measure.dirac (round μ) ≤ (Real.toNNReal (Real.exp (1 / (4 * σmin ^ 2)) *
      discreteGaussianSum (Real.sqrt 2 * σmax) 0)) • discreteGaussianMeasure σ μ := by
  have hσ : 0 < σ := h0.trans_le h1
  have hσmax : 0 < σmax := hσ.trans_le h2
  have hK := discreteGaussianSum_pos (Real.sqrt 2 * σmax) 0 (by positivity)
  set C := Real.exp (1 / (4 * σmin ^ 2)) * discreteGaussianSum (Real.sqrt 2 * σmax) 0
  have hw : Real.exp (-(1 / (8 * σmin ^ 2))) ≤ discreteGaussianWeight σ μ (round μ) := by
    have hsq : ((round μ : ℝ) - μ) ^ 2 ≤ 1 / 4 := by nlinarith [abs_le.1 (abs_sub_round μ)]
    refine Real.exp_le_exp.2 ?_
    rw [neg_div, neg_le_neg_iff, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_right hsq (sq_nonneg σmin), pow_le_pow_left₀ h0.le h1 2]
  have hmass : 1 ≤ C * discreteGaussianPMF σ μ (round μ) := by
    rw [discreteGaussianPMF, mul_div_assoc', le_div_iff₀ (discreteGaussianSum_pos σ μ hσ), one_mul]
    refine (discreteGaussianSum_le_uniform h0 h1 h2 μ).trans ?_
    calc Real.exp (1 / (8 * σmin ^ 2)) * discreteGaussianSum (Real.sqrt 2 * σmax) 0
        = C * Real.exp (-(1 / (8 * σmin ^ 2))) := by
          rw [mul_right_comm, ← Real.exp_add]; congr 2; field_simp; ring
      _ ≤ _ := by gcongr
  refine Measure.le_iff.2 fun s hs => ?_
  rw [Measure.smul_apply, Measure.dirac_apply' _ hs, ENNReal.smul_def, smul_eq_mul]
  by_cases hm : round μ ∈ s
  · rw [Set.indicator_of_mem hm, Pi.one_apply]
    calc (1 : ℝ≥0∞) ≤ ENNReal.ofReal (C * discreteGaussianPMF σ μ (round μ)) :=
          ENNReal.one_le_ofReal.2 hmass
      _ = C.toNNReal * discreteGaussianMeasure σ μ {round μ} := by
          rw [discreteGaussianMeasure_singleton, ENNReal.ofReal_mul (by positivity)]; rfl
      _ ≤ _ := by gcongr; exact Set.singleton_subset_iff.2 hm
  · simp [hm]

/-- `roundPrimitives` meets the forward Rényi law at every order `a > 1`, with an explicit
finite constant. -/
theorem roundPrimitives_samplerQuality {a : ℝ} (ha : 1 < a) :
    roundPrimitives.SamplerQuality a
      (ENNReal.ofReal (Real.exp (1 / (4 * falcon512.sigmaMin ^ 2)) *
        discreteGaussianSum (Real.sqrt 2 * falcon512.sigmaMax) 0) - 1) where
  one_lt := ha
  renyiDiv_le μ σ' h1 h2 := by
    have h0 : 0 < falcon512.sigmaMin := by
      rw [show falcon512.sigmaMin = (12778336969128337 : ℝ) / 10000000000000000 from rfl]
      norm_num
    have := isProbabilityMeasure_discreteGaussianMeasure σ' μ (h0.trans_le h1)
    change renyiDiv a 𝒟[(pure (round μ) : ProbComp ℤ)] _ ≤ _
    rw [evalDist_pure]
    refine (renyiDiv_le_of_le_smul ha (dirac_round_le_smul h0 h1 h2 μ)).trans ?_
    exact (le_add_tsub : ENNReal.ofReal _ ≤ 1 + (ENNReal.ofReal _ - 1))

/-- The envelope has content: at `δ = 0`, `roundPrimitives` violates it, so `SamplerQuality`
with a large `ε` does not give a slack-free envelope. -/
theorem not_roundPrimitives_samplerEnvelope_zero : ¬ roundPrimitives.SamplerEnvelope 0 := by
  intro h
  have hle : falcon512.sigmaMin ≤ falcon512.sigmaMax := by
    rw [show falcon512.sigmaMin = (12778336969128337 : ℝ) / 10000000000000000 from rfl,
      show falcon512.sigmaMax = (18205 : ℝ) / 10000 from rfl]
    norm_num
  have h3 := falcon512_sigmaMin_sqrt_two_pi_ge_three
  have hv := h.pointMass_le 0 falcon512.sigmaMin le_rfl hle (round (0 : ℝ))
  change Pr{let outcome ← (pure (round (0 : ℝ)) : ProbComp ℤ)}[outcome = round (0 : ℝ)] ≤ _ at hv
  rw [prEvent_pure, ite_eq_left rfl, add_zero] at hv
  have hreal : 1 / (falcon512.sigmaMin * Real.sqrt (2 * Real.pi) - 1) ≤ 1 / 2 :=
    one_div_le_one_div_of_le (by norm_num) (by linarith)
  have := hv.trans (ENNReal.ofReal_le_ofReal hreal)
  rw [← ENNReal.ofReal_one, ENNReal.ofReal_le_ofReal_iff (by norm_num)] at this
  norm_num at this

/-- A fair draw from two distinct representatives of residue zero. -/
def modularRepresentatives : ProbComp ℤ :=
  (fun bit : Bool => if bit then (12289 : ℤ) else 0) <$> ($ᵗ Bool)

example : Pr{let x ← modularRepresentatives}[x = 0] = (2 : ℝ≥0∞)⁻¹ := by
  rw [modularRepresentatives, prEvent_map, prEvent_eq_evalDist_of_discrete,
    SampleableType.evalDist_uniformSample, uniformOn_univ_apply_setOf]
  norm_num [Finset.filter_insert, Finset.filter_singleton]

/-- Modular reduction can increase point mass even when the output is the zero residue. -/
example : Pr{let x ← modularRepresentatives}[(x : ZMod 12289) = 0] = 1 := by
  rw [modularRepresentatives, prEvent_map, prEvent_eq_evalDist_of_discrete,
    SampleableType.evalDist_uniformSample]
  have hset : {bit : Bool | (((if bit then 12289 else 0) : ℤ) : ZMod 12289) = 0} =
      Set.univ := by
    ext bit
    cases bit <;> simp [show (12289 : ZMod 12289) = 0 from ZMod.natCast_self 12289]
  rw [hset]
  exact measure_univ

end LatticeCryptoTest.FalconSamplerMinEntropy
