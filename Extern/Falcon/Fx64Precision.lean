/-
Copyright (c) 2026 XC0R. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XC0R
-/

module
import all Extern.Falcon.Instance
import all Extern.Falcon.Fx64Coset
public import Extern.Falcon.Fx64Coset
public import LatticeCrypto.Falcon.PrecisionTrueTree

/-!
# Rényi precision transfer at the fixed-point FFT primitives

`fx64FFTPrimitives A p hn` and `concretePrimitives p hn` share hash, public-key encoding and
compression, and differ in the three FFT fields: fixed point with 64 fractional bits against the
exact packed FFT. This file discharges the hypotheses of `Falcon.idealExperiment_precision` for
that pair:

* with key coefficients in `[-127, 127]`, the two `ffSampling` targets `toFFTTarget` are within
  squared slotwise distance `fx64TargetSqDeviation (logn - 1)` (`slotsSqDist_toFFTTarget_fx64`);
  `fx64TargetSqDeviation_falcon512` evaluates it below `1/(4 · 10^21)` at Falcon-512;
* on sampled pairs with coefficients at most `Z`, `fromFFTPreimage` agrees whenever
  `fx64CosetDeviation (logn - 1) Z < 1/2` (`fromFFTPreimage_fx64_eq`).

`idealExperiment_fx64_precision` is the transfer for `2 ≤ logn`, and
`idealExperiment_fx64_precision_falcon512` its Falcon-512 instance at `λ = 128`, `Z = 2^33`, for
keys satisfying the NTRU equation whose tree is the true tree with leaves in `[σmin, σmax]`, root
factor slots at most `24.0001` and the other factor slots at most `0.9923`, when
`K · maxAttempts ≤ 2^53` (`fx64_falcon512_budget`). Its additive term is
`K · maxAttempts · 2⁻¹⁰⁰⁰`, from `preimageTailMass_falcon512_two_pow_33_le`.

## What is not proved

* The sampler is ideal on both sides: every `samplerZ` call is answered by the discrete Gaussian.
* `Falcon.FixedPoint.Arith64` is a model, a structure of rounding functions with error bounds; no
  executable 64.64 fixed-point code is related to it here.
* Register overflow is not represented: nothing here shows that the values of an implementation
  with 64 integer bits stay below `2^63`.
* Only the three FFT conversion fields are in fixed point; the products and `1/q` of
  `toFFTTarget`, `ffSampling`, and the products and sums of `fromFFTPreimage` are exact.
* Key coefficients in `[-127, 127]`, the NTRU equation, the tree being the true tree and the tree
  bounds are hypotheses; key generation is not covered.
-/

public section

open OracleComp OracleSpec LatticeCrypto Complex
open scoped ENNReal

namespace Falcon.Concrete

open Falcon Falcon.FixedPoint

/-! ## The squared target distance -/

/-- The bound on the squared slotwise distance of the fixed-point and exact `toFFTTarget`, for
keys with coefficients in `[-127, 127]`:
`2 · ((targetFftErrorL2 k · (2^(k+1) · 127 + fftError k) + 2^k · 17379 · fftError k) / q)²`. -/
@[expose] noncomputable def fx64TargetSqDeviation (k : ℕ) : ℝ :=
  2 * ((FixedPoint.targetFftErrorL2 k * (2 ^ (k + 1) * 127 + FixedPoint.fftError k) +
    2 ^ k * 17379 * FixedPoint.fftError k) / 12289) ^ 2

/-- **The `ffSampling` targets at the fixed-point and exact FFT fields**, for keys with
coefficients in `[-127, 127]`: squared slotwise distance at most
`fx64TargetSqDeviation (logn - 1)`. -/
theorem slotsSqDist_toFFTTarget_fx64 (A : Arith64) (p : Params) (hn : p.n = 2 ^ p.logn)
    (h1 : 1 ≤ p.logn) (sk : SecretKey p) (hkey : KeyCoeffsLe127 sk) (c : Rq p.n) :
    slotsSqDist (toFFTTarget p (fx64FFTPrimitives A p hn) c sk).1
        (toFFTTarget p (concretePrimitives p hn) c sk).1 +
      slotsSqDist (toFFTTarget p (fx64FFTPrimitives A p hn) c sk).2
        (toFFTTarget p (concretePrimitives p hn) c sk).2 ≤ fx64TargetSqDeviation p.fftDepth := by
  have h : 2 * 2 ^ p.fftDepth = p.n := by
    rw [hn, Params.fftDepth, ← pow_succ']; congr 1; omega
  have hex := concretePrimitives_exactFFT p hn h
  have htgt : ∀ c : Rq p.n, (concretePrimitives p hn).fftTarget c =
      RealFFTPoly.ofCoeffs p.fftDepth fun i => (((c.get (Fin.cast h i)).val : ℕ) : ℝ) := fun c => by
    simp [concretePrimitives, Primitives.exactFftTarget, h]
  refine slotsSqDist_toFFTTarget_le h _ _ hex.fftInt_eq htgt
    (FixedPoint.targetFftErrorL2_nonneg _) (FixedPoint.fftError_nonneg _) (fun c => ?_)
    (fun u hu j => ?_) sk (fun i => ⟨(hkey i).1, (hkey i).2.2.1⟩) c
  · rw [htgt]; exact A.sum_norm_coord_fftTarget_sub_sq_le p h c
  · rw [hex.fftInt_eq]; exact A.coord_fftInt_sub p h u hu j

/-- The squared target bound at Falcon-512 is below `1/(4 · 10^21)` (about `2^(-71.76)`). -/
theorem fx64TargetSqDeviation_falcon512 : fx64TargetSqDeviation 8 ≤ 1 / (4 * 10 ^ 21) := by
  norm_num [fx64TargetSqDeviation, FixedPoint.targetFftErrorL2, FixedPoint.fftError,
    FixedPoint.twiddleError, FixedPoint.etaFwd]

/-! ## The assembled preimage -/

/-- **`fromFFTPreimage` at the fixed-point and exact FFT fields agree** on sampled pairs with
coefficients at most `Z`, for keys with coefficients in `[-127, 127]` and
`fx64CosetDeviation (logn - 1) Z < 1/2`. -/
theorem fromFFTPreimage_fx64_eq (A : Arith64) (p : Params) (hn : p.n = 2 ^ p.logn)
    (h1 : 1 ≤ p.logn) (sk : SecretKey p) (hkey : KeyCoeffsLe127 sk) (Z : ℝ)
    (hdev : fx64CosetDeviation p.fftDepth Z < 1 / 2) (c : Rq p.n) (z : FFTPair p.fftDepth)
    (hz : PreimageCoeffsLe p.fftDepth Z z) :
    fromFFTPreimage p (fx64FFTPrimitives A p hn) c sk z =
      fromFFTPreimage p (concretePrimitives p hn) c sk z := by
  have h : 2 * 2 ^ p.fftDepth = p.n := by
    rw [hn, Params.fftDepth, ← pow_succ']; congr 1; omega
  exact fromFFTPreimage_eq_of_exactFFT h _ _ (concretePrimitives_exactFFT p hn h) sk Z
    (fun a b ha hb => ifftRound_basis_fx64 A p h _ (fx64FFTPrimitives_fx64FFTFields A p hn) sk
      hkey Z hdev a b ha hb) c z hz

/-! ## The transfer -/

/-- **Rényi precision transfer at the fixed-point FFT primitives**, for `2 ≤ logn`, keys with
coefficients in `[-127, 127]`, trees with leaves at least `σlo ≥ 1.277`, root factor slots at
most `Lroot` and the other factor slots at most `Lin`, and `Z` with
`fx64CosetDeviation (logn - 1) Z < 1/2`, under the budget
`precisionRate λ σlo · K · maxAttempts · ffSamplingGrowth κ μroot μin · fx64TargetSqDeviation κ ≤
log 2 / 2`, `κ = logn - 1`. -/
theorem idealExperiment_fx64_precision (A : Arith64) (p : Params) (hn : p.n = 2 ^ p.logn)
    (h2 : 2 ≤ p.logn) (pk : PublicKey p) (sk : SecretKey p) (hkey : KeyCoeffsLe127 sk) (Z : ℝ)
    (hdev : fx64CosetDeviation p.fftDepth Z < 1 / 2)
    (σlo σhi : ℝ) (hσlo : 1277 / 1000 ≤ σlo) (hleaves : sk.tree.LeavesIn σlo σhi)
    (Lroot Lin μroot μin : ℝ) (hμroot : Lroot ^ 2 ≤ (μroot - 1) * (μroot - 1 - Lroot ^ 2))
    (hμroot' : 1 + Lroot ^ 2 ≤ μroot) (hμin : Lin ^ 2 ≤ (μin - 1) * (μin - 1 - Lin ^ 2))
    (hμin' : 1 + Lin ^ 2 ≤ μin) (hfactors : sk.tree.FactorsLeRoot Lroot Lin)
    (lam : ℕ) (hlam : 2 ≤ lam) (maxAttempts K : ℕ)
    (hbudget : precisionRate lam σlo * (K * maxAttempts *
      (ffSamplingGrowth p.fftDepth μroot μin * fx64TargetSqDeviation p.fftDepth)) ≤
        Real.log 2 / 2)
    {α : Type} [MeasurableSpace α] [Countable α] [MeasurableSingletonClass α]
    (adv : OracleComp (unifSpec + signOracleSpec) α) (hK : IsQueryBoundP adv IsSignQuery K)
    (T : ℝ≥0∞) (hT : 1 ≤ T) {s : Set α} (hs : MeasurableSet s)
    (hwin : T * (2 : ℝ≥0∞) ^ (-((lam : ℝ) - 1)) <
      𝒟[idealExperiment p (fx64FFTPrimitives A p hn) pk sk maxAttempts adv] s) :
    T * (2 : ℝ≥0∞) ^ (-(lam : ℝ)) <
      𝒟[idealExperiment p (concretePrimitives p hn) pk sk maxAttempts adv] s +
        K * maxAttempts * preimageTailMass p (concretePrimitives p hn) sk Z :=
  idealExperiment_precision (concretePrimitives p hn) (fx64FFTPrimitives A p hn)
    (by unfold Params.fftDepth; omega) rfl rfl rfl pk sk (fx64TargetSqDeviation p.fftDepth)
    (slotsSqDist_toFFTTarget_fx64 A p hn (by omega) sk hkey) σlo σhi hσlo hleaves Lroot Lin
    μroot μin hμroot hμroot' hμin hμin' hfactors Z
    (fun c z hz => fromFFTPreimage_fx64_eq A p hn (by omega) sk hkey Z hdev c z hz) lam hlam
    maxAttempts K hbudget adv hK T hT hs hwin

/-- The Falcon-512 budget at the fixed-point fields: at `λ = 128`, leaves at least `σmin`, growth
constants `578.01` (root factor `24.0001`) and `2.6001` (inner factors `0.9923`), up to `2^53`
signing attempts fit. -/
theorem fx64_falcon512_budget (m : ℕ) (hm : m ≤ 2 ^ 53) :
    precisionRate 128 falcon512.sigmaMin * (m * (ffSamplingGrowth 8 (57801 / 100)
      (26001 / 10000) * fx64TargetSqDeviation 8)) ≤ Real.log 2 / 2 := by
  have hσ : falcon512.sigmaMin = 12778336969128337 / 10000000000000000 := rfl
  have hE0 : 0 ≤ fx64TargetSqDeviation 8 := by unfold fx64TargetSqDeviation; positivity
  have hP : 0 ≤ precisionRate 128 falcon512.sigmaMin *
      ffSamplingGrowth 8 (57801 / 100) (26001 / 10000) := by
    rw [hσ]; norm_num [precisionRate, ffSamplingGrowth]
  have hval : precisionRate 128 falcon512.sigmaMin *
      ffSamplingGrowth 8 (57801 / 100) (26001 / 10000) * (2 ^ 53 * (1 / (4 * 10 ^ 21))) ≤
        34 / 100 := by
    rw [hσ]; norm_num [precisionRate, ffSamplingGrowth]
  have hm' : (m : ℝ) ≤ 2 ^ 53 := by exact_mod_cast hm
  calc _ = precisionRate 128 falcon512.sigmaMin *
        ffSamplingGrowth 8 (57801 / 100) (26001 / 10000) * (m * fx64TargetSqDeviation 8) := by
        ring
    _ ≤ _ * (2 ^ 53 * (1 / (4 * 10 ^ 21))) := mul_le_mul_of_nonneg_left
        (mul_le_mul hm' fx64TargetSqDeviation_falcon512 hE0 (by positivity)) hP
    _ ≤ 34 / 100 := hval
    _ ≤ Real.log 2 / 2 := by linarith [Real.log_two_gt_d9]

/-- **Rényi precision transfer at the fixed-point FFT primitives for Falcon-512**, at `λ = 128`
and `Z = 2^33`, for keys satisfying the NTRU equation with coefficients in `[-127, 127]`, whose
tree is the true tree with leaves in `[σmin, σmax]`, root factor slots at most `24.0001` and the
other factor slots at most `0.9923`, and an experiment making at most `K` signing queries with
`maxAttempts` attempts each and `K · maxAttempts ≤ 2^53`: an event of probability above
`T · 2^{-127}` when the fixed-point bundle signs with the ideal sampler has probability above
`T · 2^{-128}` when the exact bundle does, up to `K · maxAttempts · 2⁻¹⁰⁰⁰`. The factor bounds are
the root check `γroot = 24` of the modified NTRUGen of ePrint 2026/1531 (Alg. 2, l. 14-15) and its
Lemma 8 at `γhybrid = 4`; neither is a check of Falcon round 3 or FIPS 206 key generation. -/
theorem idealExperiment_fx64_precision_falcon512 (A : Arith64) (pk : PublicKey falcon512)
    (sk : SecretKey falcon512) (hntru : ntruEquation falcon512 sk.f sk.g sk.capF sk.capG)
    (htree : sk.tree = trueTree falcon512 sk) (hkey : KeyCoeffsLe127 sk)
    (hleaves : sk.tree.LeavesIn falcon512.sigmaMin falcon512.sigmaMax)
    (hfactors : sk.tree.FactorsLeRoot (240001 / 10000) (9923 / 10000)) (maxAttempts K : ℕ)
    (hKM : K * maxAttempts ≤ 2 ^ 53)
    {α : Type} [MeasurableSpace α] [Countable α] [MeasurableSingletonClass α]
    (adv : OracleComp (unifSpec + signOracleSpec) α) (hK : IsQueryBoundP adv IsSignQuery K)
    (T : ℝ≥0∞) (hT : 1 ≤ T) {s : Set α} (hs : MeasurableSet s)
    (hwin : T * (2 : ℝ≥0∞) ^ (-((128 : ℕ) - 1 : ℝ)) <
      𝒟[idealExperiment falcon512 (fx64FFTPrimitives A falcon512 rfl) pk sk maxAttempts adv] s) :
    T * (2 : ℝ≥0∞) ^ (-((128 : ℕ) : ℝ)) <
      𝒟[idealExperiment falcon512 (concretePrimitives falcon512 rfl) pk sk maxAttempts adv] s +
        K * maxAttempts * ENNReal.ofReal (1 / 2 ^ 1000) := by
  have hdepth : falcon512.fftDepth = 8 := by decide
  have hσmin : (1277 / 1000 : ℝ) ≤ falcon512.sigmaMin := by
    change (1277 / 1000 : ℝ) ≤ (12778336969128337 : ℝ) / 10000000000000000
    norm_num
  have hb := fx64_falcon512_budget (K * maxAttempts) hKM
  push_cast at hb
  refine (idealExperiment_fx64_precision A falcon512 rfl (by decide) pk sk hkey (2 ^ 33)
    fx64CosetDeviation_falcon512 falcon512.sigmaMin falcon512.sigmaMax hσmin hleaves
    (240001 / 10000) (9923 / 10000) (57801 / 100) (26001 / 10000) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hfactors 128 (by norm_num) maxAttempts K
    (by rw [hdepth]; linarith) adv hK T hT hs hwin).trans_le ?_
  gcongr
  exact preimageTailMass_falcon512_two_pow_33_le (concretePrimitives falcon512 rfl) rfl rfl sk
    hntru htree hkey hleaves

end Falcon.Concrete

end
