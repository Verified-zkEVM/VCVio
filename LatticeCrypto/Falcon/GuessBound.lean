/-
Copyright (c) 2026 XC0R. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XC0R
-/

module
public import LatticeCrypto.Falcon.BasisMoments
public import LatticeCrypto.Falcon.SamplerTransfer
public import LatticeCrypto.Falcon.Security
public import VCVio.OracleComp.Constructions.AcceptCond
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# The guessing bound of Falcon's accept-conditional sampler

With Falcon's own attempt as the ideal attempt (`ε_step = 0`), `idealAttemptResamples` forces the
ideal sampler to be the accept-conditional of `signAttempt` (`acceptCondPSF`). This file proves a
numeric guessing bound `εpp` for it (`idealSamplerGuessBound_acceptCond`), and a rejection bound
`pRej` for the attempt (`prob_signAttempt_none_le`), at exact FFT fields and under the Rényi
sampler law `Primitives.SamplerQuality a ε`, from:

* the point mass of the reduced output (`trapdoorSample_pointMass_le`,
  `LatticeCrypto.Falcon.BasisCoords`): the largest point mass of `ffSampling` plus the mass of the
  far event `BasisFar`;
* the far event and the rejection under the ideal sampler (`prob_basisFar_ideal_le`,
  `prob_basisNormSq_ge_ideal_le`, `LatticeCrypto.Falcon.BasisMoments`);
* their transfer to `samplerZ` (`prob_ffSampling_le_renyi`, `LatticeCrypto.Falcon.SamplerTransfer`).

`falcon512_non_sis_terms_lt_one` / `falcon1024_non_sis_terms_lt_one` instantiate the
hypotheses of `euf_cma_collision_security` other than `hReg` and `hQ` at Falcon's parameters and
bound the sum of its exact-match, salt and sampler terms below one.

## What is not proved

* `SamplerQuality a ε` is a hypothesis; it is not established for Falcon's sampler.
* Keys are honest by hypothesis (`HonestKeys`): key generation is not covered.
* No sampler and no key generation in the repository is shown to satisfy `SamplerQuality a ε` at
  `ε ≤ 2⁻²⁰` and `HonestKeys`: the headlines have no non-vacuity witness. The two are jointly
  satisfiable on paper; that is not machine-checked.
* The collision term is not bounded. It is SIS at norm `2β`, which [FGdG+25] (§1.2) note is
  trivial at Falcon-1024 and short of the security margin at Falcon-512.
* The bounds are far from the literature: `pRej ≤ 0.91` (Markov's inequality on the second
  moment) against at most `2^-14.31` in [FGdG+25] (App. E.1); `εpp ≤ 2⁻²³⁸` (dominated by the far
  event) against `2^-(n-1)` for the coset Gaussian (GPV08 Lemma 2.10); the non-collision terms
  sum below one (`0.2291` / `0.3907`), not to a small value.
* `hReg` is not addressed. With `idealPSF := acceptCondPSF` its law depends on the secret basis
  through the tree, so an exact `hReg` witness exists only if all honest secret keys sharing a
  public key induce the same law. The only `domainSample` in the repository, in
  `LatticeCryptoTest.Falcon.NonVacuity`, samples with the basis.
* Only exact FFT fields are covered; floating-point fields are not.

## References

- [FGdG+25]: Fouque, Gajland, de Groote, Janneck, Kiltz. "A Closer Look at Falcon."
  ePrint 2024/1769.
- GPV08: Gentry, Peikert, Vaikuntanathan. STOC 2008, Lemma 2.10.
-/

public section

open OracleComp OracleSpec LatticeCrypto MeasureTheory
open scoped ENNReal

namespace Falcon

variable {p : Params}

/-! ## Honest keys -/

variable (p) in
/-- An honestly generated key: valid, `f` invertible modulo `q`, the true tree of the basis, and
leaves in `[σmin, σmax]`. -/
structure HonestKey (pk : PublicKey p) (sk : SecretKey p) : Prop where
  /-- The NTRU equation and `f · h = g`. -/
  valid : validKeyPair p pk sk = true
  /-- `f` is invertible modulo `q`. -/
  unit : ∃ u : Rq p.n, negacyclicMul (IntPoly.toRq sk.f) u = 1
  /-- The tree is exact ffLDL⋆ of the basis. -/
  tree_eq : sk.tree = trueTree p sk
  /-- Every leaf lies in `[σmin, σmax]`. -/
  leavesIn : sk.tree.LeavesIn p.sigmaMin p.sigmaMax

variable (p) in
/-- Every key pair in the support of `hr.gen` is honest. -/
@[expose] def HonestKeys
    (hr : GenerableRelation (PublicKey p) (SecretKey p) (validKeyPair p)) : Prop :=
  ∀ pk sk, (pk, sk) ∈ support hr.gen → HonestKey p pk sk

/-! ## The accept-conditional sampler -/

variable (p) in
/-- The accept-conditional of `signAttempt` as a preimage-sampleable function, with the
deterministic `eval` and `isShort` of `falconPSF`. -/
@[expose] noncomputable def acceptCondPSF (prims : Primitives p) :
    PreimageSampleableFunction (PublicKey p) (SecretKey p) (Rq p.n × Rq p.n) (Rq p.n) where
  eval := (falconPSF p prims).eval
  trapdoorSample pk sk c := ProbComp.acceptCond (signAttempt p prims pk sk c)
  isShort := (falconPSF p prims).isShort

/-- `signAttempt` resamples to its accept-conditional where it accepts with positive
probability. -/
theorem resamplesTo_acceptCondPSF (prims : Primitives p) (pk : PublicKey p) (sk : SecretKey p)
    (c : Rq p.n) (hacc : Pr{let o ← signAttempt p prims pk sk c}[o = none] < 1) :
    ProbComp.ResamplesTo (signAttempt p prims pk sk c)
      ((acceptCondPSF p prims).trapdoorSample pk sk c) :=
  (ProbComp.acceptCond_spec _ hacc).1

/-- **Correctness of the accept-conditional** on an honest key at exact fields: its outputs are
accepted outputs of `signAttempt`, hence short and on the coset. -/
theorem correctAt_acceptCondPSF (hn : 2 * 2 ^ p.fftDepth = p.n) (prims : Primitives p)
    (hex : prims.ExactFFT hn) (pk : PublicKey p) (sk : SecretKey p) (hkey : HonestKey p pk sk)
    (hacc : ∀ c, Pr{let o ← signAttempt p prims pk sk c}[o = none] < 1) :
    (acceptCondPSF p prims).CorrectAt pk sk := by
  have hn0 : 0 < p.n := by rw [← hn]; positivity
  have hvalid := hkey.valid
  have hcap := capRelation_of_validKeyPair p hn0 pk sk hvalid hkey.unit
  rw [validKeyPair_eq_true_iff] at hvalid
  intro c x hx
  have hsome := (ProbComp.acceptCond_spec _ (hacc c)).2.2 x hx
  simp only [signAttempt, mem_support_bind_iff] at hsome
  obtain ⟨y, hy, hxy⟩ := hsome
  split_ifs at hxy with hs
  · rw [support_pure, Set.mem_singleton_iff, Option.some_inj] at hxy
    subst hxy
    exact ⟨hpreimage_of_exactFFT p prims hn hex pk sk hvalid.2 hcap c x hy, hs⟩
  · simp at hxy

/-- `((1 + ε)^(4 · 2^κ) · idealRejectBound)^((a - 1) / a)`: the rejection bound of `signAttempt`. -/
@[expose] noncomputable def pRejBound (p : Params) (a : ℝ) (ε : ℝ≥0∞) : ℝ≥0∞ :=
  ((1 + ε) ^ (4 * 2 ^ p.fftDepth) * ENNReal.ofReal (idealRejectBound p)) ^ ((a - 1) / a)

private theorem signAttempt_eq_map (prims : Primitives p) (pk : PublicKey p) (sk : SecretKey p)
    (c : Rq p.n) :
    signAttempt p prims pk sk c =
      (fun z => if (falconPSF p prims).isShort (fromFFTPreimage p prims c sk z) then
          some (fromFFTPreimage p prims c sk z) else none) <$>
        prims.ffSampling p.fftDepth (toFFTTarget p prims c sk) sk.tree := by
  rw [map_eq_bind_pure_comp]
  simp only [signAttempt, falconPSF, bind_assoc, pure_bind]
  congr 1
  funext z
  rw [Function.comp_apply]
  exact (apply_ite pure _ _ _).symm

private theorem pairL2NormSq_le_sum_sq (hn : 2 * 2 ^ p.fftDepth = p.n) (x : Rq p.n × Rq p.n)
    (s₁ s₂ : Fin (2 * 2 ^ p.fftDepth) → ℤ)
    (h : ∀ i, x.1.get (Fin.cast hn i) = (s₁ i : Coeff) ∧ x.2.get (Fin.cast hn i) = (s₂ i : Coeff)) :
    (pairL2NormSq x.1 x.2 : ℝ) ≤ ∑ i, ((s₁ i : ℝ) ^ 2 + (s₂ i : ℝ) ^ 2) := by
  have hc : ∀ (y : Coeff) (s : ℤ), y = (s : Coeff) →
      (LatticeCrypto.centeredRepr y).natAbs ^ 2 ≤ s.natAbs ^ 2 := by
    rintro y s rfl
    exact Nat.pow_le_pow_left (ZMod.natAbs_min_of_le_div_two _ _ _ (ZMod.coe_valMinAbs _)
      (ZMod.natAbs_valMinAbs_le _)) 2
  have hsum : ∀ f : Fin p.n → ℕ, ∑ i, f i = ∑ i : Fin (2 * 2 ^ p.fftDepth), f (Fin.cast hn i) :=
    fun f => (Fintype.sum_equiv (finCongr hn) _ _ fun i => by simp).symm
  have hle : pairL2NormSq x.1 x.2 ≤ ∑ i, ((s₁ i).natAbs ^ 2 + (s₂ i).natAbs ^ 2) := by
    change ∑ i : Fin p.n, (LatticeCrypto.centeredRepr (x.1.get i)).natAbs ^ 2 +
      ∑ i : Fin p.n, (LatticeCrypto.centeredRepr (x.2.get i)).natAbs ^ 2 ≤ _
    rw [hsum, hsum, ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun i _ => add_le_add (hc _ _ (h i).1) (hc _ _ (h i).2)
  calc (pairL2NormSq x.1 x.2 : ℝ) ≤ ((∑ i, ((s₁ i).natAbs ^ 2 + (s₂ i).natAbs ^ 2) : ℕ) : ℝ) := by
        exact_mod_cast hle
    _ = _ := by push_cast [Nat.cast_natAbs, Int.cast_abs, sq_abs]; rfl

/-- **Rejection of `signAttempt`**: a rejection makes `ψ(t - z)` longer than `⌊β²⌋`, since
centered representatives are no longer than any lift; transfer the ideal bound. -/
theorem prob_signAttempt_none_le (hn : 2 * 2 ^ p.fftDepth = p.n) (hdepth : 1 ≤ p.fftDepth)
    (hσ : 1277 / 1000 ≤ p.sigmaMin) (prims : Primitives p) (hex : prims.ExactFFT hn)
    (htgt : prims.fftTarget = Primitives.exactFftTarget p) {a : ℝ} {ε : ℝ≥0∞}
    (hq : prims.SamplerQuality a ε) (hε : ε ≠ ⊤) (pk : PublicKey p) (sk : SecretKey p)
    (hkey : HonestKey p pk sk) (c : Rq p.n) :
    Pr{let o ← signAttempt p prims pk sk c}[o = none] ≤ pRejBound p a ε := by
  have hntru := ((validKeyPair_eq_true_iff (p := p) pk sk).1 hkey.valid).1
  have hτ : 0 ≤ (a - 1) / a := div_nonneg (by linarith [hq.one_lt]) (by linarith [hq.one_lt])
  rw [signAttempt_eq_map, prEvent_map]
  refine (prEvent_mono_of_support _ _ (fun z => (p.betaSquared : ℝ) + 1 ≤
    ∑ i, (basisCoeffFst sk i (toFFTTarget p prims c sk - z) ^ 2 +
      basisCoeffSnd sk i (toFFTTarget p prims c sk - z) ^ 2)) fun z hz hnone => ?_).trans ?_
  · obtain ⟨a', b', hz'⟩ := prims.ffSampling_support_ofCoeffs _ _ _ z hz
    obtain ⟨s₁, s₂, hψ, hred⟩ :=
      fromFFTPreimage_eq_basisCoeff hn prims hex htgt sk hntru c z ⟨a', b', hz'⟩
    have hlong : ¬ pairL2NormSq (fromFFTPreimage p prims c sk z).1
        (fromFFTPreimage p prims c sk z).2 ≤ p.betaSquared := fun hle => by
      simp [falconPSF, hle] at hnone
    have hβ : (p.betaSquared : ℝ) + 1 ≤ (pairL2NormSq (fromFFTPreimage p prims c sk z).1
        (fromFFTPreimage p prims c sk z).2 : ℝ) := by
      exact_mod_cast Nat.succ_le_of_lt (not_le.1 hlong)
    have hsq := pairL2NormSq_le_sum_sq hn _ s₁ s₂ hred
    have hsum : ∑ i, (basisCoeffFst sk i (toFFTTarget p prims c sk - z) ^ 2 +
        basisCoeffSnd sk i (toFFTTarget p prims c sk - z) ^ 2) =
        ∑ i, ((s₁ i : ℝ) ^ 2 + (s₂ i : ℝ) ^ 2) :=
      Finset.sum_congr rfl fun i _ => by rw [(hψ i).1, (hψ i).2]
    rw [hsum]
    exact hβ.trans hsq
  · refine (prob_ffSampling_le_renyi prims hq hε _ _ _ hkey.leavesIn _).trans ?_
    exact ENNReal.rpow_le_rpow (mul_le_mul' le_rfl (prob_basisNormSq_ge_ideal_le hn hdepth hσ sk
      hntru hkey.tree_eq hkey.leavesIn _)) hτ

/-- The guessing bound `(P₀ + ((1 + ε)^(4 · 2^κ) · idealFarBound)^((a - 1) / a)) / (1 - pRej)`
with `P₀ = (1 / (σmin √(2π) - 1) + (1 - (1 + ε)⁻¹)^(1/2))^(4 · 2^κ)` the point mass of
`ffSampling` under the envelope. -/
@[expose] noncomputable def guessBound (p : Params) (a : ℝ) (ε : ℝ≥0∞) : ℝ≥0∞ :=
  ((ENNReal.ofReal (1 / (p.sigmaMin * Real.sqrt (2 * Real.pi) - 1)) +
        (1 - (1 + ε)⁻¹) ^ (1 / 2 : ℝ)) ^ (4 * 2 ^ p.fftDepth) +
      ((1 + ε) ^ (4 * 2 ^ p.fftDepth) * ENNReal.ofReal (idealFarBound p)) ^ ((a - 1) / a)) /
    (1 - pRejBound p a ε)

/-- **The guessing bound of the accept-conditional sampler**: point mass of the reduced output
over the acceptance probability. -/
theorem idealSamplerGuessBound_acceptCond (hn : 2 * 2 ^ p.fftDepth = p.n)
    (hdepth : 1 ≤ p.fftDepth) (hσ : 1277 / 1000 ≤ p.sigmaMin) (prims : Primitives p)
    (hex : prims.ExactFFT hn) (htgt : prims.fftTarget = Primitives.exactFftTarget p)
    {a : ℝ} {ε : ℝ≥0∞} (hq : prims.SamplerQuality a ε) (hε : ε ≠ ⊤)
    (hr : GenerableRelation (PublicKey p) (SecretKey p) (validKeyPair p))
    (hkeys : HonestKeys p hr) :
    idealSamplerGuessBound p hr (acceptCondPSF p prims) (guessBound p a ε) := by
  have hσ' : 1 < p.sigmaMin * Real.sqrt (2 * Real.pi) := by
    have hpi := Real.pi_gt_three
    have h6 : (2.44 : ℝ) ≤ Real.sqrt (2 * Real.pi) := by
      rw [Real.le_sqrt (by norm_num) (by positivity)]
      nlinarith
    nlinarith
  have hτ : 0 ≤ (a - 1) / a := div_nonneg (by linarith [hq.one_lt]) (by linarith [hq.one_lt])
  intro pk sk hmem c x
  have hkey := hkeys pk sk hmem
  have hntru := ((validKeyPair_eq_true_iff (p := p) pk sk).1 hkey.valid).1
  have hrej := prob_signAttempt_none_le hn hdepth hσ prims hex htgt hq hε pk sk hkey c
  have hP : 0 < ENNReal.ofReal (1 / (p.sigmaMin * Real.sqrt (2 * Real.pi) - 1)) :=
    ENNReal.ofReal_pos.2 (one_div_pos.2 (by linarith))
  have hnum : Pr{let y ← (falconPSF p prims).trapdoorSample pk sk c}[y = x] ≤
      (ENNReal.ofReal (1 / (p.sigmaMin * Real.sqrt (2 * Real.pi) - 1)) +
        (1 - (1 + ε)⁻¹) ^ (1 / 2 : ℝ)) ^ (4 * 2 ^ p.fftDepth) +
      ((1 + ε) ^ (4 * 2 ^ p.fftDepth) * ENNReal.ofReal (idealFarBound p)) ^ ((a - 1) / a) := by
    refine (trapdoorSample_pointMass_le hn prims hex htgt pk sk hntru c x).trans
      (add_le_add (iSup_le fun z => ?_) ?_)
    · exact prims.ffSampling_pointMass_le_of_samplerEnvelope hσ'
        (prims.samplerEnvelope_of_samplerQuality hq hσ') _ _ _ hkey.leavesIn z
    · refine (prob_ffSampling_le_renyi prims hq hε _ _ _ hkey.leavesIn
        (fun z => BasisFar sk (toFFTTarget p prims c sk - z))).trans ?_
      exact ENNReal.rpow_le_rpow (mul_le_mul' le_rfl (prob_basisFar_ideal_le hn hdepth hσ sk hntru
        hkey.tree_eq hkey.leavesIn _)) hτ
  by_cases hacc : Pr{let o ← signAttempt p prims pk sk c}[o = none] < 1
  · obtain ⟨-, hform, -⟩ := ProbComp.acceptCond_spec _ hacc
    have hsome : Pr{let o ← signAttempt p prims pk sk c}[o = some x] ≤
        Pr{let y ← (falconPSF p prims).trapdoorSample pk sk c}[y = x] := by
      rw [signAttempt_eq_map, prEvent_map]
      simp only [falconPSF, bind_pure_comp, prEvent_map]
      refine prEvent_mono _ _ _ fun z hz => ?_
      split_ifs at hz
      exact Option.some_injective _ hz
    have hform' : Pr{let y ← (acceptCondPSF p prims).trapdoorSample pk sk c}[y = x] =
        Pr{let o ← signAttempt p prims pk sk c}[o = some x] /
          (1 - Pr{let o ← signAttempt p prims pk sk c}[o = none]) := hform x
    rw [hform']
    exact ENNReal.div_le_div (hsome.trans hnum) (tsub_le_tsub_left hrej 1)
  · have hz : 1 - pRejBound p a ε = 0 := tsub_eq_zero_of_le ((not_lt.1 hacc).trans hrej)
    have hnum0 : (ENNReal.ofReal (1 / (p.sigmaMin * Real.sqrt (2 * Real.pi) - 1)) +
          (1 - (1 + ε)⁻¹) ^ (1 / 2 : ℝ)) ^ (4 * 2 ^ p.fftDepth) +
        ((1 + ε) ^ (4 * 2 ^ p.fftDepth) * ENNReal.ofReal (idealFarBound p)) ^ ((a - 1) / a) ≠ 0 :=
      (lt_of_lt_of_le (ENNReal.pow_pos (lt_of_lt_of_le hP le_self_add) _) le_self_add).ne'
    rw [guessBound, hz, ENNReal.div_zero hnum0]
    exact le_top

/-! ## Falcon-512 and Falcon-1024 -/

theorem falcon512_two_mul_two_pow_fftDepth : 2 * 2 ^ falcon512.fftDepth = falcon512.n := by
  decide

theorem falcon1024_two_mul_two_pow_fftDepth : 2 * 2 ^ falcon1024.fftDepth = falcon1024.n := by
  decide

private theorem two_inv_pow_eq (k : ℕ) : (2⁻¹ : ℝ≥0∞) ^ k = ENNReal.ofReal ((1 / 2) ^ k) := by
  rw [ENNReal.ofReal_pow (by norm_num), one_div, ENNReal.ofReal_inv_of_pos two_pos,
    ENNReal.ofReal_ofNat]

private theorem one_add_pow_le {u : ℝ} (hu : 0 ≤ u) (M : ℕ) (h : M * u ≤ 1) :
    (1 + u) ^ M ≤ 1 + (M * u + (M * u) ^ 2) := by
  have hq := Real.abs_exp_sub_one_sub_id_le (x := M * u)
    (by rw [abs_of_nonneg (by positivity)]; exact h)
  calc (1 + u) ^ M ≤ Real.exp u ^ M := by gcongr; linarith [Real.add_one_le_exp u]
    _ = Real.exp (M * u) := (Real.exp_nat_mul u M).symm
    _ ≤ _ := by linarith [(abs_le.1 hq).2]

private theorem one_add_pow_le_ofReal {ε : ℝ≥0∞} (hε : ε ≤ 2⁻¹ ^ 20) (M : ℕ)
    (hM : (M : ℝ) * (1 / 2) ^ 20 ≤ 1) :
    (1 + ε) ^ M ≤ ENNReal.ofReal (1 + ((M : ℝ) * (1 / 2) ^ 20 + ((M : ℝ) * (1 / 2) ^ 20) ^ 2)) := by
  calc (1 + ε) ^ M ≤ (1 + 2⁻¹ ^ 20) ^ M := by gcongr
    _ = ENNReal.ofReal ((1 + (1 / 2) ^ 20) ^ M) := by
      rw [two_inv_pow_eq, ← ENNReal.ofReal_one, ← ENNReal.ofReal_add zero_le_one (by positivity),
        ← ENNReal.ofReal_pow (by positivity)]
    _ ≤ _ := ENNReal.ofReal_le_ofReal (one_add_pow_le (by positivity) M hM)

private theorem half_le_div {a : ℝ} (ha : 2 ≤ a) : 1 / 2 ≤ (a - 1) / a := by
  rw [div_le_div_iff₀ (by norm_num) (by linarith)]
  linarith

private theorem rpow_le_ofReal_of_le_sq {Y : ℝ≥0∞} {c τ : ℝ} (hc : 0 ≤ c) (hc1 : c ≤ 1)
    (hτ : 1 / 2 ≤ τ) (hY : Y ≤ ENNReal.ofReal (c ^ 2)) : Y ^ τ ≤ ENNReal.ofReal c := by
  have hY1 : Y ≤ 1 := hY.trans (ENNReal.ofReal_le_one.2 (by nlinarith))
  calc Y ^ τ ≤ Y ^ (1 / 2 : ℝ) := ENNReal.rpow_le_rpow_of_exponent_ge hY1 hτ
    _ ≤ ENNReal.ofReal (c ^ 2) ^ (1 / 2 : ℝ) := ENNReal.rpow_le_rpow hY (by norm_num)
    _ = ENNReal.ofReal c := by
      rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num), ← Real.sqrt_eq_rpow,
        Real.sqrt_sq hc]

private theorem sqrt_one_sub_inv_le {ε : ℝ≥0∞} (hε : ε ≤ 2⁻¹ ^ 20) :
    (1 - (1 + ε)⁻¹) ^ (1 / 2 : ℝ) ≤ ENNReal.ofReal ((1 / 2) ^ 10) := by
  have htop : ε ≠ ⊤ := ne_top_of_le_ne_top (by simp) hε
  have h1 : 1 - (1 + ε)⁻¹ ≤ ε := by
    rw [tsub_le_iff_right]
    have h0 : (1 + ε) ≠ 0 := (lt_of_lt_of_le one_pos le_self_add).ne'
    have ht : (1 + ε) ≠ ⊤ := ENNReal.add_ne_top.2 ⟨ENNReal.one_ne_top, htop⟩
    calc (1 : ℝ≥0∞) = (1 + ε) * (1 + ε)⁻¹ := (ENNReal.mul_inv_cancel h0 ht).symm
      _ = (1 + ε)⁻¹ + ε * (1 + ε)⁻¹ := by rw [add_mul, one_mul]
      _ ≤ (1 + ε)⁻¹ + ε * 1 := by gcongr; exact ENNReal.inv_le_one.2 le_self_add
      _ = ε + (1 + ε)⁻¹ := by rw [mul_one, add_comm]
  have h2 : ε ≤ ENNReal.ofReal (((1 / 2) ^ 10) ^ 2) := by
    rw [← pow_mul, ← two_inv_pow_eq]
    exact hε
  calc (1 - (1 + ε)⁻¹) ^ (1 / 2 : ℝ) ≤ ENNReal.ofReal (((1 / 2) ^ 10) ^ 2) ^ (1 / 2 : ℝ) :=
        ENNReal.rpow_le_rpow (h1.trans h2) (by norm_num)
    _ = ENNReal.ofReal ((1 / 2) ^ 10) := by
      rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num), ← Real.sqrt_eq_rpow,
        Real.sqrt_sq (by positivity)]

private theorem exp_neg_le_half_pow {x : ℝ} (k : ℕ) (h : (k : ℝ) * 0.6931471808 ≤ x) :
    Real.exp (-x) ≤ (1 / 2) ^ k := by
  have hk : (k : ℝ) * Real.log 2 ≤ x :=
    (mul_le_mul_of_nonneg_left Real.log_two_lt_d9.le (Nat.cast_nonneg k)).trans h
  calc Real.exp (-x) ≤ Real.exp (-(k * Real.log 2)) := Real.exp_le_exp.2 (by linarith)
    _ = (1 / 2) ^ k := by
      rw [Real.exp_neg, Real.exp_nat_mul, Real.exp_log two_pos, one_div, inv_pow]

private theorem mgfSlack_le {κ : ℕ} (hK : (1 + 1 / 2 ^ 36 : ℝ) ^ (4 * 2 ^ κ) ≤ 1 + 1 / 2 ^ 24) :
    mgfSlack κ ≤ 1 / 2 ^ 24 + (2 + 1 / 2 ^ 24) / 2 ^ 12 := by
  unfold mgfSlack
  have hK1 : (1 : ℝ) ≤ (1 + 1 / 2 ^ 36) ^ (4 * 2 ^ κ) := one_le_pow₀ (by norm_num)
  have hs : Real.sqrt ((1 + 1 / 2 ^ 36 : ℝ) ^ (4 * 2 ^ κ) - 1) ≤ 1 / 2 ^ 12 := by
    rw [show (1 / 2 ^ 12 : ℝ) = Real.sqrt ((1 / 2 ^ 12) ^ 2) from
      (Real.sqrt_sq (by norm_num)).symm]
    exact Real.sqrt_le_sqrt (by norm_num; linarith)
  calc _ ≤ 1 / 2 ^ 24 + (2 + 1 / 2 ^ 24) * (1 / 2 ^ 12) :=
        add_le_add (by linarith) (mul_le_mul (by linarith) hs (Real.sqrt_nonneg _) (by norm_num))
    _ = _ := by ring

private theorem pRejBound_le_of {p : Params} {a : ℝ} {ε : ℝ≥0∞} {c : ℝ} (ha : 2 ≤ a)
    (hε : ε ≤ 2⁻¹ ^ 20) (hc : 0 ≤ c) (hc1 : c ≤ 1)
    (hK : (1 + 1 / 2 ^ 36 : ℝ) ^ (4 * 2 ^ p.fftDepth) ≤ 1 + 1 / 2 ^ 24)
    (hM : ((4 * 2 ^ p.fftDepth : ℕ) : ℝ) * (1 / 2) ^ 20 ≤ 1)
    (h : (1 + (((4 * 2 ^ p.fftDepth : ℕ) : ℝ) * (1 / 2) ^ 20 +
        (((4 * 2 ^ p.fftDepth : ℕ) : ℝ) * (1 / 2) ^ 20) ^ 2)) *
      (4 * 2 ^ p.fftDepth * p.sigma ^ 2 * (1 + (1 / 2 ^ 24 + (2 + 1 / 2 ^ 24) / 2 ^ 12)) /
        ((p.betaSquared : ℝ) + 1)) ≤ c ^ 2) :
    pRejBound p a ε ≤ ENNReal.ofReal c := by
  unfold pRejBound
  refine rpow_le_ofReal_of_le_sq hc hc1 (half_le_div ha) ?_
  have hη := mgfSlack_le hK
  have hR : idealRejectBound p ≤ 4 * 2 ^ p.fftDepth * p.sigma ^ 2 *
      (1 + (1 / 2 ^ 24 + (2 + 1 / 2 ^ 24) / 2 ^ 12)) / ((p.betaSquared : ℝ) + 1) := by
    unfold idealRejectBound
    gcongr
  calc _ ≤ ENNReal.ofReal (1 + (((4 * 2 ^ p.fftDepth : ℕ) : ℝ) * (1 / 2) ^ 20 +
          (((4 * 2 ^ p.fftDepth : ℕ) : ℝ) * (1 / 2) ^ 20) ^ 2)) *
        ENNReal.ofReal (4 * 2 ^ p.fftDepth * p.sigma ^ 2 *
          (1 + (1 / 2 ^ 24 + (2 + 1 / 2 ^ 24) / 2 ^ 12)) / ((p.betaSquared : ℝ) + 1)) :=
        mul_le_mul' (one_add_pow_le_ofReal hε _ hM) (ENNReal.ofReal_le_ofReal hR)
    _ = _ := (ENNReal.ofReal_mul (by positivity)).symm
    _ ≤ _ := ENNReal.ofReal_le_ofReal h

/-- `guessBound ≤ 2⁻ᵇ` from numeric side conditions: `2⁻ᵐ` scales both terms of the numerator,
`2m + j` is the exponent of the far term, `c₀` bounds its square root, `4 · 2^κ = 256 t` and
`b = m - 4`. -/
private theorem guessBound_le_of {p : Params} {a : ℝ} {ε : ℝ≥0∞} {r c₀ : ℝ} (m j b t : ℕ)
    (ha : 2 ≤ a) (hε : ε ≤ 2⁻¹ ^ 20) (hr : pRejBound p a ε ≤ ENNReal.ofReal r) (hr0 : 0 ≤ r)
    (hr1 : r < 1) (h3 : 3 ≤ p.sigmaMin * Real.sqrt (2 * Real.pi))
    (hK : (1 + 1 / 2 ^ 36 : ℝ) ^ (4 * 2 ^ p.fftDepth) ≤ 1 + 1 / 2 ^ 24)
    (hM : ((4 * 2 ^ p.fftDepth : ℕ) : ℝ) * (1 / 2) ^ 20 ≤ 1)
    (hexp : ((2 * m + j : ℕ) : ℝ) * 0.6931471808 ≤ farRadius ^ 2 / (4 * p.sigma ^ 2))
    (hc₀ : 0 ≤ c₀) (hc₁ : (1 / 2) ^ m * c₀ ≤ 1)
    (hF : (1 + (((4 * 2 ^ p.fftDepth : ℕ) : ℝ) * (1 / 2) ^ 20 +
        (((4 * 2 ^ p.fftDepth : ℕ) : ℝ) * (1 / 2) ^ 20) ^ 2)) *
      (4 * 2 ^ p.fftDepth * (2 * (1 + 1 / 2 ^ 24))) * (1 / 2) ^ j ≤ c₀ ^ 2)
    (ht : 4 * 2 ^ p.fftDepth = 256 * t) (ht' : m + 10 ≤ 250 * t) (hmb : m = b + 4)
    (hB : ((1 / 2) ^ 10 + c₀) / (1 - r) ≤ 16) :
    guessBound p a ε ≤ ENNReal.ofReal ((1 / 2) ^ b) := by
  unfold guessBound
  have hr' : (0 : ℝ) < 1 - r := by linarith
  have hden : ENNReal.ofReal (1 - r) ≤ 1 - pRejBound p a ε := by
    rw [ENNReal.ofReal_sub _ hr0, ENNReal.ofReal_one]
    exact tsub_le_tsub_left hr 1
  have h1 : ENNReal.ofReal (1 / (p.sigmaMin * Real.sqrt (2 * Real.pi) - 1)) ≤
      ENNReal.ofReal (1 / 2) :=
    ENNReal.ofReal_le_ofReal (one_div_le_one_div_of_le (by norm_num) (by linarith))
  have hP : (1 / 2 + (1 / 2) ^ 10 : ℝ) ^ (4 * 2 ^ p.fftDepth) ≤ (1 / 2) ^ m * (1 / 2) ^ 10 := by
    rw [ht, pow_mul, ← pow_add]
    calc ((1 / 2 + (1 / 2) ^ 10 : ℝ) ^ 256) ^ t ≤ ((1 / 2) ^ 250) ^ t :=
          pow_le_pow_left₀ (by positivity) (by norm_num) t
      _ = (1 / 2) ^ (250 * t) := (pow_mul _ _ _).symm
      _ ≤ (1 / 2) ^ (m + 10) := pow_le_pow_of_le_one (by norm_num) (by norm_num) ht'
  have hP' : (ENNReal.ofReal (1 / (p.sigmaMin * Real.sqrt (2 * Real.pi) - 1)) +
      (1 - (1 + ε)⁻¹) ^ (1 / 2 : ℝ)) ^ (4 * 2 ^ p.fftDepth) ≤
      ENNReal.ofReal ((1 / 2) ^ m * (1 / 2) ^ 10) := by
    calc _ ≤ (ENNReal.ofReal (1 / 2) + ENNReal.ofReal ((1 / 2) ^ 10)) ^ (4 * 2 ^ p.fftDepth) :=
          pow_le_pow_left₀ zero_le (add_le_add h1 (sqrt_one_sub_inv_le hε)) _
      _ = ENNReal.ofReal ((1 / 2 + (1 / 2) ^ 10) ^ (4 * 2 ^ p.fftDepth)) := by
        rw [← ENNReal.ofReal_add (by norm_num) (by norm_num), ← ENNReal.ofReal_pow (by norm_num)]
      _ ≤ _ := ENNReal.ofReal_le_ofReal hP
  have hF' : ((1 + ε) ^ (4 * 2 ^ p.fftDepth) * ENNReal.ofReal (idealFarBound p)) ^ ((a - 1) / a) ≤
      ENNReal.ofReal ((1 / 2) ^ m * c₀) := by
    refine rpow_le_ofReal_of_le_sq (by positivity) hc₁ (half_le_div ha) ?_
    have he := exp_neg_le_half_pow (2 * m + j) hexp
    have hfar : idealFarBound p ≤
        4 * 2 ^ p.fftDepth * (2 * (1 + 1 / 2 ^ 24)) * (1 / 2) ^ (2 * m + j) := by
      unfold idealFarBound
      gcongr
    have hsq : (1 + (((4 * 2 ^ p.fftDepth : ℕ) : ℝ) * (1 / 2) ^ 20 +
        (((4 * 2 ^ p.fftDepth : ℕ) : ℝ) * (1 / 2) ^ 20) ^ 2)) *
        (4 * 2 ^ p.fftDepth * (2 * (1 + 1 / 2 ^ 24)) * (1 / 2) ^ (2 * m + j)) ≤
        ((1 / 2) ^ m * c₀) ^ 2 := by
      rw [show 2 * m + j = m * 2 + j by ring, pow_add, pow_mul]
      calc _ = (1 + (((4 * 2 ^ p.fftDepth : ℕ) : ℝ) * (1 / 2) ^ 20 +
            (((4 * 2 ^ p.fftDepth : ℕ) : ℝ) * (1 / 2) ^ 20) ^ 2)) *
            (4 * 2 ^ p.fftDepth * (2 * (1 + 1 / 2 ^ 24))) * (1 / 2) ^ j * ((1 / 2) ^ m) ^ 2 := by
            ring
        _ ≤ c₀ ^ 2 * ((1 / 2) ^ m) ^ 2 := mul_le_mul_of_nonneg_right hF (by positivity)
        _ = _ := by ring
    calc _ ≤ ENNReal.ofReal (1 + (((4 * 2 ^ p.fftDepth : ℕ) : ℝ) * (1 / 2) ^ 20 +
            (((4 * 2 ^ p.fftDepth : ℕ) : ℝ) * (1 / 2) ^ 20) ^ 2)) *
          ENNReal.ofReal (4 * 2 ^ p.fftDepth * (2 * (1 + 1 / 2 ^ 24)) * (1 / 2) ^ (2 * m + j)) :=
          mul_le_mul' (one_add_pow_le_ofReal hε _ hM) (ENNReal.ofReal_le_ofReal hfar)
      _ = _ := (ENNReal.ofReal_mul (by positivity)).symm
      _ ≤ _ := ENNReal.ofReal_le_ofReal hsq
  have hB' : (1 / 2) ^ 10 + c₀ ≤ 16 * (1 - r) := (div_le_iff₀ hr').1 hB
  calc _ ≤ (ENNReal.ofReal ((1 / 2) ^ m * (1 / 2) ^ 10) + ENNReal.ofReal ((1 / 2) ^ m * c₀)) /
        ENNReal.ofReal (1 - r) := ENNReal.div_le_div (add_le_add hP' hF') hden
    _ = ENNReal.ofReal (((1 / 2) ^ m * (1 / 2) ^ 10 + (1 / 2) ^ m * c₀) / (1 - r)) := by
      rw [← ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_div_of_pos hr']
    _ ≤ _ := by
      refine ENNReal.ofReal_le_ofReal ((div_le_iff₀ hr').2 ?_)
      subst hmb
      calc (1 / 2 : ℝ) ^ (b + 4) * (1 / 2) ^ 10 + (1 / 2) ^ (b + 4) * c₀ =
            (1 / 2) ^ b * (1 / 2) ^ 4 * ((1 / 2) ^ 10 + c₀) := by ring
        _ ≤ (1 / 2) ^ b * (1 / 2) ^ 4 * (16 * (1 - r)) :=
            mul_le_mul_of_nonneg_left hB' (by positivity)
        _ = _ := by ring

private theorem non_sis_terms_lt_one {qSign qHash maxAttempts e : ℕ} {r : ℝ} (hr0 : 0 ≤ r)
    (hr1 : r < 1) (hqSign : qSign ≤ 2 ^ 64) (hqHash : qHash ≤ 2 ^ 128) (hmax : 486 ≤ maxAttempts)
    (hsum : ((2 : ℝ) ^ 64 + 2 ^ 128 + 1) * (1 / 2) ^ e +
      (2 ^ 64 + 2 ^ 128 + 1) ^ 2 / (2 * (2 ^ 160) ^ 2) + 2 ^ 64 * (r ^ 243) ^ 2 < 1) :
    ((qSign + (qHash + 1) : ℕ) : ℝ≥0∞) * 2⁻¹ ^ e +
        GPVHashAndSign.collisionBound (Bytes 40) qSign (qHash + 1) +
        ENNReal.ofReal (qSign * (0 / (1 - r) + r ^ maxAttempts)) < 1 := by
  have hS : (qSign : ℝ) ≤ 2 ^ 64 := by exact_mod_cast hqSign
  have hH : (qHash : ℝ) ≤ 2 ^ 128 := by exact_mod_cast hqHash
  have hN : ((qSign + (qHash + 1) : ℕ) : ℝ) ≤ 2 ^ 64 + 2 ^ 128 + 1 := by push_cast; linarith
  have hN0 : (0 : ℝ) ≤ ((qSign + (qHash + 1) : ℕ) : ℝ) := Nat.cast_nonneg _
  have hcard : Fintype.card (Bytes 40) = 2 ^ 320 := by
    rw [Fintype.card_congr (arrayVectorEquivFin Byte 40), Fintype.card_fun, Fintype.card_fin]
    have h8 : Fintype.card UInt8 = 2 ^ 8 := by
      rw [← FinEnum.card_eq_fintypeCard]
      rfl
    rw [h8, ← pow_mul]
  have ha : ((qSign + (qHash + 1) : ℕ) : ℝ≥0∞) * 2⁻¹ ^ e ≤
      ENNReal.ofReal ((2 ^ 64 + 2 ^ 128 + 1) * (1 / 2) ^ e) := by
    rw [two_inv_pow_eq, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul hN0]
    exact ENNReal.ofReal_le_ofReal (by gcongr)
  have hb : GPVHashAndSign.collisionBound (Bytes 40) qSign (qHash + 1) ≤
      ENNReal.ofReal ((2 ^ 64 + 2 ^ 128 + 1) ^ 2 / (2 * (2 ^ 160) ^ 2)) := by
    unfold GPVHashAndSign.collisionBound
    rw [hcard]
    have h2 : (2 : ℝ≥0∞) * ((2 ^ 320 : ℕ) : ℝ≥0∞) = ENNReal.ofReal (2 * (2 ^ 160) ^ 2) := by
      rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_pow (by positivity),
        ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_ofNat, ← pow_mul, Nat.cast_pow,
        Nat.cast_ofNat]
    rw [h2, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_pow hN0,
      ← ENNReal.ofReal_div_of_pos (by norm_num)]
    exact ENNReal.ofReal_le_ofReal (by gcongr)
  have hc : ENNReal.ofReal (qSign * (0 / (1 - r) + r ^ maxAttempts)) ≤
      ENNReal.ofReal (2 ^ 64 * (r ^ 243) ^ 2) := by
    refine ENNReal.ofReal_le_ofReal ?_
    rw [zero_div, zero_add, ← pow_mul]
    exact mul_le_mul hS (pow_le_pow_of_le_one hr0 hr1.le hmax) (pow_nonneg hr0 _) (by norm_num)
  calc _ ≤ ENNReal.ofReal ((2 ^ 64 + 2 ^ 128 + 1) * (1 / 2) ^ e) +
        ENNReal.ofReal ((2 ^ 64 + 2 ^ 128 + 1) ^ 2 / (2 * (2 ^ 160) ^ 2)) +
        ENNReal.ofReal (2 ^ 64 * (r ^ 243) ^ 2) := add_le_add (add_le_add ha hb) hc
    _ = ENNReal.ofReal (((2 : ℝ) ^ 64 + 2 ^ 128 + 1) * (1 / 2) ^ e +
        (2 ^ 64 + 2 ^ 128 + 1) ^ 2 / (2 * (2 ^ 160) ^ 2) + 2 ^ 64 * (r ^ 243) ^ 2) := by
      rw [ENNReal.ofReal_add (by positivity) (by positivity),
        ENNReal.ofReal_add (by positivity) (by positivity)]
    _ < 1 := ENNReal.ofReal_lt_one.2 hsum

/-- At Falcon-512, `a ≥ 2` and `ε ≤ 2⁻²⁰`, `pRej ≤ 0.91` (`0.9096` at `a = 2`). -/
theorem falcon512_pRejBound_le {a : ℝ} {ε : ℝ≥0∞} (ha : 2 ≤ a) (hε : ε ≤ 2⁻¹ ^ 20) :
    pRejBound falcon512 a ε ≤ ENNReal.ofReal (91 / 100) := by
  have hd : falcon512.fftDepth = 8 := by decide
  refine pRejBound_le_of ha hε (by norm_num) (by norm_num) ?_ ?_ ?_
  · rw [hd]
    exact (one_add_pow_le (by norm_num) _ (by norm_num)).trans (by norm_num)
  · rw [hd]
    norm_num
  · rw [hd, show falcon512.sigma = 1657366171829776 / 10000000000000 from rfl,
      show falcon512.betaSquared = 34034726 from rfl]
    norm_num

/-- At Falcon-1024, `a ≥ 2` and `ε ≤ 2⁻²⁰`, `pRej ≤ 0.911` (`0.9101` at `a = 2`). -/
theorem falcon1024_pRejBound_le {a : ℝ} {ε : ℝ≥0∞} (ha : 2 ≤ a) (hε : ε ≤ 2⁻¹ ^ 20) :
    pRejBound falcon1024 a ε ≤ ENNReal.ofReal (911 / 1000) := by
  have hd : falcon1024.fftDepth = 9 := by decide
  refine pRejBound_le_of ha hε (by norm_num) (by norm_num) ?_ ?_ ?_
  · rw [hd]
    exact (one_add_pow_le (by norm_num) _ (by norm_num)).trans (by norm_num)
  · rw [hd]
    norm_num
  · rw [hd, show falcon1024.sigma = 16838857144654395 / 100000000000000 from rfl,
      show falcon1024.betaSquared = 70265242 from rfl]
    norm_num

/-- At Falcon-512, `a ≥ 2` and `ε ≤ 2⁻²⁰`, `εpp ≤ 2⁻²³⁸`; the far event dominates. -/
theorem falcon512_guessBound_le {a : ℝ} {ε : ℝ≥0∞} (ha : 2 ≤ a) (hε : ε ≤ 2⁻¹ ^ 20) :
    guessBound falcon512 a ε ≤ 2⁻¹ ^ 238 := by
  have hd : falcon512.fftDepth = 8 := by decide
  rw [two_inv_pow_eq]
  refine guessBound_le_of (c₀ := 1 + 1 / 2 ^ 10) 242 11 238 4 ha hε (falcon512_pRejBound_le ha hε)
    (by norm_num) (by norm_num) falcon512_sigmaMin_sqrt_two_pi_ge_three ?_ ?_ ?_ (by norm_num)
    (by norm_num) ?_ (by rw [hd]; norm_num) (by norm_num) rfl (by norm_num)
  · rw [hd]
    exact (one_add_pow_le (by norm_num) _ (by norm_num)).trans (by norm_num)
  · rw [hd]
    norm_num
  · rw [farRadius, show falcon512.sigma = 1657366171829776 / 10000000000000 from rfl]
    norm_num [modulus]
  · rw [hd]
    norm_num

/-- At Falcon-1024, `a ≥ 2` and `ε ≤ 2⁻²⁰`, `εpp ≤ 2⁻²³⁰`; the far event dominates. -/
theorem falcon1024_guessBound_le {a : ℝ} {ε : ℝ≥0∞} (ha : 2 ≤ a) (hε : ε ≤ 2⁻¹ ^ 20) :
    guessBound falcon1024 a ε ≤ 2⁻¹ ^ 230 := by
  have hd : falcon1024.fftDepth = 9 := by decide
  rw [two_inv_pow_eq]
  refine guessBound_le_of (c₀ := 1 + 1 / 2 ^ 9) 234 12 230 8 ha hε (falcon1024_pRejBound_le ha hε)
    (by norm_num) (by norm_num) falcon1024_sigmaMin_sqrt_two_pi_ge_three ?_ ?_ ?_ (by norm_num)
    (by norm_num) ?_ (by rw [hd]; norm_num) (by norm_num) rfl (by norm_num)
  · rw [hd]
    exact (one_add_pow_le (by norm_num) _ (by norm_num)).trans (by norm_num)
  · rw [hd]
    norm_num
  · rw [farRadius, show falcon1024.sigma = 16838857144654395 / 100000000000000 from rfl]
    norm_num [modulus]
  · rw [hd]
    norm_num

/-- The conclusion of the Falcon-512/1024 headlines at any parameter set, from `pRej ≤ r`,
`εpp ≤ 2⁻ᵉ` and the numeric sum. -/
private theorem non_sis_terms_lt_one_of (hn : 2 * 2 ^ p.fftDepth = p.n) (hdepth : 1 ≤ p.fftDepth)
    (hσ : 1277 / 1000 ≤ p.sigmaMin) (prims : Primitives p) (hex : prims.ExactFFT hn)
    (htgt : prims.fftTarget = Primitives.exactFftTarget p) {a : ℝ} {ε : ℝ≥0∞}
    (hq : prims.SamplerQuality a ε) (hε : ε ≠ ⊤)
    (hr : GenerableRelation (PublicKey p) (SecretKey p) (validKeyPair p))
    (hkeys : HonestKeys p hr) {r : ℝ} {e : ℕ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hrej : pRejBound p a ε ≤ ENNReal.ofReal r) (hguess : guessBound p a ε ≤ 2⁻¹ ^ e)
    {qSign qHash maxAttempts : ℕ} (hqSign : qSign ≤ 2 ^ 64) (hqHash : qHash ≤ 2 ^ 128)
    (hmax : 486 ≤ maxAttempts)
    (hsum : ((2 : ℝ) ^ 64 + 2 ^ 128 + 1) * (1 / 2) ^ e +
      (2 ^ 64 + 2 ^ 128 + 1) ^ 2 / (2 * (2 ^ 160) ^ 2) + 2 ^ 64 * (r ^ 243) ^ 2 < 1) :
    attemptTransport p prims hr (signAttempt p prims) 0 ∧
      attemptRejectBound p hr (signAttempt p prims) r ∧
      idealAttemptResamples p hr (signAttempt p prims) (acceptCondPSF p prims) ∧
      (∀ pk sk, (pk, sk) ∈ support hr.gen → (acceptCondPSF p prims).CorrectAt pk sk) ∧
      idealSamplerGuessBound p hr (acceptCondPSF p prims) (2⁻¹ ^ e) ∧
      ((qSign + (qHash + 1) : ℕ) : ℝ≥0∞) * 2⁻¹ ^ e +
          GPVHashAndSign.collisionBound (Bytes 40) qSign (qHash + 1) +
          ENNReal.ofReal (qSign * (0 / (1 - r) + r ^ maxAttempts)) < 1 := by
  have hrej' : ∀ pk sk, (pk, sk) ∈ support hr.gen → ∀ c,
      Pr{let o ← signAttempt p prims pk sk c}[o = none] ≤ ENNReal.ofReal r :=
    fun pk sk h c => (prob_signAttempt_none_le hn hdepth hσ prims hex htgt hq hε pk sk
      (hkeys pk sk h) c).trans hrej
  have hacc : ∀ pk sk, (pk, sk) ∈ support hr.gen → ∀ c,
      Pr{let o ← signAttempt p prims pk sk c}[o = none] < 1 :=
    fun pk sk h c => (hrej' pk sk h c).trans_lt (ENNReal.ofReal_lt_one.2 hr1)
  refine ⟨fun pk sk _ c => by simp, fun pk sk h c => ENNReal.toReal_le_of_le_ofReal hr0
    (hrej' pk sk h c), fun pk sk h c => resamplesTo_acceptCondPSF prims pk sk c (hacc pk sk h c),
    fun pk sk h => correctAt_acceptCondPSF hn prims hex pk sk (hkeys pk sk h) (hacc pk sk h),
    fun pk sk h c x => (idealSamplerGuessBound_acceptCond hn hdepth hσ prims hex htgt hq hε hr
      hkeys pk sk h c x).trans hguess,
    non_sis_terms_lt_one hr0 hr1 hqSign hqHash hmax hsum⟩

/-- **The hypotheses and the terms other than the collision term of `euf_cma_collision_security`
at Falcon-512.** With Falcon's own attempt as the ideal attempt and its accept-conditional as the
ideal sampler, at exact FFT fields, honest keys and `SamplerQuality a ε` with `a ≥ 2`,
`ε ≤ 2⁻²⁰`: `ε_step = 0`, `pRej = 0.91`, `hCorrect` and `εpp = 2⁻²³⁸`; at `Salt = Bytes 40`,
`qSign ≤ 2^64`, `qHash ≤ 2^128` and `maxAttempts ≥ 486` the exact-match, salt and sampler terms
of its bound, in its own form, sum below one (`0.2291` at the extremes). The collision term is
not bounded.

The result is conditional on `SamplerQuality a ε` at `ε ≤ 2⁻²⁰` and on `HonestKeys`, which no
sampler and no key generation in the repository is shown to satisfy. They are jointly satisfiable
on paper; that is not machine-checked.

`hReg` and `hQ` remain the caller's. `hReg` asks for a `domainSample` that matches the joint law
of the ideal sampler exactly and does not see the secret key; the law of `acceptCondPSF` depends
on the secret basis through the tree. When honest secret keys sharing a public key induce
different laws, `hReg` has no witness and `euf_cma_collision_security` at `acceptCondPSF` is
vacuous. The only `domainSample` in the repository, in `LatticeCryptoTest.Falcon.NonVacuity`,
samples with the basis, so the collision term is not a hardness assumption here. -/
theorem falcon512_non_sis_terms_lt_one (prims : Primitives falcon512)
    (hex : prims.ExactFFT falcon512_two_mul_two_pow_fftDepth)
    (htgt : prims.fftTarget = Primitives.exactFftTarget falcon512)
    {a : ℝ} {ε : ℝ≥0∞} (hq : prims.SamplerQuality a ε) (ha : 2 ≤ a) (hε : ε ≤ 2⁻¹ ^ 20)
    (hr : GenerableRelation (PublicKey falcon512) (SecretKey falcon512) (validKeyPair falcon512))
    (hkeys : HonestKeys falcon512 hr) {qSign qHash maxAttempts : ℕ} (hqSign : qSign ≤ 2 ^ 64)
    (hqHash : qHash ≤ 2 ^ 128) (hmax : 486 ≤ maxAttempts) :
    attemptTransport falcon512 prims hr (signAttempt falcon512 prims) 0 ∧
      attemptRejectBound falcon512 hr (signAttempt falcon512 prims) (91 / 100) ∧
      idealAttemptResamples falcon512 hr (signAttempt falcon512 prims)
        (acceptCondPSF falcon512 prims) ∧
      (∀ pk sk, (pk, sk) ∈ support hr.gen → (acceptCondPSF falcon512 prims).CorrectAt pk sk) ∧
      idealSamplerGuessBound falcon512 hr (acceptCondPSF falcon512 prims) (2⁻¹ ^ 238) ∧
      ((qSign + (qHash + 1) : ℕ) : ℝ≥0∞) * 2⁻¹ ^ 238 +
          GPVHashAndSign.collisionBound (Bytes 40) qSign (qHash + 1) +
          ENNReal.ofReal (qSign * (0 / (1 - 91 / 100) + (91 / 100) ^ maxAttempts)) < 1 :=
  non_sis_terms_lt_one_of falcon512_two_mul_two_pow_fftDepth (by decide)
    (by rw [show falcon512.sigmaMin = 12778336969128337 / 10000000000000000 from rfl]; norm_num)
    prims hex htgt hq (ne_top_of_le_ne_top (by simp) hε) hr hkeys (by norm_num) (by norm_num)
    (falcon512_pRejBound_le ha hε) (falcon512_guessBound_le ha hε) hqSign hqHash hmax
    (by norm_num)

/-- **The hypotheses and the terms other than the collision term of `euf_cma_collision_security`
at Falcon-1024**, as `falcon512_non_sis_terms_lt_one` with `pRej = 0.911` and `εpp = 2⁻²³⁰`
(`0.3907` at the extremes). Conditional on `SamplerQuality a ε` and `HonestKeys` in the same way;
`hReg` and `hQ` remain the caller's, with the same caveat: when honest secret keys sharing a
public key induce different laws of `acceptCondPSF`, `hReg` has no witness and
`euf_cma_collision_security` at `acceptCondPSF` is vacuous. The collision term is SIS at norm
`2β`, which [FGdG+25] (§1.2) note is trivial at Falcon-1024, so `euf_cma_collision_security`
gives no meaningful bound here whatever `εpp` is. -/
theorem falcon1024_non_sis_terms_lt_one (prims : Primitives falcon1024)
    (hex : prims.ExactFFT falcon1024_two_mul_two_pow_fftDepth)
    (htgt : prims.fftTarget = Primitives.exactFftTarget falcon1024)
    {a : ℝ} {ε : ℝ≥0∞} (hq : prims.SamplerQuality a ε) (ha : 2 ≤ a) (hε : ε ≤ 2⁻¹ ^ 20)
    (hr : GenerableRelation (PublicKey falcon1024) (SecretKey falcon1024)
      (validKeyPair falcon1024))
    (hkeys : HonestKeys falcon1024 hr) {qSign qHash maxAttempts : ℕ} (hqSign : qSign ≤ 2 ^ 64)
    (hqHash : qHash ≤ 2 ^ 128) (hmax : 486 ≤ maxAttempts) :
    attemptTransport falcon1024 prims hr (signAttempt falcon1024 prims) 0 ∧
      attemptRejectBound falcon1024 hr (signAttempt falcon1024 prims) (911 / 1000) ∧
      idealAttemptResamples falcon1024 hr (signAttempt falcon1024 prims)
        (acceptCondPSF falcon1024 prims) ∧
      (∀ pk sk, (pk, sk) ∈ support hr.gen → (acceptCondPSF falcon1024 prims).CorrectAt pk sk) ∧
      idealSamplerGuessBound falcon1024 hr (acceptCondPSF falcon1024 prims) (2⁻¹ ^ 230) ∧
      ((qSign + (qHash + 1) : ℕ) : ℝ≥0∞) * 2⁻¹ ^ 230 +
          GPVHashAndSign.collisionBound (Bytes 40) qSign (qHash + 1) +
          ENNReal.ofReal (qSign * (0 / (1 - 911 / 1000) + (911 / 1000) ^ maxAttempts)) < 1 :=
  non_sis_terms_lt_one_of falcon1024_two_mul_two_pow_fftDepth (by decide)
    (by rw [show falcon1024.sigmaMin = 1298280334344292 / 1000000000000000 from rfl]; norm_num)
    prims hex htgt hq (ne_top_of_le_ne_top (by simp) hε) hr hkeys (by norm_num) (by norm_num)
    (falcon1024_pRejBound_le ha hε) (falcon1024_guessBound_le ha hε) hqSign hqHash hmax
    (by norm_num)

end Falcon

end
