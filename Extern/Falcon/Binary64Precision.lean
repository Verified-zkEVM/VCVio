/-
Copyright (c) 2026 XC0R. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XC0R
-/

module
import all Extern.Falcon.Instance
import all Extern.Falcon.Binary64Table
import all Extern.Falcon.Binary64FFT
import all Extern.Falcon.Binary64Coset
import all LatticeCrypto.Falcon.FFTStages
import all LatticeCrypto.Falcon.Concrete.FloatLike
import all LatticeCrypto.Falcon.Concrete.FPR
import all Extern.Falcon.FPR.Decode
import all LatticeCrypto.Falcon.PackedFFT
import all LatticeCrypto.Falcon.Coset
public import Extern.Falcon.Binary64Coset
public import LatticeCrypto.Falcon.Precision
public import LatticeCrypto.Falcon.PrecisionTrueTree
public import LatticeCrypto.Falcon.FFTStagesL2

/-!
# Rényi precision transfer at the binary64 FFT primitives

`binary64FFTPrimitives p hn` and `concretePrimitives p hn` share hash, public-key encoding and
compression, and differ in the three FFT fields: binary64 `fpolyFFT` / `fpolyIFFT` on `FPR`
against the exact packed FFT. This file discharges the hypotheses of
`Falcon.idealExperiment_precision` for that pair:

* with key coefficients in `[-127, 127]`, the two `ffSampling` targets `toFFTTarget` are within
  squared slotwise distance `targetSqDeviation (logn - 1)` (`slotsSqDist_toFFTTarget_binary64`),
  from the `ℓ²` error of the binary64 forward stages (`fwdStagesF_error_l2`) on the hash target,
  whose coefficients in `[0, q)` `FPR.ofInt` reads exactly (checked bit by bit, `decide +kernel`),
  giving `targetFftErrorL2 (logn - 1)` (`sum_norm_coord_binary64FftTarget_sub_sq_le`);
* on sampled pairs with coefficients at most `Z`, the binary64 basis application rounds to the
  same lattice point as the exact one whenever `cosetDeviation (logn - 1) Z < 1/2`, so
  `fromFFTPreimage` agrees (`fromFFTPreimage_binary64_eq`).

`idealExperiment_binary64_precision` is the transfer for `2 ≤ logn ≤ 9`, and
`idealExperiment_binary64_precision_falcon512` its Falcon-512 instance at `λ = 128`, `Z = 80000`,
for trees with leaves in `[σmin, σmax]`, root factor slots at most `24.0001` and the other factor
slots at most `0.9923`, when `K · maxAttempts ≤ 2^18` (`falcon512_budget`).

## What is not proved

* The sampler is ideal on both sides: every `samplerZ` call is answered by the discrete Gaussian.
  `concretePrimitives`' sampler is not covered.
* Only the three FFT conversion fields are binary64. The products and `1/q` of `toFFTTarget`,
  `ffSampling`, and the products and sums of `fromFFTPreimage` are exact on both sides, so this is
  not the binary64 signer of `Extern.Falcon.Sign`. The results are about `FPR`, not the native
  `Float` backend.
* `preimageTailMass` stays an explicit additive term. For keys satisfying the NTRU equation whose
  tree is the true tree, `preimageTailMass_binary64_falcon512_le` bounds the term by
  `K · maxAttempts · 2⁻¹⁰⁰⁰`.
* `2 ≤ logn ≤ 9`, from `landsOnLattice_of_binary64FFTFields`: Falcon-1024 is not covered.
* Key coefficients in `[-127, 127]` and the tree bounds are hypotheses; no real Falcon key or tree
  is shown to satisfy them. The transfer does not tie the tree to the key;
  `preimageTailMass_binary64_falcon512_le` does, through `sk.tree = trueTree falcon512 sk`.
* The bounds are not tight: the key FFT error is bounded slot by slot, every factor slot by its
  level's bound, and the hash target by its coefficient range.
-/

public section

open OracleComp OracleSpec LatticeCrypto Complex
open scoped ENNReal

namespace Falcon.Concrete

open Falcon Falcon.FFTStages Falcon.Concrete.FPR Falcon.Concrete.FPRBridge Falcon.Concrete.Binary64
  Falcon.Concrete.FFTOps

/-! ## `FPR.ofInt` on the hash target range -/

private theorem ofIntOK_target : (List.range 12289).all (fun i => ofIntOK (i : ℤ)) = true := by
  decide +kernel

private theorem ofInt32_exact_of_ofIntOK {v : ℤ} (hok : ofIntOK v = true) :
    toReal (FloatLike.ofInt32 (Int32.ofInt v) : FPR) = v ∧
      FPR.IsNormalOrZero (FloatLike.ofInt32 (Int32.ofInt v) : FPR) := by
  have hdef : (FloatLike.ofInt32 (Int32.ofInt v) : FPR) = FPR.ofInt (Int32.ofInt v).toInt64 := rfl
  rw [hdef]
  set b := FPR.decode (FPR.ofInt (Int32.ofInt v).toInt64) with hb
  have hm : b.mantissa < 2 ^ 52 := FPR.decode_mantissa_lt _
  unfold ofIntOK at hok
  rw [← hb] at hok
  by_cases h0 : v = 0
  · simp only [h0, ite_true, Bool.and_eq_true, beq_iff_eq] at hok
    have hz : FPR.IsZero (FPR.ofInt (Int32.ofInt v).toInt64) := ⟨hok.1, hok.2⟩
    refine ⟨?_, Or.inr hz⟩
    change b.toReal = _
    rw [h0]; unfold FPR.Bits.toReal; simp [hok.1, hok.2]
  · simp only [h0, ite_false, Bool.and_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq,
      beq_iff_eq] at hok
    obtain ⟨⟨⟨he0, hle⟩, hsig⟩, hsgn⟩ := hok
    have hne : b.exponent ≠ 2047 := by omega
    refine ⟨?_, Or.inl ⟨he0, hne⟩⟩
    change b.toReal = _
    rw [FPR.Bits.toReal_eq_of_exponent_ne_2047 b hne]
    have hs : b.significand = v.natAbs * 2 ^ (1075 - b.exponent) := by
      unfold FPR.Bits.significand; simp only [he0, ite_false]; rw [← hsig, Nat.add_comm]
    have hw : b.workExp = b.exponent := by
      unfold FPR.Bits.workExp; exact Nat.max_eq_left (by omega)
    rw [hs, hw, hsgn]
    have hpow : (2 : ℝ) ^ (1075 - b.exponent) * (2 : ℝ) ^ ((b.exponent : ℤ) - 1023 - 52) = 1 := by
      rw [← zpow_natCast, ← zpow_add₀ (by norm_num)]
      have : (((1075 - b.exponent : ℕ) : ℤ) + ((b.exponent : ℤ) - 1023 - 52)) = 0 := by omega
      rw [this, zpow_zero]
    push_cast
    simp only [mul_assoc, hpow, mul_one]
    by_cases hneg : v < 0
    · simp only [hneg, decide_true, ite_true]
      rw [Nat.cast_natAbs, Int.cast_abs, abs_of_neg (by exact_mod_cast hneg)]; ring
    · simp only [hneg, decide_false, Bool.false_eq_true, ite_false]
      rw [Nat.cast_natAbs, Int.cast_abs,
        abs_of_nonneg (by exact_mod_cast (show (0 : ℤ) ≤ v by omega))]
      ring

/-- `FPR.ofInt` is exact on `[0, 12288]`, with a normal or zero result. -/
theorem ofInt32_exact_target {v : ℤ} (h0 : 0 ≤ v) (h1 : v ≤ 12288) :
    toReal (FloatLike.ofInt32 (Int32.ofInt v) : FPR) = v ∧
      FPR.IsNormalOrZero (FloatLike.ofInt32 (Int32.ofInt v) : FPR) := by
  have hok : ofIntOK v = true := by
    have h := List.all_eq_true.mp ofIntOK_target v.toNat
      (List.mem_range.mpr (by omega))
    rwa [show ((v.toNat : ℕ) : ℤ) = v by omega] at h
  exact ofInt32_exact_of_ofIntOK hok

private theorem good_ofInt_target {v : ℤ} (h0 : 0 ≤ v) (h1 : v ≤ 12288) :
    Good 1 12288 (FloatLike.ofInt32 (Int32.ofInt v) : FPR) := by
  obtain ⟨he, hn⟩ := ofInt32_exact_target h0 h1
  refine ⟨hn, ?_, ?_⟩
  · rw [he]
    by_cases h : v = 0
    · left; simp [h]
    · right; exact_mod_cast Int.one_le_abs h
  · rw [he, abs_of_nonneg (by exact_mod_cast h0)]; exact_mod_cast h1

/-! ## The assembled preimage -/

/-- **`fromFFTPreimage` at the binary64 and exact FFT fields agree** on sampled pairs with
coefficients at most `Z`, for keys with coefficients in `[-127, 127]` and
`cosetDeviation (logn - 1) Z < 1/2`. -/
theorem fromFFTPreimage_binary64_eq (p : Params) (hn : p.n = 2 ^ p.logn) (h2 : 2 ≤ p.logn)
    (h9 : p.logn ≤ 9) (sk : SecretKey p) (hkey : KeyCoeffsLe127 sk) (Z : ℝ)
    (hdev : cosetDeviation p.fftDepth Z < 1 / 2) (c : Rq p.n) (z : FFTPair p.fftDepth)
    (hz : PreimageCoeffsLe p.fftDepth Z z) :
    fromFFTPreimage p (binary64FFTPrimitives p hn) c sk z =
      fromFFTPreimage p (concretePrimitives p hn) c sk z := by
  have h : 2 * 2 ^ p.fftDepth = p.n := by
    rw [hn, Params.fftDepth, ← pow_succ']; congr 1; omega
  have hb := binary64FFTPrimitives_binary64FFTFields p hn
  refine fromFFTPreimage_eq_of_exactFFT h _ _ (concretePrimitives_exactFFT p hn h) sk Z
    (fun a b ha hb' => ⟨?_, ?_⟩) c z hz
  · rw [hb.ifftRound_eq, hb.fftInt_eq]
    apply binary64IfftRound_eq p h2 h9 h _ _ _ _ _ _ hdev
    · intro j
      rw [ofCoeffs_latticePoint]
      exact coord_products_sub p hn h2 h9 h a b Z ha hb' _ _ (fun i => (hkey i).2.1)
        (fun i => (hkey i).2.2.2) j
    · intro j
      rw [ofCoeffs_latticePoint]
      exact norm_coord_products_le p h a b Z ha hb' _ _ (fun i => (hkey i).2.1)
        (fun i => (hkey i).2.2.2) j
  · have hneg : (RealFFTPoly.ofCoeffs p.fftDepth fun i => ((-(intPolyMul
        (Poly.ofPi fun i => a (Fin.cast h.symm i)) sk.f + intPolyMul
        (Poly.ofPi fun i => b (Fin.cast h.symm i)) sk.capF)).get (Fin.cast h i) : ℝ)) =
        -(RealFFTPoly.ofCoeffs p.fftDepth fun i => ((intPolyMul
        (Poly.ofPi fun i => a (Fin.cast h.symm i)) sk.f + intPolyMul
        (Poly.ofPi fun i => b (Fin.cast h.symm i)) sk.capF).get (Fin.cast h i) : ℝ)) := by
      rw [← RealFFTPoly.ofCoeffs_neg]; congr 1; funext i; rw [Poly.get_neg]; push_cast; rfl
    rw [hb.ifftRound_eq, hb.fftInt_eq]
    apply binary64IfftRound_eq p h2 h9 h _ _ _ _ _ _ hdev
    · intro j
      rw [hneg, ofCoeffs_latticePoint, RealFFTPoly.coord_neg, RealFFTPoly.coord_neg,
        show ∀ x y : ℂ, -x - -y = -(x - y) from fun x y => by ring, norm_neg]
      exact coord_products_sub p hn h2 h9 h a b Z ha hb' _ _ (fun i => (hkey i).1)
        (fun i => (hkey i).2.2.1) j
    · intro j
      rw [hneg, ofCoeffs_latticePoint, RealFFTPoly.coord_neg, norm_neg]
      exact norm_coord_products_le p h a b Z ha hb' _ _ (fun i => (hkey i).1)
        (fun i => (hkey i).2.2.1) j

/-! ## The squared target distance -/

/-- **`ℓ²` error of the binary64 forward stages.** For `k ≤ 8` inputs that are `Good` (nonzero
entries at least `2^(-79)` and all at most `M0`, with `16 · 8^k · M0 ≤ 2^1023`) and have `ℓ²` norm
at most `√2^k · A`, the `k` forward stages of `fpolyFFT` end within
`k · ηF · 2^k · (1 + ηF)^(k-1) · A` of the exact stages in `ℓ²`. -/
theorem fwdStagesF_error_l2 (k : ℕ) (hk : k ≤ 8) (X : ℕ → FPR × FPR) (m0 M0 A : ℝ)
    (hm0 : (2 : ℝ) ^ (-(79 : ℤ)) ≤ m0) (hMb : 16 * (8 ^ k * M0) ≤ 2 ^ (1023 : ℤ))
    (hX : ∀ q < 2 ^ k, GoodP m0 M0 (X q))
    (hXA : rangeL2 (2 ^ k) (fun q => cplx (X q)) ≤ √2 ^ k * A) :
    rangeL2 (2 ^ k) (fun q => cplx (fwdStagesF k k X q) - fwdStages k k (fun q => cplx (X q)) q) ≤
      k * etaF * 2 ^ k * (1 + etaF) ^ (k - 1) * A := by
  have hm0' : 0 ≤ m0 := le_trans (by positivity) hm0
  have hM0 : 0 ≤ M0 := (abs_nonneg _).trans (hX 0 (by positivity)).1.2.2
  have hloc : ∀ s < k, (∀ q < 2 ^ k, GoodP (lowAt m0 s) (8 ^ s * M0) (fwdStagesF k s X q)) →
      (∀ q < 2 ^ k, GoodP (lowAt m0 (s + 1)) (8 ^ (s + 1) * M0) (fwdStagesF k (s + 1) X q)) ∧
      rangeL2 (2 ^ k) (fun q => cplx (fwdStagesF k (s + 1) X q) -
        fwdStage k s (fun q => cplx (fwdStagesF k s X q)) q) ≤
        √2 * etaF * rangeL2 (2 ^ k) (fun q => cplx (fwdStagesF k s X q)) + 0 := by
    intro s hs hP
    set H := 2 ^ (k - 1 - s) with hHdef
    have hHpos : 0 < H := by positivity
    have hdvd : 2 * H ∣ 2 ^ k := two_mul_two_pow_dvd hs
    have hsk : s ≤ 7 := by omega
    have hMs : 16 * (8 ^ s * M0) ≤ (2 : ℝ) ^ (1023 : ℤ) := by
      have h8 : (8 : ℝ) ^ s ≤ 8 ^ k := pow_le_pow_right₀ (by norm_num) (by omega)
      exact le_trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h8 hM0)
        (by norm_num)) hMb
    have bf : ∀ c < 2 ^ s, ∀ a b, a < 2 ^ k → b < 2 ^ k →
        ‖cplx (fwdBFF (gmPair (2 ^ (s + 1) + c)) (fwdStagesF k s X a, fwdStagesF k s X b)).1 -
            (fwdBF (twiddle s c) (cplx (fwdStagesF k s X a), cplx (fwdStagesF k s X b))).1‖ ≤
            etaF * max ‖cplx (fwdStagesF k s X a)‖ ‖cplx (fwdStagesF k s X b)‖ ∧
        ‖cplx (fwdBFF (gmPair (2 ^ (s + 1) + c)) (fwdStagesF k s X a, fwdStagesF k s X b)).2 -
            (fwdBF (twiddle s c) (cplx (fwdStagesF k s X a), cplx (fwdStagesF k s X b))).2‖ ≤
            etaF * max ‖cplx (fwdStagesF k s X a)‖ ‖cplx (fwdStagesF k s X b)‖ ∧
        GoodP (lowAt m0 (s + 1)) (8 ^ (s + 1) * M0)
          (fwdBFF (gmPair (2 ^ (s + 1) + c)) (fwdStagesF k s X a, fwdStagesF k s X b)).1 ∧
        GoodP (lowAt m0 (s + 1)) (8 ^ (s + 1) * M0)
          (fwdBFF (gmPair (2 ^ (s + 1) + c)) (fwdStagesF k s X a, fwdStagesF k s X b)).2 := by
      intro c hc a b ha hb
      obtain ⟨hgt, htw⟩ := gmPair_twiddle hsk hc
      obtain ⟨e1, e2, g1, g2⟩ := fwdBFF_error (m := lowAt m0 s) (M := 8 ^ s * M0)
        (ms := 2 ^ (-(9 : ℤ))) (σ := twiddle s c) _ _ _ (hP a ha) (hP b hb) hgt
        (lowAt_nonneg hm0' s) (by positivity) (zpow_le_one_of_nonpos₀ (by norm_num) (by norm_num))
        (low_ok hm0 hsk) hMs htw (le_max_left _ _) (le_max_right _ _)
      rw [nextLow_lowAt, show 8 * (8 ^ s * M0) = 8 ^ (s + 1) * M0 by ring] at g1 g2
      refine ⟨?_, ?_, g1, g2⟩
      · exact e1.trans (le_of_eq (by unfold etaF; ring))
      · exact e2.trans (le_of_eq (by unfold etaF; ring))
    refine ⟨fun q hq => ?_, ?_⟩
    · change GoodP _ _ (bfStage H _ (fwdStagesF k s X) q)
      unfold bfStage
      split_ifs with hr
      · exact (bf _ (block_lt hs hq) q (q + H) hq (add_half_lt hdvd hHpos hq hr)).2.2.1
      · have := (mod_div_sub_half hHpos hr).1
        exact (bf _ (block_lt hs hq) (q - H) q (by omega) hq).2.2.2
    · refine (rangeL2_le_of_pairMax (2 ^ k) (2 ^ s) H (two_pow_eq_blocks hs) _
        (fun q => cplx (fwdStagesF k s X q)) 0 etaF le_rfl etaF_nonneg fun q hq => ?_).trans
          (le_of_eq (by rw [zero_mul]))
      change ‖cplx (bfStage H _ (fwdStagesF k s X) q) - bfStage H (fun c => fwdBF (twiddle s c))
        (fun q => cplx (fwdStagesF k s X q)) q‖ ≤ _
      unfold pairMax bfStage
      split_ifs with hr
      · dsimp only
        rw [zero_add, Complex.norm_real, Real.norm_of_nonneg (le_max_of_le_left (norm_nonneg _))]
        exact (bf _ (block_lt hs hq) q (q + H) hq (add_half_lt hdvd hHpos hq hr)).1
      · have := (mod_div_sub_half hHpos hr).1
        dsimp only
        rw [zero_add, Complex.norm_real, Real.norm_of_nonneg (le_max_of_le_left (norm_nonneg _))]
        exact (bf _ (block_lt hs hq) (q - H) q (by omega) hq).2.1
  obtain ⟨-, -, he⟩ := stages_error_l2 (2 ^ k) k (fun s q => cplx (fwdStagesF k s X q))
    (fun s => fwdStages k s (fun q => cplx (X q))) (fwdStage k)
    (fun s => ∀ q < 2 ^ k, GoodP (lowAt m0 s) (8 ^ s * M0) (fwdStagesF k s X q)) (√2 * etaF) 0
    (√2 ^ k * A) (mul_nonneg (Real.sqrt_nonneg _) etaF_nonneg)
    (fun s hs y z => (rangeL2_fwdStage_sub hs y z).le) (fun s hs y => (rangeL2_fwdStage hs y).le)
    (fun s => rfl) (fun q _ => rfl) hXA (by simpa [lowAt, fwdStagesF] using hX) hloc k le_rfl
  rwa [zero_mul, add_zero, stages_error_l2_bound_eq] at he

/-- The bound `k · ηF · 2^k · (1 + ηF)^(k-1) · 17379` on the `ℓ²` error of the binary64 `fftTarget`
of a hash target with coefficients in `[0, 12288]` (`17379 ≥ √2 · 12288` bounds each complex input
slot). -/
@[expose] noncomputable def targetFftErrorL2 (k : ℕ) : ℝ :=
  k * etaF * 2 ^ k * (1 + etaF) ^ (k - 1) * 17379

/-- **The `ℓ²` error of the binary64 `fftTarget`.** For `2 ≤ logn ≤ 9`, the squared slot errors of
the binary64 `fftTarget` of a hash target against the exact packed FFT of its coefficients in
`[0, q)` sum to at most `targetFftErrorL2 (logn - 1) ^ 2`. -/
theorem sum_norm_coord_binary64FftTarget_sub_sq_le (p : Params) (hn : p.n = 2 ^ p.logn)
    (h2 : 2 ≤ p.logn) (h9 : p.logn ≤ 9) (h : 2 * 2 ^ p.fftDepth = p.n) (c : Rq p.n) :
    ∑ j, ‖RealFFTPoly.coord (binary64FftTarget p c) j - RealFFTPoly.coord
      (RealFFTPoly.ofCoeffs p.fftDepth fun i => (((c.get (Fin.cast h i)).val : ℕ) : ℝ)) j‖ ^ 2 ≤
      targetFftErrorL2 p.fftDepth ^ 2 := by
  set k := p.fftDepth with hk
  have hk1 : k = p.logn - 1 := rfl
  have hpow : 2 ^ p.logn = 2 * 2 ^ k := by rw [hk1, ← pow_succ']; congr 1; omega
  set F : ℕ → ℤ := fun i => if hi : i < p.n then (((c.get ⟨i, hi⟩).val : ℕ) : ℤ) else 0 with hF
  have hFb : ∀ i < 2 ^ p.logn, 0 ≤ F i ∧ F i ≤ 12288 := by
    intro i hi
    simp only [hF, show i < p.n by omega, dite_true]
    have hlt : (c.get ⟨i, by omega⟩).val < 12289 := ZMod.val_lt _
    exact ⟨by positivity, by exact_mod_cast (show (c.get ⟨i, by omega⟩).val ≤ 12288 by omega)⟩
  set ints := Array.ofFn fun i : Fin p.n => Int32.ofInt ((c.get i).val : ℤ) with hints
  have hintsF : ∀ i < 2 ^ p.logn, ints.getD i 0 = Int32.ofInt (F i) := by
    intro i hi
    simp [hints, hF, show i < p.n by omega, Array.getD_eq_getD_getElem?]
  set a := fpolySetSmall (F := FPR) p.logn ints with hadef
  have ha : a.size = 2 * 2 ^ k := by rw [hadef, size_fpolySetSmall, hpow]
  have hX : ∀ q < 2 ^ k, cv (2 ^ k) a q = (FloatLike.ofInt32 (Int32.ofInt (F q)),
      FloatLike.ofInt32 (Int32.ofInt (F (q + 2 ^ k)))) := by
    intro q hq
    simp only [cv, hadef]
    rw [getElem!_fpolySetSmall _ _ _ (by omega), getElem!_fpolySetSmall _ _ _ (by omega),
      hintsF _ (by omega), hintsF _ (by omega)]
  have hval : ∀ q < 2 ^ k, cplx (cv (2 ^ k) a q) = (F q : ℂ) + I * (F (q + 2 ^ k) : ℂ) := by
    intro q hq
    rw [hX q hq]
    have e1 := (ofInt32_exact_target (hFb q (by omega)).1 (hFb q (by omega)).2).1
    have e2 := (ofInt32_exact_target (hFb (q + 2 ^ k) (by omega)).1
      (hFb (q + 2 ^ k) (by omega)).2).1
    apply Complex.ext <;> simp [cplx, e1, e2]
  have hgood : ∀ q < 2 ^ k, GoodP 1 12288 (cv (2 ^ k) a q) := by
    intro q hq
    rw [hX q hq]
    exact ⟨good_ofInt_target (hFb q (by omega)).1 (hFb q (by omega)).2,
      good_ofInt_target (hFb _ (by omega)).1 (hFb _ (by omega)).2⟩
  have hsq : ∀ q < 2 ^ k, ‖cplx (cv (2 ^ k) a q)‖ ^ 2 ≤ 17379 ^ 2 := by
    intro q hq
    have h1 := hFb q (by omega)
    have h2 := hFb (q + 2 ^ k) (by omega)
    have r1 : (0 : ℝ) ≤ F q ∧ (F q : ℝ) ≤ 12288 := ⟨by exact_mod_cast h1.1, by exact_mod_cast h1.2⟩
    have r2 : (0 : ℝ) ≤ F (q + 2 ^ k) ∧ (F (q + 2 ^ k) : ℝ) ≤ 12288 :=
      ⟨by exact_mod_cast h2.1, by exact_mod_cast h2.2⟩
    rw [hval q hq, ← Complex.ofReal_intCast, ← Complex.ofReal_intCast,
      norm_ofReal_add_I_mul_sq]
    nlinarith
  have hXA : rangeL2 (2 ^ k) (fun q => cplx (cv (2 ^ k) a q)) ≤ √2 ^ k * 17379 := by
    unfold rangeL2
    calc _ ≤ √(2 ^ k * 17379 ^ 2) := by
          refine Real.sqrt_le_sqrt ((Finset.sum_le_sum fun q hq =>
            hsq q (Finset.mem_range.mp hq)).trans (le_of_eq ?_))
          simp
      _ = √2 ^ k * 17379 := by
          rw [show (2 : ℝ) ^ k * 17379 ^ 2 = (√2 ^ k * 17379) ^ 2 by
            rw [mul_pow, ← pow_mul, mul_comm k 2, pow_mul, Real.sq_sqrt (by norm_num)]]
          exact Real.sqrt_sq (by positivity)
  have hl2 := fwdStagesF_error_l2 k (by omega) (cv (2 ^ k) a) 1 12288 17379 (by norm_num)
    (eight_pow_bound (by omega) (by norm_num) (by norm_num)) hgood hXA
  have hout : (fpolyFFT p.logn a).size = 2 * 2 ^ k := size_fpolyFFT p.logn h2 a ha
  have hslot : ∀ j : Fin (2 ^ p.fftDepth),
      RealFFTPoly.coord (binary64FftTarget p c) j - RealFFTPoly.coord
        (RealFFTPoly.ofCoeffs p.fftDepth fun i => (((c.get (Fin.cast h i)).val : ℕ) : ℝ)) j =
      cplx (fwdStagesF k k (cv (2 ^ k) a) j.1) -
        fwdStages k k (fun q => cplx (cv (2 ^ k) a q)) j.1 := by
    intro j
    have hj : j.1 < 2 ^ k := j.2
    have hcv := cv_eq_getD (2 ^ k) (fpolyFFT p.logn a) j.1 (by rw [hout]; omega)
    have hleft : RealFFTPoly.coord (binary64FftTarget p c) j = cplx (cv (2 ^ k)
        (fpolyFFT p.logn a) j.1) := by
      rw [hcv]
      apply Complex.ext <;>
        simp [binary64FftTarget, binary64FFTOf, RealFFTPoly.coord, RealFFTPoly.re,
          RealFFTPoly.im, cplx, hints, hadef, hk, Params.fftDepth, floatLike_zero_fpr]
    have hright : RealFFTPoly.coord (RealFFTPoly.ofCoeffs p.fftDepth fun i =>
        (((c.get (Fin.cast h i)).val : ℕ) : ℝ)) j =
        fwdStages k k (fun q => cplx (cv (2 ^ k) a q)) j.1 := by
      rw [coord_ofCoeffs_eq_fwdStages]
      apply fwdStages_congr _ _ le_rfl _ _ _ j.1 hj
      intro r hr
      have hr' : r < 2 ^ p.fftDepth := hr
      rw [hval r hr']
      have h1 : r < p.n := by omega
      have h2' : r + 2 ^ p.fftDepth < p.n := by omega
      simp [complexify, extend, hF, hk, h1, h2', show r < 2 * 2 ^ p.fftDepth by omega,
        show r + 2 ^ p.fftDepth < 2 * 2 ^ p.fftDepth by omega]
      rfl
    rw [hleft, hright]
    exact congrArg (fun x => cplx x - _) (cv_fpolyFFT p.logn h2 a ha j.1 hj)
  simp only [hslot]
  rw [Fin.sum_univ_eq_sum_range (fun q => ‖cplx (fwdStagesF k k (cv (2 ^ k) a) q) -
    fwdStages k k (fun q => cplx (cv (2 ^ k) a q)) q‖ ^ 2) (2 ^ k), ← rangeL2_sq]
  exact pow_le_pow_left₀ (rangeL2_nonneg _ _) hl2 2

/-- The bound on the squared slotwise distance of the binary64 and exact `toFFTTarget`, for keys
with coefficients in `[-127, 127]`:
`2 · ((targetFftErrorL2 k · (2^(k+1) · 127 + fftError k) + 2^k · 17379 · fftError k) / q)²`. -/
@[expose] noncomputable def targetSqDeviation (k : ℕ) : ℝ :=
  2 * ((targetFftErrorL2 k * (2 ^ (k + 1) * 127 + fftError k) +
    2 ^ k * 17379 * fftError k) / 12289) ^ 2

/-- **The `ffSampling` targets at the binary64 and exact FFT fields**, for keys with
coefficients in `[-127, 127]`: squared slotwise distance at most `targetSqDeviation (logn - 1)`.
-/
theorem slotsSqDist_toFFTTarget_binary64 (p : Params) (hn : p.n = 2 ^ p.logn) (h2 : 2 ≤ p.logn)
    (h9 : p.logn ≤ 9) (sk : SecretKey p) (hkey : KeyCoeffsLe127 sk) (c : Rq p.n) :
    slotsSqDist (toFFTTarget p (binary64FFTPrimitives p hn) c sk).1
        (toFFTTarget p (concretePrimitives p hn) c sk).1 +
      slotsSqDist (toFFTTarget p (binary64FFTPrimitives p hn) c sk).2
        (toFFTTarget p (concretePrimitives p hn) c sk).2 ≤ targetSqDeviation p.fftDepth := by
  have h : 2 * 2 ^ p.fftDepth = p.n := by
    rw [hn, Params.fftDepth, ← pow_succ']; congr 1; omega
  have hex := concretePrimitives_exactFFT p hn h
  have htgt : ∀ c : Rq p.n, (concretePrimitives p hn).fftTarget c =
      RealFFTPoly.ofCoeffs p.fftDepth fun i => (((c.get (Fin.cast h i)).val : ℕ) : ℝ) := fun c => by
    simp [concretePrimitives, Primitives.exactFftTarget, h]
  have hL : 0 ≤ targetFftErrorL2 p.fftDepth := by
    have := etaF_nonneg; unfold targetFftErrorL2; positivity
  refine slotsSqDist_toFFTTarget_le h _ _ hex.fftInt_eq htgt hL (fftError_nonneg _)
    (fun c => ?_) (fun u hu j => ?_) sk (fun i => ⟨(hkey i).1, (hkey i).2.2.1⟩) c
  · rw [htgt]; exact sum_norm_coord_binary64FftTarget_sub_sq_le p hn h2 h9 h c
  · rw [hex.fftInt_eq]; exact coord_binary64FftInt_sub p hn h2 h9 h u hu j

/-! ## The transfer -/

/-- **Rényi precision transfer at the binary64 FFT primitives**, for `2 ≤ logn ≤ 9`, keys with
coefficients in `[-127, 127]`, trees with leaves at least `σlo ≥ 1.277`, root factor slots at
most `Lroot` and the other factor slots at most `Lin`, and `Z` with
`cosetDeviation (logn - 1) Z < 1/2`, under the budget
`precisionRate λ σlo · K · maxAttempts · ffSamplingGrowth κ μroot μin · targetSqDeviation κ ≤
log 2 / 2`, `κ = logn - 1`. -/
theorem idealExperiment_binary64_precision (p : Params) (hn : p.n = 2 ^ p.logn)
    (h2 : 2 ≤ p.logn) (h9 : p.logn ≤ 9) (pk : PublicKey p) (sk : SecretKey p)
    (hkey : KeyCoeffsLe127 sk) (Z : ℝ) (hdev : cosetDeviation p.fftDepth Z < 1 / 2)
    (σlo σhi : ℝ) (hσlo : 1277 / 1000 ≤ σlo) (hleaves : sk.tree.LeavesIn σlo σhi)
    (Lroot Lin μroot μin : ℝ) (hμroot : Lroot ^ 2 ≤ (μroot - 1) * (μroot - 1 - Lroot ^ 2))
    (hμroot' : 1 + Lroot ^ 2 ≤ μroot) (hμin : Lin ^ 2 ≤ (μin - 1) * (μin - 1 - Lin ^ 2))
    (hμin' : 1 + Lin ^ 2 ≤ μin) (hfactors : sk.tree.FactorsLeRoot Lroot Lin)
    (lam : ℕ) (hlam : 2 ≤ lam) (maxAttempts K : ℕ)
    (hbudget : precisionRate lam σlo * (K * maxAttempts *
      (ffSamplingGrowth p.fftDepth μroot μin * targetSqDeviation p.fftDepth)) ≤ Real.log 2 / 2)
    {α : Type} [MeasurableSpace α] [Countable α] [MeasurableSingletonClass α]
    (A : OracleComp (unifSpec + signOracleSpec) α) (hK : IsQueryBoundP A IsSignQuery K)
    (T : ℝ≥0∞) (hT : 1 ≤ T) {s : Set α} (hs : MeasurableSet s)
    (hwin : T * (2 : ℝ≥0∞) ^ (-((lam : ℝ) - 1)) <
      𝒟[idealExperiment p (binary64FFTPrimitives p hn) pk sk maxAttempts A] s) :
    T * (2 : ℝ≥0∞) ^ (-(lam : ℝ)) <
      𝒟[idealExperiment p (concretePrimitives p hn) pk sk maxAttempts A] s +
        K * maxAttempts * preimageTailMass p (concretePrimitives p hn) sk Z :=
  idealExperiment_precision (concretePrimitives p hn) (binary64FFTPrimitives p hn)
    (by unfold Params.fftDepth; omega) rfl rfl rfl pk sk (targetSqDeviation p.fftDepth)
    (slotsSqDist_toFFTTarget_binary64 p hn h2 h9 sk hkey) σlo σhi hσlo hleaves Lroot Lin μroot
    μin hμroot hμroot' hμin hμin' hfactors Z
    (fun c z hz => fromFFTPreimage_binary64_eq p hn h2 h9 sk hkey Z hdev c z hz) lam hlam
    maxAttempts K hbudget A hK T hT hs hwin

/-- The Falcon-512 budget: at `λ = 128`, leaves at least `σmin`, growth constants `578.01` (root
factor `24.0001`) and `2.6001` (inner factors `0.9923`), up to `2^18` signing attempts fit. -/
theorem falcon512_budget (m : ℕ) (hm : m ≤ 2 ^ 18) :
    precisionRate 128 falcon512.sigmaMin * (m * (ffSamplingGrowth 8 (57801 / 100)
      (26001 / 10000) * targetSqDeviation 8)) ≤ Real.log 2 / 2 := by
  have hσ : falcon512.sigmaMin = 12778336969128337 / 10000000000000000 := rfl
  have hX : 0 ≤ precisionRate 128 falcon512.sigmaMin *
      (ffSamplingGrowth 8 (57801 / 100) (26001 / 10000) * targetSqDeviation 8) := by
    rw [hσ]
    norm_num [precisionRate, ffSamplingGrowth, targetSqDeviation, targetFftErrorL2, fftError,
      etaF, u]
  have hval : precisionRate 128 falcon512.sigmaMin *
      (ffSamplingGrowth 8 (57801 / 100) (26001 / 10000) * targetSqDeviation 8) * 2 ^ 18 ≤
        34 / 100 := by
    rw [hσ]
    norm_num [precisionRate, ffSamplingGrowth, targetSqDeviation, targetFftErrorL2, fftError,
      etaF, u]
  have hm' : (m : ℝ) ≤ 2 ^ 18 := by exact_mod_cast hm
  calc _ = precisionRate 128 falcon512.sigmaMin *
        (ffSamplingGrowth 8 (57801 / 100) (26001 / 10000) * targetSqDeviation 8) * m := by ring
    _ ≤ _ * 2 ^ 18 := mul_le_mul_of_nonneg_left hm' hX
    _ ≤ 34 / 100 := hval
    _ ≤ Real.log 2 / 2 := by linarith [Real.log_two_gt_d9]

/-- At Falcon-512 the deviation bound is below `1/2` for sampled coefficients up to `80000`. -/
theorem cosetDeviation_falcon512_80000 : cosetDeviation 8 80000 < 1 / 2 := by
  norm_num [cosetDeviation, ifftDeviation, fftError, etaF, etaI, u]

/-- **Rényi precision transfer at the binary64 FFT primitives for Falcon-512**, at `λ = 128` and
`Z = 80000`, for keys with coefficients in `[-127, 127]`, trees with leaves in `[σmin, σmax]`,
root factor slots at most `24.0001` and the other factor slots at most `0.9923`, and an
experiment making at most `K` signing queries with `maxAttempts` attempts each and
`K · maxAttempts ≤ 2^18`: an event of probability above `T · 2^{-127}` when the binary64 bundle
signs with the ideal sampler has probability above `T · 2^{-128}` when the exact bundle does, up
to `K · maxAttempts · preimageTailMass`. The factor bounds are the root check `γroot = 24` of the
modified NTRUGen of ePrint 2026/1531 (Alg. 2, l. 14-15) and its Lemma 8 at `γhybrid = 4`; neither
is a check of Falcon round 3 or FIPS 206 key generation. -/
theorem idealExperiment_binary64_precision_falcon512 (pk : PublicKey falcon512)
    (sk : SecretKey falcon512) (hkey : KeyCoeffsLe127 sk)
    (hleaves : sk.tree.LeavesIn falcon512.sigmaMin falcon512.sigmaMax)
    (hfactors : sk.tree.FactorsLeRoot (240001 / 10000) (9923 / 10000)) (maxAttempts K : ℕ)
    (hKM : K * maxAttempts ≤ 2 ^ 18)
    {α : Type} [MeasurableSpace α] [Countable α] [MeasurableSingletonClass α]
    (A : OracleComp (unifSpec + signOracleSpec) α) (hK : IsQueryBoundP A IsSignQuery K)
    (T : ℝ≥0∞) (hT : 1 ≤ T) {s : Set α} (hs : MeasurableSet s)
    (hwin : T * (2 : ℝ≥0∞) ^ (-((128 : ℕ) - 1 : ℝ)) <
      𝒟[idealExperiment falcon512 (binary64FFTPrimitives falcon512 rfl) pk sk maxAttempts A] s) :
    T * (2 : ℝ≥0∞) ^ (-((128 : ℕ) : ℝ)) <
      𝒟[idealExperiment falcon512 (concretePrimitives falcon512 rfl) pk sk maxAttempts A] s +
        K * maxAttempts * preimageTailMass falcon512 (concretePrimitives falcon512 rfl) sk
          80000 := by
  have hdepth : falcon512.fftDepth = 8 := by decide
  have hσmin : (1277 / 1000 : ℝ) ≤ falcon512.sigmaMin := by
    change (1277 / 1000 : ℝ) ≤ (12778336969128337 : ℝ) / 10000000000000000
    norm_num
  have hb := falcon512_budget (K * maxAttempts) hKM
  push_cast at hb
  exact idealExperiment_binary64_precision falcon512 rfl (by decide) (by decide) pk sk hkey
    80000 cosetDeviation_falcon512_80000 falcon512.sigmaMin falcon512.sigmaMax hσmin hleaves
    (240001 / 10000) (9923 / 10000) (57801 / 100) (26001 / 10000) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hfactors 128 (by norm_num)
    maxAttempts K (by rw [hdepth]; linarith) A hK T hT hs hwin

/-- **The additive term of the binary64 transfer at Falcon-512**: for keys satisfying the NTRU
equation, with coefficients in `[-127, 127]`, whose tree is the true tree with leaves in
`[σmin, σmax]`, `K · maxAttempts · preimageTailMass ≤ K · maxAttempts · 2⁻¹⁰⁰⁰`. -/
theorem preimageTailMass_binary64_falcon512_le (sk : SecretKey falcon512)
    (hntru : ntruEquation falcon512 sk.f sk.g sk.capF sk.capG)
    (htree : sk.tree = trueTree falcon512 sk) (hkey : KeyCoeffsLe127 sk)
    (hleaves : sk.tree.LeavesIn falcon512.sigmaMin falcon512.sigmaMax) (maxAttempts K : ℕ) :
    K * maxAttempts * preimageTailMass falcon512 (concretePrimitives falcon512 rfl) sk 80000 ≤
      K * maxAttempts * ENNReal.ofReal (1 / 2 ^ 1000) := by
  gcongr
  have hfft : (concretePrimitives falcon512 rfl).fftInt = Primitives.exactFftInt falcon512 := rfl
  have htgt : (concretePrimitives falcon512 rfl).fftTarget =
      Primitives.exactFftTarget falcon512 := rfl
  exact preimageTailMass_falcon512_80000_le (concretePrimitives falcon512 rfl) hfft htgt sk
    hntru htree hkey hleaves

end Falcon.Concrete

end
