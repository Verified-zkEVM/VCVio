/-
Copyright (c) 2026 XC0R. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XC0R
-/

module
import all LatticeCrypto.Falcon.Primitives
import all LatticeCrypto.Falcon.PackedFFT
import all LatticeCrypto.Falcon.FFTStages
public import LatticeCrypto.Falcon.FixedPoint.Arith
public import LatticeCrypto.Falcon.FFTStagesL2
public import LatticeCrypto.Falcon.PackedFFT

/-!
# The packed FFT in fixed point with 64 fractional bits

The butterfly stages of `Falcon.FFTStages`, computed with an `Arith64`: the forward stage maps
`(a, b)` to `(a + t, a - t)` with `t = A.mul (A.tw s c) b`, the inverse stage maps `(a, b)` to
`(a + b, A.mul (conj (A.tw s c)) (a - b))`. Additions and subtractions are exact.

The three FFT conversion fields of `Falcon.Primitives`, computed with these stages:

- `Arith64.fftInt` and `Arith64.fftTarget` run the forward stages on the integer coefficients,
  which the format holds exactly;
- `Arith64.ifftRound` reads each real input onto the grid with `A.rnd`, runs the inverse stages,
  scales by `2^(-k)` with `A.rnd`, and rounds each coefficient to the nearest integer.

Error bounds, for every depth `k`:

- `Arith64.fwdStages_error`, `Arith64.invStages_error`: the stage error recursion
  `Falcon.FFTStages.stages_error` with stage factors `etaFwd` and `etaInv`;
- `Arith64.fwdStages_error_l2`: the `ℓ²` error recursion `Falcon.FFTStages.stages_error_l2`;
- `Arith64.coord_fftInt_sub`, `Arith64.coord_fftTarget_sub`: slotwise errors `fftError k` on
  coefficients in `[-127, 127]` and `targetFftError k` on coefficients in `[0, 12288]`;
- `Arith64.sum_norm_coord_fftTarget_sub_sq_le`: the `ℓ²` error `targetFftErrorL2 k` of the
  target transform over all slots;
- `Arith64.ifftRound_eq`: if a real input is within `D` of the packed FFT of an integer vector
  whose slots are bounded by `V`, and `ifftDeviation k D V < 1/2`, the rounded inverse returns
  the integer vector.

The bounds hold for every depth because the model has no subnormal range. They are bounds on
`Arith64`, which does not represent register overflow: they say nothing about an implementation
whose values reach `2^63` in magnitude.
-/

public section

open Complex LatticeCrypto

namespace Falcon.FixedPoint

/-! ## Constants -/

/-- The twiddle table error `0.7072 · 2⁻⁶⁴`. -/
@[expose] noncomputable def twiddleError : ℝ := 7072 / 10000 / 2 ^ 64

/-- The stage factor of the forward stages on inputs bounded by at least `254`:
`0.7072 · 2⁻⁶⁴ + √2 · 2⁻⁶⁴ / 254 ≤ 0.713 · 2⁻⁶⁴`. -/
@[expose] noncomputable def etaFwd : ℝ := 713 / 1000 / 2 ^ 64

/-- The stage factor of the inverse stages on inputs bounded by at least `2^10`:
`2 · 0.7072 · 2⁻⁶⁴ + √2 · 2⁻⁶⁴ / 2^10 ≤ 1.4158 · 2⁻⁶⁴`. -/
@[expose] noncomputable def etaInv : ℝ := 14158 / 10000 / 2 ^ 64

/-- The slotwise error `((2 + ηF)^k - 2^k) · 254` of `Arith64.fftInt` on coefficients in
`[-127, 127]`. -/
@[expose] noncomputable def fftError (k : ℕ) : ℝ := ((2 + etaFwd) ^ k - 2 ^ k) * 254

/-- The slotwise error `((2 + ηF)^k - 2^k) · 24576` of `Arith64.fftTarget` on coefficients in
`[0, 12288]`. -/
@[expose] noncomputable def targetFftError (k : ℕ) : ℝ := ((2 + etaFwd) ^ k - 2 ^ k) * 24576

/-- The `ℓ²` error of `Arith64.fftTarget` over all `2^k` slots:
`k · δ · 2^k · (1 + δ)^(k-1) · 17379 + 2^(k+2) · (1 + δ)^k · 2⁻⁶⁴`, `δ` the twiddle error;
`17379 ≥ √2 · 12288` bounds each complex input slot. -/
@[expose] noncomputable def targetFftErrorL2 (k : ℕ) : ℝ :=
  k * twiddleError * 2 ^ k * (1 + twiddleError) ^ (k - 1) * 17379 +
    2 ^ (k + 2) * (1 + twiddleError) ^ k / 2 ^ 64

/-- The deviation bound of `Arith64.ifftRound`: inputs within `D` of the packed FFT of an integer
vector whose slots are bounded by `V`. -/
@[expose] noncomputable def ifftDeviation (k : ℕ) (D V : ℝ) : ℝ :=
  ((2 + etaInv) ^ k - 2 ^ k) * (V + D + 2 ^ 10) / 2 ^ k + D + 2 / 2 ^ 64

theorem twiddleError_nonneg : 0 ≤ twiddleError := by unfold twiddleError; positivity

theorem fftError_nonneg (k : ℕ) : 0 ≤ fftError k := by
  have he : (0 : ℝ) ≤ etaFwd := by unfold etaFwd; positivity
  have h : (2 : ℝ) ^ k ≤ (2 + etaFwd) ^ k := pow_le_pow_left₀ (by norm_num) (by linarith) k
  unfold fftError
  nlinarith

theorem targetFftErrorL2_nonneg (k : ℕ) : 0 ≤ targetFftErrorL2 k := by
  have := twiddleError_nonneg
  unfold targetFftErrorL2
  positivity

/-! ## Stages -/

namespace Arith64

/-- Stage `s` of the forward transform on `2^k` slots in fixed point. -/
@[expose] noncomputable def fwdStage (A : Arith64) (k s : ℕ) : (ℕ → ℂ) → ℕ → ℂ :=
  FFTStages.bfStage (2 ^ (k - 1 - s)) fun c p =>
    (p.1 + A.mul (A.tw s c) p.2, p.1 - A.mul (A.tw s c) p.2)

/-- Stage `s` of the inverse transform on `2^k` slots in fixed point. -/
@[expose] noncomputable def invStage (A : Arith64) (k s : ℕ) : (ℕ → ℂ) → ℕ → ℂ :=
  FFTStages.bfStage (2 ^ (k - 1 - s)) fun c p =>
    (p.1 + p.2, A.mul ((starRingEnd ℂ) (A.tw s c)) (p.1 - p.2))

/-- The first `s` forward stages in fixed point. -/
@[expose] noncomputable def fwdStages (A : Arith64) (k : ℕ) : ℕ → (ℕ → ℂ) → ℕ → ℂ
  | 0, x => x
  | s + 1, x => A.fwdStage k s (fwdStages A k s x)

/-- The first `j` inverse stages in fixed point. -/
@[expose] noncomputable def invStages (A : Arith64) (k : ℕ) : ℕ → (ℕ → ℂ) → ℕ → ℂ
  | 0, x => x
  | j + 1, x => A.invStage k (k - 1 - j) (invStages A k j x)

end Arith64

/-! ## Packed polynomials and slots -/

/-- The packed polynomial whose slot `j` is `x j`. -/
@[expose] noncomputable def ofSlots (k : ℕ) (x : ℕ → ℂ) : RealFFTPoly k :=
  RealFFTPoly.pack (Vector.ofFn fun j : Fin (2 ^ k) => (x j.1).re)
    (Vector.ofFn fun j : Fin (2 ^ k) => (x j.1).im)

/-- The slots of a packed polynomial, `0` from `2^k` on. -/
@[expose] noncomputable def slots {k : ℕ} (v : RealFFTPoly k) : ℕ → ℂ := fun q =>
  if h : q < 2 ^ k then RealFFTPoly.coord v ⟨q, h⟩ else 0

/-- The real coefficients of `2^k` complex slots: coefficient `m < 2^k` is the real part of slot
`m`, coefficient `m + 2^k` the imaginary part. -/
@[expose] noncomputable def coeffOfSlots (k : ℕ) (y : ℕ → ℂ) (m : ℕ) : ℝ :=
  if m < 2 ^ k then (y m).re else (y (m - 2 ^ k)).im

/-- The coefficients of an integer polynomial on `Fin (2 · 2^(logn - 1))`, `0` from `n` on. -/
@[expose] def intCoeffs (p : Params) (f : IntPoly p.n) : Fin (2 * 2 ^ p.fftDepth) → ℤ :=
  fun i => if h : i.1 < p.n then f.get ⟨i.1, h⟩ else 0

/-- The coefficients of a hash target in `[0, q)` on `Fin (2 · 2^(logn - 1))`, `0` from `n` on. -/
@[expose] def targetCoeffs (p : Params) (c : Rq p.n) : Fin (2 * 2 ^ p.fftDepth) → ℤ :=
  fun i => if h : i.1 < p.n then ((c.get ⟨i.1, h⟩).val : ℤ) else 0

theorem coord_ofSlots (k : ℕ) (x : ℕ → ℂ) (j : Fin (2 ^ k)) :
    RealFFTPoly.coord (ofSlots k x) j = x j := by
  rw [ofSlots, RealFFTPoly.coord_pack]
  apply Complex.ext <;> simp

theorem intCoeffs_eq (p : Params) (h : 2 * 2 ^ p.fftDepth = p.n) (f : IntPoly p.n) :
    (fun i => (intCoeffs p f i : ℝ)) = fun i => (f.get (Fin.cast h i) : ℝ) := by
  funext i
  have hi : i.1 < p.n := by have := i.2; omega
  simp only [intCoeffs, hi, ↓reduceDIte]
  rfl

theorem targetCoeffs_eq (p : Params) (h : 2 * 2 ^ p.fftDepth = p.n) (c : Rq p.n) :
    (fun i => (targetCoeffs p c i : ℝ)) = fun i => (((c.get (Fin.cast h i)).val : ℕ) : ℝ) := by
  funext i
  have hi : i.1 < p.n := by have := i.2; omega
  simp only [targetCoeffs, hi, ↓reduceDIte, Int.cast_natCast]
  rfl

theorem abs_intCoeffs_le (p : Params) (f : IntPoly p.n) (hf : ∀ i, |f.get i| ≤ 127)
    (i : Fin (2 * 2 ^ p.fftDepth)) : |(intCoeffs p f i : ℝ)| ≤ 127 := by
  unfold intCoeffs
  split_ifs
  · exact_mod_cast hf _
  · norm_num

theorem abs_targetCoeffs_le (p : Params) (c : Rq p.n) (i : Fin (2 * 2 ^ p.fftDepth)) :
    |(targetCoeffs p c i : ℝ)| ≤ 12288 := by
  unfold targetCoeffs
  split_ifs with h
  · have hlt : (c.get ⟨i.1, h⟩).val < 12289 := ZMod.val_lt _
    rw [Int.cast_natCast, abs_of_nonneg (Nat.cast_nonneg _)]
    exact_mod_cast (show (c.get ⟨i.1, h⟩).val ≤ 12288 by omega)
  · norm_num

/-! ## The three FFT fields -/

namespace Arith64

/-- The packed FFT of integer coefficients: the forward stages on the complex slots
`fᵣ + i · f_{r + 2^k}`. -/
@[expose] noncomputable def fftOfInts (A : Arith64) (k : ℕ) (f : Fin (2 * 2 ^ k) → ℤ) :
    RealFFTPoly k :=
  ofSlots k (A.fwdStages k k (FFTStages.complexify fun i => (f i : ℝ)))

/-- The fixed-point `fftInt`. -/
@[expose] noncomputable def fftInt (A : Arith64) (p : Params) (f : IntPoly p.n) :
    RealFFTPoly p.fftDepth :=
  A.fftOfInts p.fftDepth (intCoeffs p f)

/-- The fixed-point `fftTarget`: the hash target's coefficients in `[0, q)`. -/
@[expose] noncomputable def fftTarget (A : Arith64) (p : Params) (c : Rq p.n) :
    RealFFTPoly p.fftDepth :=
  A.fftOfInts p.fftDepth (targetCoeffs p c)

/-- The fixed-point `ifftRound`: each real input read onto the grid with `A.rnd`, the inverse
stages, the scaling by `2^(-k)` read with `A.rnd`, then the nearest integer. -/
@[expose] noncomputable def ifftRound (A : Arith64) (p : Params) (v : RealFFTPoly p.fftDepth) :
    IntPoly p.n :=
  Poly.ofPi fun i : Fin p.n =>
    round (A.rnd (coeffOfSlots p.fftDepth (A.invStages p.fftDepth p.fftDepth
      (slots (k := p.fftDepth) (v.map A.rnd))) i.1 / 2 ^ p.fftDepth))

/-! ## Butterfly errors -/

private theorem norm_mul_tw_sub_le (A : Arith64) (s c : ℕ) (b : ℂ) :
    ‖A.mul (A.tw s c) b - FFTStages.twiddle s c * b‖ ≤ √2 / 2 ^ 64 + twiddleError * ‖b‖ := by
  have e : A.mul (A.tw s c) b - FFTStages.twiddle s c * b =
      (A.mul (A.tw s c) b - A.tw s c * b) + (A.tw s c - FFTStages.twiddle s c) * b := by ring
  rw [e]
  refine (norm_add_le _ _).trans (add_le_add (A.mul_err _ _) ?_)
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right (A.tw_err s c) (norm_nonneg _)

private theorem norm_mul_conj_tw_sub_le (A : Arith64) (s c : ℕ) (d : ℂ) :
    ‖A.mul ((starRingEnd ℂ) (A.tw s c)) d - d * (starRingEnd ℂ) (FFTStages.twiddle s c)‖ ≤
      √2 / 2 ^ 64 + twiddleError * ‖d‖ := by
  have e : A.mul ((starRingEnd ℂ) (A.tw s c)) d - d * (starRingEnd ℂ) (FFTStages.twiddle s c) =
      (A.mul ((starRingEnd ℂ) (A.tw s c)) d - (starRingEnd ℂ) (A.tw s c) * d) +
        (starRingEnd ℂ) (A.tw s c - FFTStages.twiddle s c) * d := by
    rw [map_sub]; ring
  rw [e]
  refine (norm_add_le _ _).trans (add_le_add (A.mul_err _ _) ?_)
  rw [norm_mul, Complex.norm_conj]
  exact mul_le_mul_of_nonneg_right (A.tw_err s c) (norm_nonneg _)

/-- The forward butterfly in fixed point is within `√2 · 2⁻⁶⁴ + δ · ‖b‖` of the exact one. -/
private theorem fwd_pair_le (A : Arith64) (s c : ℕ) (p : ℂ × ℂ) :
    ‖(p.1 + A.mul (A.tw s c) p.2) - (FFTStages.fwdBF (FFTStages.twiddle s c) p).1‖ ≤
        √2 / 2 ^ 64 + twiddleError * ‖p.2‖ ∧
      ‖(p.1 - A.mul (A.tw s c) p.2) - (FFTStages.fwdBF (FFTStages.twiddle s c) p).2‖ ≤
        √2 / 2 ^ 64 + twiddleError * ‖p.2‖ := by
  have h := norm_mul_tw_sub_le A s c p.2
  simp only [FFTStages.fwdBF]
  constructor
  · rw [show p.1 + A.mul (A.tw s c) p.2 - (p.1 + FFTStages.twiddle s c * p.2) =
      A.mul (A.tw s c) p.2 - FFTStages.twiddle s c * p.2 by ring]
    exact h
  · rw [show p.1 - A.mul (A.tw s c) p.2 - (p.1 - FFTStages.twiddle s c * p.2) =
      -(A.mul (A.tw s c) p.2 - FFTStages.twiddle s c * p.2) by ring, norm_neg]
    exact h

/-- The inverse butterfly in fixed point is within `√2 · 2⁻⁶⁴ + δ · 2X` of the exact one on
inputs bounded by `X`. -/
private theorem inv_pair_le (A : Arith64) (s c : ℕ) (a b : ℂ) (X : ℝ) (ha : ‖a‖ ≤ X)
    (hb : ‖b‖ ≤ X) :
    ‖(a + b) - (FFTStages.invBF (FFTStages.twiddle s c) (a, b)).1‖ ≤
        √2 / 2 ^ 64 + twiddleError * (2 * X) ∧
      ‖A.mul ((starRingEnd ℂ) (A.tw s c)) (a - b) -
          (FFTStages.invBF (FFTStages.twiddle s c) (a, b)).2‖ ≤
        √2 / 2 ^ 64 + twiddleError * (2 * X) := by
  have hX : 0 ≤ X := (norm_nonneg _).trans ha
  have hδ := twiddleError_nonneg
  have hab : ‖a - b‖ ≤ 2 * X := by linarith [norm_sub_le a b]
  simp only [FFTStages.invBF]
  constructor
  · rw [sub_self, norm_zero]; positivity
  · exact (norm_mul_conj_tw_sub_le A s c (a - b)).trans
      (add_le_add le_rfl (mul_le_mul_of_nonneg_left hab hδ))

/-! ## Stage errors -/

/-- **Error of the fixed-point forward stages.** For inputs bounded by `B` and a stage factor
`η ≥ δ + √2 · 2⁻⁶⁴ / B`, the `k` forward stages end within `((2 + η)^k - 2^k) · B` of the exact
stages. -/
theorem fwdStages_error (A : Arith64) (k : ℕ) (η B : ℝ) (hB : 0 < B)
    (hη : twiddleError + √2 / 2 ^ 64 / B ≤ η) (x : ℕ → ℂ) (hx : ∀ q < 2 ^ k, ‖x q‖ ≤ B) :
    ∀ q < 2 ^ k, ‖A.fwdStages k k x q - FFTStages.fwdStages k k x q‖ ≤
      ((2 + η) ^ k - 2 ^ k) * B := by
  have hδ := twiddleError_nonneg
  have hc : 0 ≤ √2 / 2 ^ 64 / B := div_nonneg (by positivity) hB.le
  have hη0 : 0 ≤ η := by linarith
  have hloc : ∀ s < k, True → (∀ q < 2 ^ k, ‖A.fwdStages k s x q‖ ≤ (2 + η) ^ s * B) →
      True ∧ ∀ q < 2 ^ k, ‖A.fwdStages k (s + 1) x q -
        FFTStages.fwdStage k s (A.fwdStages k s x) q‖ ≤ η * ((2 + η) ^ s * B) := by
    intro s hs _ hu
    refine ⟨trivial, fun q hq => ?_⟩
    have h1 : (1 : ℝ) ≤ (2 + η) ^ s := one_le_pow₀ (by linarith)
    have hX0 : 0 ≤ (2 + η) ^ s * B := mul_nonneg (zero_le_one.trans h1) hB.le
    have hp := FFTStages.bfStage_sub_le_of_pair (FFTStages.two_mul_two_pow_dvd hs)
      (by positivity)
      (fun c p => (p.1 + A.mul (A.tw s c) p.2, p.1 - A.mul (A.tw s c) p.2))
      (fun c => FFTStages.fwdBF (FFTStages.twiddle s c)) (A.fwdStages k s x) ((2 + η) ^ s * B)
      (√2 / 2 ^ 64 + twiddleError * ((2 + η) ^ s * B)) hu
      (fun c a b _ hb => ⟨(fwd_pair_le A s c (a, b)).1.trans
          (add_le_add le_rfl (mul_le_mul_of_nonneg_left hb hδ)),
        (fwd_pair_le A s c (a, b)).2.trans
          (add_le_add le_rfl (mul_le_mul_of_nonneg_left hb hδ))⟩) q hq
    refine hp.trans ?_
    have hcB : √2 / 2 ^ 64 / B * B = √2 / 2 ^ 64 := div_mul_cancel₀ _ hB.ne'
    have h2 : √2 / 2 ^ 64 / B * B ≤ √2 / 2 ^ 64 / B * ((2 + η) ^ s * B) :=
      mul_le_mul_of_nonneg_left (le_mul_of_one_le_left hB.le h1) hc
    have h3 := mul_le_mul_of_nonneg_right hη hX0
    linarith
  exact (FFTStages.stages_error (2 ^ k) k (fun s => A.fwdStages k s x)
    (fun s => FFTStages.fwdStages k s x) (FFTStages.fwdStage k) (fun _ => True) η B hη0 hB.le
    (fun s hs => FFTStages.fwdStage_sub_le hs) (fun s hs => FFTStages.fwdStage_norm_le hs)
    (fun s => rfl) (fun q _ => rfl) hx trivial hloc k le_rfl).2.2

/-- **Error of the fixed-point inverse stages.** For inputs bounded by `B` and a stage factor
`η ≥ 2δ + √2 · 2⁻⁶⁴ / B`, the `k` inverse stages end within `((2 + η)^k - 2^k) · B` of the exact
stages. -/
theorem invStages_error (A : Arith64) (k : ℕ) (η B : ℝ) (hB : 0 < B)
    (hη : 2 * twiddleError + √2 / 2 ^ 64 / B ≤ η) (x : ℕ → ℂ) (hx : ∀ q < 2 ^ k, ‖x q‖ ≤ B) :
    ∀ q < 2 ^ k, ‖A.invStages k k x q - FFTStages.invStages k k x q‖ ≤
      ((2 + η) ^ k - 2 ^ k) * B := by
  have hδ := twiddleError_nonneg
  have hc : 0 ≤ √2 / 2 ^ 64 / B := div_nonneg (by positivity) hB.le
  have hη0 : 0 ≤ η := by linarith
  have hloc : ∀ j < k, True → (∀ q < 2 ^ k, ‖A.invStages k j x q‖ ≤ (2 + η) ^ j * B) →
      True ∧ ∀ q < 2 ^ k, ‖A.invStages k (j + 1) x q -
        FFTStages.invStage k (k - 1 - j) (A.invStages k j x) q‖ ≤ η * ((2 + η) ^ j * B) := by
    intro j hj _ hu
    refine ⟨trivial, fun q hq => ?_⟩
    have hs : k - 1 - j < k := by omega
    have h1 : (1 : ℝ) ≤ (2 + η) ^ j := one_le_pow₀ (by linarith)
    have hX0 : 0 ≤ (2 + η) ^ j * B := mul_nonneg (zero_le_one.trans h1) hB.le
    have hp := FFTStages.bfStage_sub_le_of_pair (FFTStages.two_mul_two_pow_dvd hs)
      (by positivity)
      (fun c p => (p.1 + p.2, A.mul ((starRingEnd ℂ) (A.tw (k - 1 - j) c)) (p.1 - p.2)))
      (fun c => FFTStages.invBF (FFTStages.twiddle (k - 1 - j) c)) (A.invStages k j x)
      ((2 + η) ^ j * B) (√2 / 2 ^ 64 + twiddleError * (2 * ((2 + η) ^ j * B))) hu
      (fun c a b ha hb => inv_pair_le A (k - 1 - j) c a b _ ha hb) q hq
    refine hp.trans ?_
    have hcB : √2 / 2 ^ 64 / B * B = √2 / 2 ^ 64 := div_mul_cancel₀ _ hB.ne'
    have h2 : √2 / 2 ^ 64 / B * B ≤ √2 / 2 ^ 64 / B * ((2 + η) ^ j * B) :=
      mul_le_mul_of_nonneg_left (le_mul_of_one_le_left hB.le h1) hc
    have h3 := mul_le_mul_of_nonneg_right hη hX0
    linarith
  exact (FFTStages.stages_error (2 ^ k) k (fun j => A.invStages k j x)
    (fun j => FFTStages.invStages k j x) (fun j => FFTStages.invStage k (k - 1 - j))
    (fun _ => True) η B hη0 hB.le
    (fun j hj => FFTStages.invStage_sub_le (by omega)) (fun j hj => FFTStages.invStage_norm_le
      (by omega)) (fun j => rfl) (fun q _ => rfl) hx trivial hloc k le_rfl).2.2

private theorem sqrt_two_pow_mul_self (n : ℕ) : √2 ^ n * √2 ^ n = (2 : ℝ) ^ n := by
  rw [← mul_pow, Real.mul_self_sqrt (by norm_num)]

private theorem sqrt_cast_two_pow (k : ℕ) : √((2 ^ k : ℕ) : ℝ) = √2 ^ k := by
  have h : ((2 ^ k : ℕ) : ℝ) = (√2 ^ k) ^ 2 := by
    rw [sq, sqrt_two_pow_mul_self]; push_cast; ring
  rw [h, Real.sqrt_sq (by positivity)]

private theorem sum_geom_le (δ : ℝ) (hδ : 0 ≤ δ) (n : ℕ) :
    ∑ j ∈ Finset.range n, (√2 + √2 * δ) ^ j ≤ (1 + δ) ^ n * ((√2 + 1) * √2 ^ n) := by
  induction n with
  | zero =>
    simp only [Finset.range_zero, Finset.sum_empty, pow_zero, one_mul, mul_one]
    positivity
  | succ n ih =>
    rw [Finset.sum_range_succ]
    have h1 : (1 : ℝ) ≤ 1 + δ := by linarith
    have hp : (1 + δ) ^ n ≤ (1 + δ) ^ (n + 1) := pow_le_pow_right₀ h1 (by omega)
    have e : (√2 + √2 * δ) ^ n = √2 ^ n * (1 + δ) ^ n := by
      rw [show √2 + √2 * δ = √2 * (1 + δ) by ring, mul_pow]
    have h2 : √2 * √2 = (2 : ℝ) := Real.mul_self_sqrt (by norm_num)
    have hq : 0 ≤ (√2 + 1) * √2 ^ (n + 1) := by positivity
    calc _ ≤ (1 + δ) ^ n * ((√2 + 1) * √2 ^ n) + √2 ^ n * (1 + δ) ^ n := by linarith [ih, e]
      _ = (1 + δ) ^ n * ((√2 + 1) * √2 ^ (n + 1)) := by
          linear_combination (-(1 + δ) ^ n * √2 ^ n) * h2
      _ ≤ _ := mul_le_mul_of_nonneg_right hp hq

/-- **`ℓ²` error of the fixed-point forward stages.** For inputs with `ℓ²` norm at most
`√(2^k) · X`, the `k` forward stages end within
`k · δ · 2^k · (1 + δ)^(k-1) · X + 2^(k+2) · (1 + δ)^k · 2⁻⁶⁴` of the exact stages in `ℓ²`. -/
theorem fwdStages_error_l2 (A : Arith64) (k : ℕ) (x : ℕ → ℂ) (X : ℝ) (hX : 0 ≤ X)
    (hx : ∑ q ∈ Finset.range (2 ^ k), ‖x q‖ ^ 2 ≤ 2 ^ k * X ^ 2) :
    √(∑ q ∈ Finset.range (2 ^ k), ‖A.fwdStages k k x q - FFTStages.fwdStages k k x q‖ ^ 2) ≤
      k * twiddleError * 2 ^ k * (1 + twiddleError) ^ (k - 1) * X +
        2 ^ (k + 2) * (1 + twiddleError) ^ k / 2 ^ 64 := by
  have hδ := twiddleError_nonneg
  have hs2 : (0 : ℝ) ≤ √2 := Real.sqrt_nonneg _
  have hX' : FFTStages.rangeL2 (2 ^ k) x ≤ √2 ^ k * X := by
    unfold FFTStages.rangeL2
    calc _ ≤ √(2 ^ k * X ^ 2) := Real.sqrt_le_sqrt hx
      _ = √2 ^ k * X := by
          rw [show (2 : ℝ) ^ k * X ^ 2 = (√2 ^ k * X) ^ 2 by
            rw [mul_pow, sq (√2 ^ k), sqrt_two_pow_mul_self]]
          exact Real.sqrt_sq (by positivity)
  have hloc : ∀ s < k, True → True ∧
      FFTStages.rangeL2 (2 ^ k) (fun q => A.fwdStages k (s + 1) x q -
        FFTStages.fwdStage k s (A.fwdStages k s x) q) ≤
        √2 * twiddleError * FFTStages.rangeL2 (2 ^ k) (A.fwdStages k s x) +
          √2 / 2 ^ 64 * √2 ^ k := by
    intro s hs _
    refine ⟨trivial, ?_⟩
    have h := FFTStages.rangeL2_bfStage_sub_le (2 ^ k) (2 ^ s) (2 ^ (k - 1 - s))
      (FFTStages.two_pow_eq_blocks hs)
      (fun c p => (p.1 + A.mul (A.tw s c) p.2, p.1 - A.mul (A.tw s c) p.2))
      (fun c => FFTStages.fwdBF (FFTStages.twiddle s c)) (A.fwdStages k s x) (√2 / 2 ^ 64)
      twiddleError (by positivity) hδ fun c p =>
        ⟨(fwd_pair_le A s c p).1.trans (add_le_add le_rfl
          (mul_le_mul_of_nonneg_left (le_max_right _ _) hδ)),
        (fwd_pair_le A s c p).2.trans (add_le_add le_rfl
          (mul_le_mul_of_nonneg_left (le_max_right _ _) hδ))⟩
    rw [sqrt_cast_two_pow] at h
    exact h
  obtain ⟨-, -, he⟩ := FFTStages.stages_error_l2 (2 ^ k) k (fun s => A.fwdStages k s x)
    (fun s => FFTStages.fwdStages k s x) (FFTStages.fwdStage k) (fun _ => True)
    (√2 * twiddleError) (√2 / 2 ^ 64 * √2 ^ k) (√2 ^ k * X) (mul_nonneg hs2 hδ)
    (fun s hs y z => (FFTStages.rangeL2_fwdStage_sub hs y z).le)
    (fun s hs y => (FFTStages.rangeL2_fwdStage hs y).le)
    (fun s => rfl) (fun q _ => rfl) hX' trivial hloc k le_rfl
  refine he.trans ?_
  have hii : √2 / 2 ^ 64 * √2 ^ k * ∑ j ∈ Finset.range k, (√2 + √2 * twiddleError) ^ j ≤
      2 ^ (k + 2) * (1 + twiddleError) ^ k / 2 ^ 64 := by
    have hg := sum_geom_le twiddleError hδ k
    have hc : 0 ≤ √2 / 2 ^ 64 * √2 ^ k := by positivity
    have h2 : √2 * √2 = (2 : ℝ) := Real.mul_self_sqrt (by norm_num)
    have hs2' : √2 ≤ 2 := by nlinarith
    have hp : 0 ≤ (1 + twiddleError) ^ k * 2 ^ k := mul_nonneg (pow_nonneg (by linarith) k)
      (by positivity)
    calc _ ≤ √2 / 2 ^ 64 * √2 ^ k * ((1 + twiddleError) ^ k * ((√2 + 1) * √2 ^ k)) :=
          mul_le_mul_of_nonneg_left hg hc
      _ = (1 + twiddleError) ^ k * 2 ^ k * (2 + √2) / 2 ^ 64 := by
          linear_combination ((1 + twiddleError) ^ k / 2 ^ 64 * (√2 * √2 + √2)) *
            sqrt_two_pow_mul_self k + ((1 + twiddleError) ^ k / 2 ^ 64 * 2 ^ k) * h2
      _ ≤ (1 + twiddleError) ^ k * 2 ^ k * 4 / 2 ^ 64 := by
          gcongr
          linarith
      _ = 2 ^ (k + 2) * (1 + twiddleError) ^ k / 2 ^ 64 := by ring
  rw [FFTStages.stages_error_l2_bound_eq]
  linarith

/-! ## Errors of the three fields -/

/-- **The fixed-point packed FFT of integer coefficients.** For coefficients bounded by
`M ≥ 127`, every slot is within `((2 + ηF)^k - 2^k) · 2M` of the exact packed FFT. -/
theorem coord_fftOfInts_sub (A : Arith64) (k : ℕ) (f : Fin (2 * 2 ^ k) → ℤ) (M : ℝ)
    (hM : 127 ≤ M) (hf : ∀ i, |(f i : ℝ)| ≤ M) (j : Fin (2 ^ k)) :
    ‖RealFFTPoly.coord (A.fftOfInts k f) j -
      RealFFTPoly.coord (RealFFTPoly.ofCoeffs k fun i => (f i : ℝ)) j‖ ≤
      ((2 + etaFwd) ^ k - 2 ^ k) * (2 * M) := by
  have hc : ∀ q, ‖FFTStages.complexify (fun i => (f i : ℝ)) q‖ ≤ 2 * M := by
    intro q
    have he : ∀ m, ‖((FFTStages.extend (fun i => (f i : ℝ)) m : ℝ) : ℂ)‖ ≤ M := by
      intro m
      rw [Complex.norm_real, Real.norm_eq_abs]
      unfold FFTStages.extend
      split_ifs
      · exact hf _
      · simp only [abs_zero]; linarith
    unfold FFTStages.complexify
    calc _ ≤ _ := norm_add_le _ _
      _ ≤ M + M := by
          rw [norm_mul, Complex.norm_I, one_mul]
          exact add_le_add (he _) (he _)
      _ = 2 * M := by ring
  have hη : twiddleError + √2 / 2 ^ 64 / (2 * M) ≤ etaFwd := by
    have h1 : √2 / 2 ^ 64 / (2 * M) ≤ 14143 / 10000 / 2 ^ 64 / 254 := by
      calc √2 / 2 ^ 64 / (2 * M) ≤ 14143 / 10000 / 2 ^ 64 / (2 * M) := by
            gcongr; exact sqrt_two_le
        _ ≤ 14143 / 10000 / 2 ^ 64 / 254 := by gcongr; linarith
    have h2 : (7072 / 10000 / 2 ^ 64 : ℝ) + 14143 / 10000 / 2 ^ 64 / 254 ≤
        713 / 1000 / 2 ^ 64 := by
      norm_num
    unfold twiddleError etaFwd
    linarith
  have h := A.fwdStages_error k etaFwd (2 * M) (by linarith) hη _ (fun q _ => hc q) j.1 j.2
  rw [fftOfInts, coord_ofSlots, FFTStages.coord_ofCoeffs_eq_fwdStages]
  exact h

/-- **The fixed-point `fftInt` of a key polynomial.** For coefficients in `[-127, 127]`, every
slot is within `fftError (logn - 1)` of the exact packed FFT. -/
theorem coord_fftInt_sub (A : Arith64) (p : Params) (h : 2 * 2 ^ p.fftDepth = p.n)
    (f : IntPoly p.n) (hf : ∀ i, |f.get i| ≤ 127) (j : Fin (2 ^ p.fftDepth)) :
    ‖RealFFTPoly.coord (A.fftInt p f) j - RealFFTPoly.coord
      (RealFFTPoly.ofCoeffs p.fftDepth fun i => (f.get (Fin.cast h i) : ℝ)) j‖ ≤
      fftError p.fftDepth := by
  have := A.coord_fftOfInts_sub p.fftDepth (intCoeffs p f) 127 le_rfl
    (abs_intCoeffs_le p f hf) j
  rw [intCoeffs_eq p h] at this
  refine this.trans (le_of_eq ?_)
  unfold fftError; ring

/-- **The fixed-point `fftTarget` of a hash target.** Every slot is within
`targetFftError (logn - 1)` of the exact packed FFT of the coefficients in `[0, q)`. -/
theorem coord_fftTarget_sub (A : Arith64) (p : Params) (h : 2 * 2 ^ p.fftDepth = p.n)
    (c : Rq p.n) (j : Fin (2 ^ p.fftDepth)) :
    ‖RealFFTPoly.coord (A.fftTarget p c) j - RealFFTPoly.coord
      (RealFFTPoly.ofCoeffs p.fftDepth fun i => (((c.get (Fin.cast h i)).val : ℕ) : ℝ)) j‖ ≤
      targetFftError p.fftDepth := by
  have := A.coord_fftOfInts_sub p.fftDepth (targetCoeffs p c) 12288 (by norm_num)
    (abs_targetCoeffs_le p c) j
  rw [targetCoeffs_eq p h] at this
  refine this.trans (le_of_eq ?_)
  unfold targetFftError; ring

/-- **The `ℓ²` error of the fixed-point `fftTarget`.** The squared slot errors of the target
transform sum to at most `targetFftErrorL2 (logn - 1) ^ 2`. -/
theorem sum_norm_coord_fftTarget_sub_sq_le (A : Arith64) (p : Params)
    (h : 2 * 2 ^ p.fftDepth = p.n) (c : Rq p.n) :
    ∑ j, ‖RealFFTPoly.coord (A.fftTarget p c) j - RealFFTPoly.coord
      (RealFFTPoly.ofCoeffs p.fftDepth fun i => (((c.get (Fin.cast h i)).val : ℕ) : ℝ)) j‖ ^ 2 ≤
      targetFftErrorL2 p.fftDepth ^ 2 := by
  obtain ⟨x, hx⟩ : ∃ x, x = FFTStages.complexify fun i => (targetCoeffs p c i : ℝ) := ⟨_, rfl⟩
  have hxb : ∑ q ∈ Finset.range (2 ^ p.fftDepth), ‖x q‖ ^ 2 ≤ 2 ^ p.fftDepth * 17379 ^ 2 := by
    calc _ ≤ ∑ _q ∈ Finset.range (2 ^ p.fftDepth), (17379 : ℝ) ^ 2 :=
          Finset.sum_le_sum fun q _ => by
            rw [hx]
            exact (FFTStages.norm_complexify_sq_le _ 12288 (abs_targetCoeffs_le p c) q).trans
              (by norm_num)
      _ = _ := by simp
  have hl2 := A.fwdStages_error_l2 p.fftDepth x 17379 (by norm_num) hxb
  have hsum : ∑ j, ‖RealFFTPoly.coord (A.fftTarget p c) j - RealFFTPoly.coord
      (RealFFTPoly.ofCoeffs p.fftDepth fun i => (((c.get (Fin.cast h i)).val : ℕ) : ℝ)) j‖ ^ 2 =
      ∑ q ∈ Finset.range (2 ^ p.fftDepth),
        ‖A.fwdStages p.fftDepth p.fftDepth x q -
          FFTStages.fwdStages p.fftDepth p.fftDepth x q‖ ^ 2 := by
    rw [← Fin.sum_univ_eq_sum_range (fun q => ‖A.fwdStages p.fftDepth p.fftDepth x q -
      FFTStages.fwdStages p.fftDepth p.fftDepth x q‖ ^ 2)]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← targetCoeffs_eq p h, fftTarget, fftOfInts, coord_ofSlots,
      FFTStages.coord_ofCoeffs_eq_fwdStages, hx]
  rw [hsum]
  have h0 : 0 ≤ ∑ q ∈ Finset.range (2 ^ p.fftDepth),
      ‖A.fwdStages p.fftDepth p.fftDepth x q -
        FFTStages.fwdStages p.fftDepth p.fftDepth x q‖ ^ 2 :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  calc _ = (√(∑ q ∈ Finset.range (2 ^ p.fftDepth),
        ‖A.fwdStages p.fftDepth p.fftDepth x q -
          FFTStages.fwdStages p.fftDepth p.fftDepth x q‖ ^ 2)) ^ 2 := (Real.sq_sqrt h0).symm
    _ ≤ _ := pow_le_pow_left₀ (Real.sqrt_nonneg _) hl2 2

/-! ## The inverse transform -/

/-- Reading a packed polynomial onto the grid moves each slot by at most `2⁻⁶⁴`. -/
theorem norm_coord_map_rnd_sub_le (A : Arith64) {k : ℕ} (v : RealFFTPoly k) (j : Fin (2 ^ k)) :
    ‖RealFFTPoly.coord (v.map A.rnd) j - RealFFTPoly.coord v j‖ ≤ 1 / 2 ^ 64 := by
  have hre : (RealFFTPoly.coord (v.map A.rnd) j - RealFFTPoly.coord v j).re =
      A.rnd (v.re j) - v.re j := by
    simp [RealFFTPoly.coord, RealFFTPoly.re, RealFFTPoly.get_eq_getElem]
  have him : (RealFFTPoly.coord (v.map A.rnd) j - RealFFTPoly.coord v j).im =
      A.rnd (v.im j) - v.im j := by
    simp [RealFFTPoly.coord, RealFFTPoly.im, RealFFTPoly.get_eq_getElem]
  calc _ ≤ |(RealFFTPoly.coord (v.map A.rnd) j - RealFFTPoly.coord v j).re| +
        |(RealFFTPoly.coord (v.map A.rnd) j - RealFFTPoly.coord v j).im| :=
        Complex.norm_le_abs_re_add_abs_im _
    _ ≤ 1 / 2 ^ 65 + 1 / 2 ^ 65 := by
        rw [hre, him]; exact add_le_add (A.rnd_err _) (A.rnd_err _)
    _ = 1 / 2 ^ 64 := by norm_num

private theorem complexify_re {k : ℕ} (f : Fin (2 * 2 ^ k) → ℝ) (q : ℕ) (hq : q < 2 ^ k) :
    (FFTStages.complexify f q).re = f ⟨q, by omega⟩ := by
  simp [FFTStages.complexify, FFTStages.extend, show q < 2 * 2 ^ k by omega]

private theorem complexify_im {k : ℕ} (f : Fin (2 * 2 ^ k) → ℝ) (q : ℕ) (hq : q < 2 ^ k) :
    (FFTStages.complexify f q).im = f ⟨q + 2 ^ k, by omega⟩ := by
  simp [FFTStages.complexify, FFTStages.extend, show q + 2 ^ k < 2 * 2 ^ k by omega]

/-- **The fixed-point `ifftRound` recovers an integer polynomial.** If every slot of `v` is
within `D` of the exact packed FFT of `w`, those slots are bounded by `V`, and
`ifftDeviation (logn - 1) D V < 1/2`, then the fixed-point `ifftRound` of `v` is `w`. -/
theorem ifftRound_eq (A : Arith64) (p : Params) (h : 2 * 2 ^ p.fftDepth = p.n)
    (v : RealFFTPoly p.fftDepth) (w : IntPoly p.n) (D V : ℝ)
    (hD : ∀ j, ‖RealFFTPoly.coord v j - RealFFTPoly.coord
      (RealFFTPoly.ofCoeffs p.fftDepth fun i => (w.get (Fin.cast h i) : ℝ)) j‖ ≤ D)
    (hV : ∀ j, ‖RealFFTPoly.coord
      (RealFFTPoly.ofCoeffs p.fftDepth fun i => (w.get (Fin.cast h i) : ℝ)) j‖ ≤ V)
    (hdev : ifftDeviation p.fftDepth D V < 1 / 2) :
    A.ifftRound p v = w := by
  have hN : 0 < 2 ^ p.fftDepth := by positivity
  have hD0 : 0 ≤ D := (norm_nonneg _).trans (hD ⟨0, hN⟩)
  have hV0 : 0 ≤ V := (norm_nonneg _).trans (hV ⟨0, hN⟩)
  obtain ⟨wR, hwR⟩ : ∃ wR : Fin (2 * 2 ^ p.fftDepth) → ℝ,
      wR = fun i => (w.get (Fin.cast h i) : ℝ) := ⟨_, rfl⟩
  rw [← hwR] at hD hV
  obtain ⟨xs, hxs⟩ : ∃ xs, xs = slots (k := p.fftDepth) (v.map A.rnd) := ⟨_, rfl⟩
  obtain ⟨z, hz⟩ : ∃ z, z = FFTStages.fwdStages p.fftDepth p.fftDepth (FFTStages.complexify wR) :=
    ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B : ℝ, B = V + D + 2 ^ 10 := ⟨_, rfl⟩
  have hB0 : 0 < B := by rw [hB]; positivity
  have hzq : ∀ q (hq : q < 2 ^ p.fftDepth),
      z q = RealFFTPoly.coord (RealFFTPoly.ofCoeffs p.fftDepth wR) ⟨q, hq⟩ := by
    intro q hq
    rw [FFTStages.coord_ofCoeffs_eq_fwdStages, hz]
  have hxq : ∀ q (hq : q < 2 ^ p.fftDepth),
      xs q = RealFFTPoly.coord (v.map A.rnd) ⟨q, hq⟩ := by
    intro q hq
    rw [hxs, slots]
    simp only [hq, ↓reduceDIte]
  have hx1 : ∀ q < 2 ^ p.fftDepth, ‖xs q - z q‖ ≤ D + 1 / 2 ^ 64 := by
    intro q hq
    rw [hxq q hq, hzq q hq]
    calc _ = ‖(RealFFTPoly.coord (v.map A.rnd) ⟨q, hq⟩ - RealFFTPoly.coord v ⟨q, hq⟩) +
          (RealFFTPoly.coord v ⟨q, hq⟩ -
            RealFFTPoly.coord (RealFFTPoly.ofCoeffs p.fftDepth wR) ⟨q, hq⟩)‖ := by
          congr 1; ring
      _ ≤ _ := norm_add_le _ _
      _ ≤ 1 / 2 ^ 64 + D := add_le_add (A.norm_coord_map_rnd_sub_le v _) (hD _)
      _ = D + 1 / 2 ^ 64 := by ring
  have hxB : ∀ q < 2 ^ p.fftDepth, ‖xs q‖ ≤ B := by
    intro q hq
    have h1 := hx1 q hq
    have h2 : ‖z q‖ ≤ V := by rw [hzq q hq]; exact hV _
    have h3 : ‖xs q‖ ≤ ‖z q‖ + ‖xs q - z q‖ := by
      calc ‖xs q‖ = ‖z q + (xs q - z q)‖ := by congr 1; ring
        _ ≤ _ := norm_add_le _ _
    have h4 : (1 : ℝ) / 2 ^ 64 ≤ 2 ^ 10 := by norm_num
    rw [hB]; linarith
  have hη : 2 * twiddleError + √2 / 2 ^ 64 / B ≤ etaInv := by
    have hB10 : (2 : ℝ) ^ 10 ≤ B := by rw [hB]; linarith
    have h1 : √2 / 2 ^ 64 / B ≤ 14143 / 10000 / 2 ^ 64 / 2 ^ 10 := by
      calc √2 / 2 ^ 64 / B ≤ 14143 / 10000 / 2 ^ 64 / B := by gcongr; exact sqrt_two_le
        _ ≤ 14143 / 10000 / 2 ^ 64 / 2 ^ 10 := by gcongr
    have h2 : 2 * (7072 / 10000 / 2 ^ 64 : ℝ) + 14143 / 10000 / 2 ^ 64 / 2 ^ 10 ≤
        14158 / 10000 / 2 ^ 64 := by norm_num
    unfold twiddleError etaInv
    linarith
  have hinv := A.invStages_error p.fftDepth etaInv B hB0 hη xs hxB
  have hsub := FFTStages.invStages_sub_le p.fftDepth p.fftDepth le_rfl xs z (D + 1 / 2 ^ 64) hx1
  have hex : FFTStages.invStages p.fftDepth p.fftDepth z =
      fun q => (((2 : ℝ) ^ p.fftDepth : ℝ) : ℂ) * FFTStages.complexify wR q := by
    rw [hz, FFTStages.invStages_fwdStages]
    funext q
    push_cast
    rfl
  obtain ⟨E1, hE1⟩ : ∃ E1 : ℝ, E1 = ((2 + etaInv) ^ p.fftDepth - 2 ^ p.fftDepth) * B +
      2 ^ p.fftDepth * (D + 1 / 2 ^ 64) := ⟨_, rfl⟩
  have hy : ∀ q < 2 ^ p.fftDepth, ‖A.invStages p.fftDepth p.fftDepth xs q -
      (((2 : ℝ) ^ p.fftDepth : ℝ) : ℂ) * FFTStages.complexify wR q‖ ≤ E1 := by
    intro q hq
    have e := congrFun hex q
    calc _ = ‖(A.invStages p.fftDepth p.fftDepth xs q -
            FFTStages.invStages p.fftDepth p.fftDepth xs q) +
          (FFTStages.invStages p.fftDepth p.fftDepth xs q -
            FFTStages.invStages p.fftDepth p.fftDepth z q)‖ := by
          rw [e]; congr 1; ring
      _ ≤ _ := norm_add_le _ _
      _ ≤ E1 := by rw [hE1]; exact add_le_add (hinv q hq) (hsub q hq)
  have hk : (0 : ℝ) < 2 ^ p.fftDepth := by positivity
  apply Poly.ext_get_eq
  intro i
  rw [ifftRound, Poly.get_ofPi, ← hxs, round_eq_iff, Set.mem_Ico]
  have hcoef : |coeffOfSlots p.fftDepth (A.invStages p.fftDepth p.fftDepth xs) i.1 -
      2 ^ p.fftDepth * (w.get i : ℝ)| ≤ E1 := by
    unfold coeffOfSlots
    split_ifs with hi
    · have hW : (FFTStages.complexify wR i.1).re = (w.get i : ℝ) := by
        rw [complexify_re wR i.1 hi, hwR]
        rfl
      calc _ = |(A.invStages p.fftDepth p.fftDepth xs i.1 -
            (((2 : ℝ) ^ p.fftDepth : ℝ) : ℂ) * FFTStages.complexify wR i.1).re| := by
            rw [Complex.sub_re, Complex.re_ofReal_mul, hW]
        _ ≤ _ := Complex.abs_re_le_norm _
        _ ≤ E1 := hy _ hi
    · have hm : i.1 - 2 ^ p.fftDepth < 2 ^ p.fftDepth := by have := i.2; omega
      have hW : (FFTStages.complexify wR (i.1 - 2 ^ p.fftDepth)).im = (w.get i : ℝ) := by
        rw [complexify_im wR _ hm, hwR]
        simp only
        congr 2
        ext
        simp only [Fin.val_cast]
        omega
      calc _ = |(A.invStages p.fftDepth p.fftDepth xs (i.1 - 2 ^ p.fftDepth) -
            (((2 : ℝ) ^ p.fftDepth : ℝ) : ℂ) *
              FFTStages.complexify wR (i.1 - 2 ^ p.fftDepth)).im| := by
            rw [Complex.sub_im, Complex.im_ofReal_mul, hW]
        _ ≤ _ := Complex.abs_im_le_norm _
        _ ≤ E1 := hy _ hm
  obtain ⟨cv, hcv⟩ : ∃ cv,
      cv = coeffOfSlots p.fftDepth (A.invStages p.fftDepth p.fftDepth xs) i.1 := ⟨_, rfl⟩
  rw [← hcv] at hcoef ⊢
  have hdiv : |cv / 2 ^ p.fftDepth - (w.get i : ℝ)| ≤ E1 / 2 ^ p.fftDepth := by
    rw [show cv / 2 ^ p.fftDepth - (w.get i : ℝ) =
      (cv - 2 ^ p.fftDepth * (w.get i : ℝ)) / 2 ^ p.fftDepth by field_simp,
      abs_div, abs_of_pos hk]
    exact div_le_div_of_nonneg_right hcoef hk.le
  have hr := A.rnd_err (cv / 2 ^ p.fftDepth)
  have hE : E1 / 2 ^ p.fftDepth + 1 / 2 ^ 65 < 1 / 2 := by
    have e : E1 / 2 ^ p.fftDepth = ((2 + etaInv) ^ p.fftDepth - 2 ^ p.fftDepth) * B /
        2 ^ p.fftDepth + D + 1 / 2 ^ 64 := by
      rw [hE1]; field_simp; ring
    have hd : ifftDeviation p.fftDepth D V = ((2 + etaInv) ^ p.fftDepth - 2 ^ p.fftDepth) * B /
        2 ^ p.fftDepth + D + 2 / 2 ^ 64 := by
      rw [ifftDeviation, hB]
    have h3 : (1 : ℝ) / 2 ^ 64 + 1 / 2 ^ 65 < 2 / 2 ^ 64 := by norm_num
    linarith
  have hfin : |A.rnd (cv / 2 ^ p.fftDepth) - (w.get i : ℝ)| < 1 / 2 :=
    calc _ ≤ |A.rnd (cv / 2 ^ p.fftDepth) - cv / 2 ^ p.fftDepth| +
          |cv / 2 ^ p.fftDepth - (w.get i : ℝ)| := abs_sub_le _ _ _
      _ < 1 / 2 := by linarith
  rw [abs_lt] at hfin
  constructor <;> linarith [hfin.1, hfin.2]

end Arith64

end Falcon.FixedPoint

end
