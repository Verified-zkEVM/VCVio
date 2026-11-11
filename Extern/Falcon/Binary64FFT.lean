/-
Copyright (c) 2026 XC0R. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XC0R
-/

module
import all LatticeCrypto.Falcon.Concrete.FloatLike
import all Extern.Falcon.FPR.Decode
import all LatticeCrypto.Falcon.FFTStages
public import Extern.Falcon.Binary64Table
public import Mathlib.Data.Int.Log

/-!
# Error of the binary64 `fpolyFFT` and `fpolyIFFT`

The stage form of the loops (`Extern.Falcon.FFTLoops`), the butterfly bounds
(`Extern.Falcon.Binary64Ops`) and the table bounds (`Extern.Falcon.Binary64Table`) feed the stage
error recursion `Falcon.FFTStages.stages_error`:

- `fwdStagesF_error`: for inputs bounded by `A` whose nonzero entries are at least `2^(-79)`, the
  `k ≤ 8` forward stages of `fpolyFFT` in binary64 end within `((2 + ηF)^k - 2^k) · A` of the exact
  stages, `ηF = 2^(-48) + 18 · 2^(-52)`;
- `invStagesF_error`: the same for the inverse stages of `fpolyIFFT`, with
  `ηI = 2 · 2^(-48) + 38 · 2^(-52)`.

The lower bound `2^(-79)` on the inputs is what keeps every exact intermediate of the eight stages
out of the subnormal range excluded by `#514`'s bounds. This argument's lower bound loses a factor
`2^(-118)` per stage and does not close at nine stages (Falcon-1024); that limit is a property of
the argument, not of binary64.

On coefficient vectors:

- `fpolyFFT_int_error`: `fpolyFFT` on integers of magnitude at most `127`, read by
  `fpolySetSmall`, is within `((2 + ηF)^(logn - 1) - 2^(logn - 1)) · 254` of the exact stages;
- `fpolyIFFT_round`: if a real input is within `D` of the packed FFT of an integer vector whose
  slots are bounded by `V`, and the explicit bound `ifftDeviation` is below `1/2`, then rounding the
  output of `fpolyIFFT` on the binary64 reading of the input returns the integer vector.

`encode` is that reading: zero below `2^(-64)` in magnitude, else the value with its significand
truncated to 53 bits (`encode_spec`). It is how a real input reaches `fpolyIFFT` in
`Extern.Falcon.Binary64Coset`; the reference computes that input in binary64 instead.
-/

public section

namespace Falcon.Concrete.Binary64

open Falcon.Concrete.FPRBridge Falcon.Concrete.FPR Falcon.FFTStages Falcon.Concrete.FFTOps Complex

/-! ## Constants -/

/-- The stage error factor of the binary64 forward butterflies. -/
@[expose] noncomputable def etaF : ℝ := 2 ^ (-(48 : ℤ)) + 18 * u

/-- The stage error factor of the binary64 inverse butterflies. -/
@[expose] noncomputable def etaI : ℝ := 2 * 2 ^ (-(48 : ℤ)) + 38 * u

/-- `ηF` is nonnegative. -/
theorem etaF_nonneg : 0 ≤ etaF := by unfold etaF; have := u_pos; positivity

/-- `ηF` is at most `1`. -/
theorem etaF_le_one : etaF ≤ 1 := by
  unfold etaF; rw [u_eq]; norm_num

private theorem etaI_nonneg : 0 ≤ etaI := by unfold etaI; have := u_pos; positivity

/-- The lower bound on nonzero values after `s` binary64 stages from `m0`. -/
@[expose] noncomputable def lowAt (m0 : ℝ) (s : ℕ) : ℝ := ((2 : ℝ) ^ (-(118 : ℤ))) ^ s * m0

private theorem nextLow_lowAt (m0 : ℝ) (s : ℕ) :
    nextLow (lowAt m0 s) (2 ^ (-(9 : ℤ))) = lowAt m0 (s + 1) := by
  unfold nextLow lowAt
  rw [pow_succ]
  have : (2 : ℝ) ^ (-(118 : ℤ)) = 2 ^ (-(54 : ℤ)) * 2 ^ (-(54 : ℤ)) * 2 ^ (-(9 : ℤ)) / 2 := by
    norm_num
  rw [this]; ring

private theorem lowAt_nonneg {m0 : ℝ} (h : 0 ≤ m0) (s : ℕ) : 0 ≤ lowAt m0 s := by
  unfold lowAt; positivity

private theorem low_ok {m0 : ℝ} (hm0 : (2 : ℝ) ^ (-(79 : ℤ)) ≤ m0) {s : ℕ} (hs : s ≤ 7) :
    (2 : ℝ) ^ (-(1022 : ℤ)) ≤
      2 ^ (-(53 : ℤ)) * (2 ^ (-(54 : ℤ)) * (lowAt m0 s * 2 ^ (-(9 : ℤ)) / 2)) := by
  unfold lowAt
  have h1 : ((2 : ℝ) ^ (-(118 : ℤ))) ^ 7 ≤ ((2 : ℝ) ^ (-(118 : ℤ))) ^ s :=
    pow_le_pow_of_le_one (by positivity) (zpow_le_one_of_nonpos₀ (by norm_num) (by norm_num)) hs
  have h2 : (2 : ℝ) ^ (-(1022 : ℤ)) = 2 ^ (-(53 : ℤ)) * (2 ^ (-(54 : ℤ)) *
      (((2 : ℝ) ^ (-(118 : ℤ))) ^ 7 * 2 ^ (-(79 : ℤ)) * 2 ^ (-(9 : ℤ)) / 2)) := by
    rw [← zpow_natCast (2 ^ (-(118 : ℤ)) : ℝ) 7, ← zpow_mul, div_eq_mul_inv,
      ← zpow_neg_one (2 : ℝ)]
    simp only [← zpow_add₀ (two_ne_zero (α := ℝ))]
    norm_num
  rw [h2]
  gcongr

private theorem block_lt {k s q : ℕ} (hs : s < k) (hq : q < 2 ^ k) :
    q / (2 * 2 ^ (k - 1 - s)) < 2 ^ s := by
  rw [Nat.div_lt_iff_lt_mul (by positivity)]
  calc q < 2 ^ k := hq
    _ = 2 ^ s * (2 * 2 ^ (k - 1 - s)) := by rw [← pow_succ', ← pow_add]; congr 1; omega

/-! ## The forward stages -/

/-- **Error of the binary64 forward stages.** -/
theorem fwdStagesF_error (k : ℕ) (hk : k ≤ 8) (X : ℕ → FPR × FPR) (m0 M0 A : ℝ)
    (hm0 : (2 : ℝ) ^ (-(79 : ℤ)) ≤ m0) (hMb : 16 * (8 ^ k * M0) ≤ 2 ^ (1023 : ℤ)) (hA : 0 ≤ A)
    (hX : ∀ q < 2 ^ k, GoodP m0 M0 (X q)) (hXA : ∀ q < 2 ^ k, ‖cplx (X q)‖ ≤ A) :
    ∀ q < 2 ^ k, ‖cplx (fwdStagesF k k X q) - fwdStages k k (fun q => cplx (X q)) q‖ ≤
      ((2 + etaF) ^ k - 2 ^ k) * A := by
  have hm0' : 0 ≤ m0 := le_trans (by positivity) hm0
  have hM0 : 0 ≤ M0 := (abs_nonneg _).trans (hX 0 (by positivity)).1.2.2
  have key := stages_error (2 ^ k) k (fun s q => cplx (fwdStagesF k s X q))
    (fun s => fwdStages k s (fun q => cplx (X q))) (fun s => fwdStage k s)
    (fun s => ∀ q < 2 ^ k, GoodP (lowAt m0 s) (8 ^ s * M0) (fwdStagesF k s X q)) etaF A
    etaF_nonneg hA (fun s hs => fwdStage_sub_le hs) (fun s hs => fwdStage_norm_le hs)
    (fun s => rfl) (fun q _ => rfl) hXA (by simpa [lowAt, fwdStagesF] using hX) ?_
  · intro q hq
    exact (key k le_rfl).2.2 q hq
  intro s hs hP hB
  set H := 2 ^ (k - 1 - s) with hHdef
  have hHpos : 0 < H := by positivity
  have hdvd : 2 * H ∣ 2 ^ k := two_mul_two_pow_dvd hs
  have hsk : s ≤ 7 := by omega
  have hMs : 16 * (8 ^ s * M0) ≤ (2 : ℝ) ^ (1023 : ℤ) := by
    have h8 : (8 : ℝ) ^ s ≤ 8 ^ k := pow_le_pow_right₀ (by norm_num) (by omega)
    exact le_trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h8 hM0) (by norm_num))
      hMb
  -- the butterfly bound at block `c` on slots `a` and `b`
  have bf : ∀ c < 2 ^ s, ∀ a b, a < 2 ^ k → b < 2 ^ k →
      ‖cplx (fwdBFF (gmPair (2 ^ (s + 1) + c)) (fwdStagesF k s X a, fwdStagesF k s X b)).1 -
          (fwdBF (twiddle s c) (cplx (fwdStagesF k s X a), cplx (fwdStagesF k s X b))).1‖ ≤
          etaF * ((2 + etaF) ^ s * A) ∧
      ‖cplx (fwdBFF (gmPair (2 ^ (s + 1) + c)) (fwdStagesF k s X a, fwdStagesF k s X b)).2 -
          (fwdBF (twiddle s c) (cplx (fwdStagesF k s X a), cplx (fwdStagesF k s X b))).2‖ ≤
          etaF * ((2 + etaF) ^ s * A) ∧
      GoodP (lowAt m0 (s + 1)) (8 ^ (s + 1) * M0)
        (fwdBFF (gmPair (2 ^ (s + 1) + c)) (fwdStagesF k s X a, fwdStagesF k s X b)).1 ∧
      GoodP (lowAt m0 (s + 1)) (8 ^ (s + 1) * M0)
        (fwdBFF (gmPair (2 ^ (s + 1) + c)) (fwdStagesF k s X a, fwdStagesF k s X b)).2 := by
    intro c hc a b ha hb
    obtain ⟨hgt, htw⟩ := gmPair_twiddle hsk hc
    obtain ⟨e1, e2, g1, g2⟩ := fwdBFF_error (m := lowAt m0 s) (M := 8 ^ s * M0)
      (ms := 2 ^ (-(9 : ℤ))) (B := (2 + etaF) ^ s * A) (σ := twiddle s c) _ _ _ (hP a ha)
      (hP b hb) hgt (lowAt_nonneg hm0' s) (by positivity)
      (zpow_le_one_of_nonpos₀ (by norm_num) (by norm_num)) (low_ok hm0 hsk) hMs htw (hB a ha)
      (hB b hb)
    rw [nextLow_lowAt, show 8 * (8 ^ s * M0) = 8 ^ (s + 1) * M0 by ring] at g1 g2
    refine ⟨?_, ?_, g1, g2⟩
    · exact e1.trans (le_of_eq (by unfold etaF; ring))
    · exact e2.trans (le_of_eq (by unfold etaF; ring))
  refine ⟨fun q hq => ?_, fun q hq => ?_⟩
  · change GoodP _ _ (bfStage H _ (fwdStagesF k s X) q)
    unfold bfStage
    split_ifs with hr
    · exact (bf _ (block_lt hs hq) q (q + H) hq (add_half_lt hdvd hHpos hq hr)).2.2.1
    · have := (mod_div_sub_half hHpos hr).1
      exact (bf _ (block_lt hs hq) (q - H) q (by omega) hq).2.2.2
  · change ‖cplx (bfStage H _ (fwdStagesF k s X) q) -
      bfStage H (fun c => fwdBF (twiddle s c)) (fun q => cplx (fwdStagesF k s X q)) q‖ ≤ _
    unfold bfStage
    split_ifs with hr
    · exact (bf _ (block_lt hs hq) q (q + H) hq (add_half_lt hdvd hHpos hq hr)).1
    · have := (mod_div_sub_half hHpos hr).1
      exact (bf _ (block_lt hs hq) (q - H) q (by omega) hq).2.1

/-! ## The inverse stages -/

/-- **Error of the binary64 inverse stages.** -/
theorem invStagesF_error (k : ℕ) (hk : k ≤ 8) (X : ℕ → FPR × FPR) (m0 M0 A : ℝ)
    (hm0 : (2 : ℝ) ^ (-(79 : ℤ)) ≤ m0) (hMb : 16 * (8 ^ k * M0) ≤ 2 ^ (1023 : ℤ)) (hA : 0 ≤ A)
    (hX : ∀ q < 2 ^ k, GoodP m0 M0 (X q)) (hXA : ∀ q < 2 ^ k, ‖cplx (X q)‖ ≤ A) :
    (∀ q < 2 ^ k, ‖cplx (invStagesF k k X q) - invStages k k (fun q => cplx (X q)) q‖ ≤
      ((2 + etaI) ^ k - 2 ^ k) * A) ∧
    (∀ q < 2 ^ k, GoodP (lowAt m0 k) (8 ^ k * M0) (invStagesF k k X q)) ∧
    (∀ q < 2 ^ k, ‖cplx (invStagesF k k X q)‖ ≤ (2 + etaI) ^ k * A) := by
  have hm0' : 0 ≤ m0 := le_trans (by positivity) hm0
  have hM0 : 0 ≤ M0 := (abs_nonneg _).trans (hX 0 (by positivity)).1.2.2
  have key := stages_error (2 ^ k) k (fun s q => cplx (invStagesF k s X q))
    (fun s => invStages k s (fun q => cplx (X q))) (fun s => invStage k (k - 1 - s))
    (fun s => ∀ q < 2 ^ k, GoodP (lowAt m0 s) (8 ^ s * M0) (invStagesF k s X q)) etaI A
    etaI_nonneg hA (fun s hs => invStage_sub_le (by omega))
    (fun s hs => invStage_norm_le (by omega))
    (fun s => rfl) (fun q _ => rfl) hXA (by simpa [lowAt, invStagesF] using hX) ?_
  · exact ⟨fun q hq => (key k le_rfl).2.2 q hq, (key k le_rfl).1, (key k le_rfl).2.1⟩
  intro j hj hP hB
  set s := k - 1 - j with hsdef
  have hsk : s ≤ 7 := by omega
  have hHj : 2 ^ (k - 1 - s) = 2 ^ j := by congr 1; omega
  have hHpos : 0 < 2 ^ j := by positivity
  have hdvd : 2 * 2 ^ j ∣ 2 ^ k := by rw [← hHj]; exact two_mul_two_pow_dvd (by omega)
  have hidx : 2 ^ (k - j) = 2 ^ (s + 1) := by congr 1; omega
  have hMs : 16 * (8 ^ j * M0) ≤ (2 : ℝ) ^ (1023 : ℤ) := by
    have h8 : (8 : ℝ) ^ j ≤ 8 ^ k := pow_le_pow_right₀ (by norm_num) (by omega)
    exact le_trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h8 hM0) (by norm_num))
      hMb
  have hblk : ∀ q < 2 ^ k, q / (2 * 2 ^ j) < 2 ^ s := by
    intro q hq; rw [← hHj]; exact block_lt (by omega) hq
  have bf : ∀ c < 2 ^ s, ∀ a b, a < 2 ^ k → b < 2 ^ k →
      ‖cplx (invBFF (gmPair (2 ^ (k - j) + c)) (invStagesF k j X a, invStagesF k j X b)).1 -
          (invBF (twiddle s c) (cplx (invStagesF k j X a), cplx (invStagesF k j X b))).1‖ ≤
          etaI * ((2 + etaI) ^ j * A) ∧
      ‖cplx (invBFF (gmPair (2 ^ (k - j) + c)) (invStagesF k j X a, invStagesF k j X b)).2 -
          (invBF (twiddle s c) (cplx (invStagesF k j X a), cplx (invStagesF k j X b))).2‖ ≤
          etaI * ((2 + etaI) ^ j * A) ∧
      GoodP (lowAt m0 (j + 1)) (8 ^ (j + 1) * M0)
        (invBFF (gmPair (2 ^ (k - j) + c)) (invStagesF k j X a, invStagesF k j X b)).1 ∧
      GoodP (lowAt m0 (j + 1)) (8 ^ (j + 1) * M0)
        (invBFF (gmPair (2 ^ (k - j) + c)) (invStagesF k j X a, invStagesF k j X b)).2 := by
    intro c hc a b ha hb
    rw [hidx]
    obtain ⟨hgt, htw⟩ := gmPair_twiddle hsk hc
    obtain ⟨e1, e2, g1, g2⟩ := invBFF_error (m := lowAt m0 j) (M := 8 ^ j * M0)
      (ms := 2 ^ (-(9 : ℤ))) (B := (2 + etaI) ^ j * A) (σ := twiddle s c) _ _ _ (hP a ha)
      (hP b hb) hgt (lowAt_nonneg hm0' j) (by positivity)
      (zpow_le_one_of_nonpos₀ (by norm_num) (by norm_num)) (low_ok hm0 (by omega)) hMs htw
      (hB a ha) (hB b hb)
    rw [nextLow_lowAt, show 8 * (8 ^ j * M0) = 8 ^ (j + 1) * M0 by ring] at g1 g2
    refine ⟨?_, ?_, g1, g2⟩
    · exact e1.trans (le_of_eq (by unfold etaI; ring))
    · exact e2.trans (le_of_eq (by unfold etaI; ring))
  refine ⟨fun q hq => ?_, fun q hq => ?_⟩
  · change GoodP _ _ (bfStage (2 ^ j) _ (invStagesF k j X) q)
    unfold bfStage
    split_ifs with hr
    · exact (bf _ (hblk q hq) q (q + 2 ^ j) hq (add_half_lt hdvd hHpos hq hr)).2.2.1
    · have := (mod_div_sub_half hHpos hr).1
      exact (bf _ (hblk q hq) (q - 2 ^ j) q (by omega) hq).2.2.2
  · change ‖cplx (bfStage (2 ^ j) _ (invStagesF k j X) q) -
      bfStage (2 ^ (k - 1 - s)) (fun c => invBF (twiddle s c))
        (fun q => cplx (invStagesF k j X q)) q‖ ≤ _
    rw [hHj]
    unfold bfStage
    split_ifs with hr
    · exact (bf _ (hblk q hq) q (q + 2 ^ j) hq (add_half_lt hdvd hHpos hq hr)).1
    · have := (mod_div_sub_half hHpos hr).1
      exact (bf _ (hblk q hq) (q - 2 ^ j) q (by omega) hq).2.1

/-! ## Reading a real number as a binary64 value -/

/-- The binary64 word with sign `s`, biased exponent `e` and mantissa `m`. -/
def ofFields (s : Bool) (e m : ℕ) : FPR :=
  UInt64.ofNat ((if s then 2 ^ 63 else 0) + e * 2 ^ 52 + m)

private theorem decode_ofFields (s : Bool) {e m : ℕ} (he : e < 2048) (hm : m < 2 ^ 52) :
    FPR.decode (ofFields s e m) = ⟨s, e, m⟩ := by
  have hn : (if s then 2 ^ 63 else 0) + e * 2 ^ 52 + m < 2 ^ 64 := by
    split_ifs <;> omega
  unfold FPR.decode ofFields
  rw [UInt64.toNat_ofNat_of_lt' hn]
  congr 1
  · rw [Nat.testBit_eq_decide_div_mod_eq]
    split_ifs with hs <;> simp [hs] <;> omega
  · rw [Nat.shiftRight_eq_div_pow]; split_ifs <;> omega
  · split_ifs <;> omega

/-- A real number read as a binary64 value: `0` below `2^(-64)` in magnitude, otherwise the
value with its significand truncated to 53 bits. -/
noncomputable def encode (x : ℝ) : FPR :=
  if (2 : ℝ) ^ (-(64 : ℤ)) ≤ |x| then
    ofFields (decide (x < 0)) (Int.log 2 |x| + 1023).toNat
      ⌊(|x| / (2 : ℝ) ^ Int.log 2 |x| - 1) * 2 ^ 52⌋₊
  else FPR.zero

/-- **The binary64 reading of a real number.** Below `2^1023` in magnitude, `encode x` is a
valid operand, is zero or at least `2^(-64)` in magnitude, is at most `|x|`, and differs from `x`
by at most `2^(-52) · |x| + 2^(-64)`. -/
theorem encode_spec {x : ℝ} (hx : |x| < 2 ^ (1023 : ℤ)) :
    FPR.IsNormalOrZero (encode x) ∧
      (toReal (encode x) = 0 ∨ 2 ^ (-(64 : ℤ)) ≤ |toReal (encode x)|) ∧
      |toReal (encode x)| ≤ |x| ∧ |toReal (encode x) - x| ≤ u * |x| + 2 ^ (-(64 : ℤ)) := by
  unfold encode
  split_ifs with hbig
  · have hpos : 0 < |x| := lt_of_lt_of_le (by positivity) hbig
    set e := Int.log 2 |x| with he
    have h2 : (1 : ℕ) < 2 := by norm_num
    have hlo : (2 : ℝ) ^ e ≤ |x| := by
      have := Int.zpow_log_le_self h2 hpos; simpa using this
    have hhi : |x| < (2 : ℝ) ^ (e + 1) := by
      have := Int.lt_zpow_succ_log_self h2 |x|; simpa using this
    have he1 : -64 ≤ e := by
      exact (Int.zpow_le_iff_le_log (x := -64) h2 hpos).mp (by rw [Nat.cast_ofNat]; exact hbig)
    have he2 : e ≤ 1022 := by
      by_contra hc
      have : (2 : ℝ) ^ (1023 : ℤ) ≤ 2 ^ e := zpow_le_zpow_right₀ (by norm_num) (by omega)
      linarith
    set t := |x| / (2 : ℝ) ^ e with ht
    have hpe : (0 : ℝ) < 2 ^ e := by positivity
    have ht1 : 1 ≤ t := by rw [ht, le_div_iff₀ hpe]; linarith
    have ht2 : t < 2 := by
      rw [ht, div_lt_iff₀ hpe]
      calc |x| < 2 ^ (e + 1) := hhi
        _ = 2 * 2 ^ e := by rw [zpow_add_one₀ (by norm_num)]; ring
    set m := ⌊(t - 1) * 2 ^ 52⌋₊ with hm
    have hm0 : (0 : ℝ) ≤ (t - 1) * 2 ^ 52 := by nlinarith
    have hm1 : (m : ℝ) ≤ (t - 1) * 2 ^ 52 := Nat.floor_le hm0
    have hm2 : (t - 1) * 2 ^ 52 < m + 1 := Nat.lt_floor_add_one _
    have hmlt : m < 2 ^ 52 := by
      have : (m : ℝ) < 2 ^ 52 := by nlinarith
      exact_mod_cast this
    have hE : (e + 1023).toNat < 2048 := by omega
    have hdec := decode_ofFields (decide (x < 0)) hE hmlt
    set E := (e + 1023).toNat with hEdef
    have hE0 : E ≠ 0 := by omega
    have hE1 : E ≠ 2047 := by omega
    have hval : toReal (ofFields (decide (x < 0)) E m) =
        (if x < 0 then -1 else 1) * ((1 + (m : ℝ) / 2 ^ 52) * 2 ^ e) := by
      change (FPR.decode _).toReal = _
      rw [hdec]
      unfold FPR.Bits.toReal
      simp only [hE0, hE1, ite_false, decide_eq_true_eq]
      have : ((E : ℤ) - 1023) = e := by omega
      rw [this]; ring
    have hv1 : (1 + (m : ℝ) / 2 ^ 52) * 2 ^ e ≤ |x| := by
      have : (1 + (m : ℝ) / 2 ^ 52) ≤ t := by
        have : (m : ℝ) / 2 ^ 52 ≤ t - 1 := by rw [div_le_iff₀ (by positivity)]; linarith
        linarith
      calc (1 + (m : ℝ) / 2 ^ 52) * 2 ^ e ≤ t * 2 ^ e := by gcongr
        _ = |x| := by rw [ht]; field_simp
    have hv2 : |x| - (1 + (m : ℝ) / 2 ^ 52) * 2 ^ e ≤ u * |x| := by
      have h1 : t - (1 + (m : ℝ) / 2 ^ 52) ≤ 2 ^ (-(52 : ℤ)) := by
        have : t - 1 - (m : ℝ) / 2 ^ 52 < 1 / 2 ^ 52 := by
          rw [sub_lt_iff_lt_add, ← add_div, lt_div_iff₀ (by positivity)]; linarith
        have h52 : (1 : ℝ) / 2 ^ 52 = 2 ^ (-(52 : ℤ)) := by norm_num
        linarith
      have h2 : |x| - (1 + (m : ℝ) / 2 ^ 52) * 2 ^ e = (t - (1 + (m : ℝ) / 2 ^ 52)) * 2 ^ e := by
        rw [ht]; field_simp
      rw [h2, u_eq]
      calc (t - (1 + (m : ℝ) / 2 ^ 52)) * 2 ^ e ≤ 2 ^ (-(52 : ℤ)) * 2 ^ e := by gcongr
        _ ≤ 2 ^ (-(52 : ℤ)) * |x| := by gcongr
    have hv0 : 2 ^ e ≤ (1 + (m : ℝ) / 2 ^ 52) * 2 ^ e := by
      have : (0 : ℝ) ≤ (m : ℝ) / 2 ^ 52 := by positivity
      nlinarith
    have hsgn : |(if x < 0 then (-1 : ℝ) else 1)| = 1 := by split_ifs <;> simp
    have habs : |toReal (ofFields (decide (x < 0)) E m)| = (1 + (m : ℝ) / 2 ^ 52) * 2 ^ e := by
      rw [hval, abs_mul, hsgn, one_mul, abs_of_pos (by positivity)]
    refine ⟨Or.inl (by unfold FPR.IsNormal FPR.Bits.IsNormal; rw [hdec]; exact ⟨hE0, hE1⟩),
      Or.inr ?_, ?_, ?_⟩
    · rw [habs]
      calc (2 : ℝ) ^ (-(64 : ℤ)) ≤ 2 ^ e := zpow_le_zpow_right₀ (by norm_num) he1
        _ ≤ _ := hv0
    · rw [habs]; exact hv1
    · have hu := u_pos
      rw [hval]
      by_cases hneg : x < 0
      · simp only [hneg, ite_true]
        rw [abs_of_neg hneg] at hv1 hv2 ⊢
        rw [abs_le]; constructor <;> nlinarith
      · simp only [hneg, ite_false]
        rw [not_lt] at hneg
        rw [abs_of_nonneg hneg] at hv1 hv2 ⊢
        rw [abs_le]; constructor <;> nlinarith
  · rw [not_le] at hbig
    have hz : toReal FPR.zero = 0 := toReal_zero
    refine ⟨FPR.isNormalOrZero_zero, Or.inl hz, by rw [hz]; simp, ?_⟩
    rw [hz, zero_sub, abs_neg]
    have := u_pos
    nlinarith [abs_nonneg x]

/-! ## The transforms on coefficient vectors -/

private theorem good_ofInt {v : ℤ} (hv : |v| ≤ 127) :
    Good 1 127 (FloatLike.ofInt32 (Int32.ofInt v) : FPR) := by
  obtain ⟨h1, h2⟩ := ofInt32_exact hv
  refine ⟨h2, ?_, ?_⟩
  · rw [h1]
    by_cases h : v = 0
    · left; simp [h]
    · right; exact_mod_cast Int.one_le_abs h
  · rw [h1]; exact_mod_cast hv

private theorem eight_pow_bound {k : ℕ} (hk : k ≤ 8) {M : ℝ} (hM : 0 ≤ M) (hMb : M ≤ 2 ^ 200) :
    16 * (8 ^ k * M) ≤ (2 : ℝ) ^ (1023 : ℤ) := by
  have h8 : (8 : ℝ) ^ k ≤ 8 ^ 8 := pow_le_pow_right₀ (by norm_num) hk
  calc 16 * (8 ^ k * M) ≤ 16 * (8 ^ 8 * 2 ^ 200) := by gcongr
    _ = (2 : ℝ) ^ (4 + (24 + 200)) := by
        rw [pow_add, pow_add, show (2 : ℝ) ^ 4 = 16 by norm_num,
          show (2 : ℝ) ^ 24 = 8 ^ 8 by norm_num]
    _ ≤ (2 : ℝ) ^ 1023 := pow_le_pow_right₀ (by norm_num) (by norm_num)
    _ = (2 : ℝ) ^ (1023 : ℤ) := (zpow_natCast 2 1023).symm

/-- **The binary64 FFT of a small integer polynomial.** For `2 ≤ logn ≤ 9` and coefficients of
magnitude at most `127`, slot `q` of `fpolyFFT` on the `fpolySetSmall` conversion is within
`((2 + ηF)^(logn - 1) - 2^(logn - 1)) · 254` of the exact stages on the complex slots. -/
theorem fpolyFFT_int_error (logn : ℕ) (h2 : 2 ≤ logn) (h9 : logn ≤ 9) (f : ℕ → ℤ)
    (hf : ∀ i < 2 ^ logn, |f i| ≤ 127) (ints : Array Int32)
    (hints : ∀ i < 2 ^ logn, ints.getD i 0 = Int32.ofInt (f i)) :
    ∀ q < 2 ^ (logn - 1),
      ‖cplx (cv (2 ^ (logn - 1)) (fpolyFFT logn (fpolySetSmall logn ints)) q) -
        fwdStages (logn - 1) (logn - 1)
          (fun r => (f r : ℂ) + I * (f (r + 2 ^ (logn - 1)) : ℂ)) q‖ ≤
      ((2 + etaF) ^ (logn - 1) - 2 ^ (logn - 1)) * 254 := by
  set k := logn - 1 with hk
  have hn : 2 ^ logn = 2 * 2 ^ k := by rw [← pow_succ']; congr 1; omega
  set a := fpolySetSmall (F := FPR) logn ints with hadef
  have ha : a.size = 2 * 2 ^ k := by rw [hadef, size_fpolySetSmall, hn]
  have hX : ∀ q < 2 ^ k, cv (2 ^ k) a q = (FloatLike.ofInt32 (Int32.ofInt (f q)),
      FloatLike.ofInt32 (Int32.ofInt (f (q + 2 ^ k)))) := by
    intro q hq
    simp only [cv, hadef]
    rw [getElem!_fpolySetSmall _ _ _ (by omega), getElem!_fpolySetSmall _ _ _ (by omega),
      hints _ (by omega), hints _ (by omega)]
  have hval : ∀ q < 2 ^ k, cplx (cv (2 ^ k) a q) = (f q : ℂ) + I * (f (q + 2 ^ k) : ℂ) := by
    intro q hq
    rw [hX q hq]
    apply Complex.ext <;>
      simp [cplx, (ofInt32_exact (hf q (by omega))).1,
        (ofInt32_exact (hf (q + 2 ^ k) (by omega))).1]
  have hgood : ∀ q < 2 ^ k, GoodP 1 127 (cv (2 ^ k) a q) := by
    intro q hq
    rw [hX q hq]
    exact ⟨good_ofInt (hf q (by omega)), good_ofInt (hf _ (by omega))⟩
  have hA : ∀ q < 2 ^ k, ‖cplx (cv (2 ^ k) a q)‖ ≤ 254 := by
    intro q hq
    rw [hval q hq]
    calc ‖(f q : ℂ) + I * (f (q + 2 ^ k) : ℂ)‖ ≤ ‖(f q : ℂ)‖ + ‖I * (f (q + 2 ^ k) : ℂ)‖ :=
          norm_add_le _ _
      _ ≤ 127 + 127 := by
          rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_intCast, Complex.norm_intCast]
          gcongr
          · exact_mod_cast hf q (by omega)
          · exact_mod_cast hf _ (by omega)
      _ = 254 := by norm_num
  intro q hq
  rw [cv_fpolyFFT logn h2 a ha q hq,
    fwdStages_congr k k le_rfl _ (fun q => cplx (cv (2 ^ k) a q))
      (fun q hq => (hval q hq).symm) q hq]
  exact fwdStagesF_error k (by omega) (cv (2 ^ k) a) 1 127 254 (by norm_num)
    (eight_pow_bound (by omega) (by norm_num)
      (le_trans (by norm_num : (127 : ℝ) ≤ 2 ^ 7) (pow_le_pow_right₀ (by norm_num) (by norm_num))))
    (by norm_num) hgood hA q hq

/-- The deviation bound of the binary64 inverse transform: inputs within `D` of the packed FFT of
an integer vector whose slots are bounded by `V`. -/
@[expose] noncomputable def ifftDeviation (k : ℕ) (D V : ℝ) : ℝ :=
  ((2 : ℝ) ^ k)⁻¹ * (((2 + etaI) ^ k - 2 ^ k) * (V + D) +
      2 ^ k * (2 * (u * (V + D) + 2 ^ (-(64 : ℤ))) + D)) +
    u * (V + ((2 : ℝ) ^ k)⁻¹ * (((2 + etaI) ^ k - 2 ^ k) * (V + D) +
      2 ^ k * (2 * (u * (V + D) + 2 ^ (-(64 : ℤ))) + D)))

private theorem norm_le_of_abs_le {z z' : ℂ} (hre : |z'.re| ≤ |z.re|) (him : |z'.im| ≤ |z.im|) :
    ‖z'‖ ≤ ‖z‖ := by
  rw [Complex.norm_eq_sqrt_sq_add_sq, Complex.norm_eq_sqrt_sq_add_sq]
  exact Real.sqrt_le_sqrt (add_le_add (sq_le_sq.mpr hre) (sq_le_sq.mpr him))

private theorem round_eq_of_abs_lt {x : ℝ} {n : ℤ} (h : |x - n| < 1 / 2) : round x = n := by
  rw [round_eq, Int.floor_eq_iff]
  rw [abs_lt] at h
  constructor <;> linarith

private theorem final_dev {k : ℕ} {o y wv E1 W : ℝ} (hy : |y - 2 ^ k * wv| ≤ E1) (hwv : |wv| ≤ W)
    (hout : |o - y * ((2 : ℝ) ^ k)⁻¹| ≤ u * |y * ((2 : ℝ) ^ k)⁻¹|) :
    |o - wv| ≤ ((2 : ℝ) ^ k)⁻¹ * E1 + u * (W + ((2 : ℝ) ^ k)⁻¹ * E1) := by
  have hp : (0 : ℝ) < (2 ^ k)⁻¹ := by positivity
  have hpk : ((2 : ℝ) ^ k)⁻¹ * 2 ^ k = 1 := inv_mul_cancel₀ (by positivity)
  have hE : |y * ((2 : ℝ) ^ k)⁻¹ - wv| ≤ ((2 : ℝ) ^ k)⁻¹ * E1 := by
    have : y * ((2 : ℝ) ^ k)⁻¹ - wv = ((2 : ℝ) ^ k)⁻¹ * (y - 2 ^ k * wv) := by
      rw [mul_sub, ← mul_assoc, hpk, one_mul, mul_comm]
    rw [this, abs_mul, abs_of_pos hp]
    exact mul_le_mul_of_nonneg_left hy hp.le
  have hY : |y * ((2 : ℝ) ^ k)⁻¹| ≤ W + ((2 : ℝ) ^ k)⁻¹ * E1 := by
    calc |y * ((2 : ℝ) ^ k)⁻¹| = |(y * ((2 : ℝ) ^ k)⁻¹ - wv) + wv| := by rw [sub_add_cancel]
      _ ≤ |y * ((2 : ℝ) ^ k)⁻¹ - wv| + |wv| := abs_add_le _ _
      _ ≤ ((2 : ℝ) ^ k)⁻¹ * E1 + W := add_le_add hE hwv
      _ = W + ((2 : ℝ) ^ k)⁻¹ * E1 := by ring
  calc |o - wv| = |(o - y * ((2 : ℝ) ^ k)⁻¹) + (y * ((2 : ℝ) ^ k)⁻¹ - wv)| := by
        rw [sub_add_sub_cancel]
    _ ≤ |o - y * ((2 : ℝ) ^ k)⁻¹| + |y * ((2 : ℝ) ^ k)⁻¹ - wv| := abs_add_le _ _
    _ ≤ u * (W + ((2 : ℝ) ^ k)⁻¹ * E1) + ((2 : ℝ) ^ k)⁻¹ * E1 :=
        add_le_add (hout.trans (mul_le_mul_of_nonneg_left hY u_pos.le)) hE
    _ = _ := by ring

private theorem low_scale_ok {k : ℕ} (hk : k ≤ 8) :
    (2 : ℝ) ^ (-(1022 : ℤ)) ≤ lowAt (2 ^ (-(64 : ℤ))) k * 2 ^ (1 - ((k + 1 : ℕ) : ℤ)) := by
  unfold lowAt
  have h1 : ((2 : ℝ) ^ (-(118 : ℤ))) ^ 8 ≤ ((2 : ℝ) ^ (-(118 : ℤ))) ^ k :=
    pow_le_pow_of_le_one (by positivity) (zpow_le_one_of_nonpos₀ (by norm_num) (by norm_num)) hk
  have h2 : (2 : ℝ) ^ (-(8 : ℤ)) ≤ 2 ^ (1 - ((k + 1 : ℕ) : ℤ)) :=
    zpow_le_zpow_right₀ (by norm_num) (by push_cast; omega)
  calc (2 : ℝ) ^ (-(1022 : ℤ)) ≤
        ((2 : ℝ) ^ (-(118 : ℤ))) ^ 8 * 2 ^ (-(64 : ℤ)) * 2 ^ (-(8 : ℤ)) := by
        rw [← zpow_natCast (2 ^ (-(118 : ℤ)) : ℝ) 8, ← zpow_mul, ← zpow_add₀ (by norm_num),
          ← zpow_add₀ (by norm_num)]
        exact zpow_le_zpow_right₀ (by norm_num) (by norm_num)
    _ ≤ _ := by gcongr

/-- A deviation bound below `1/2` forces `2 · (V + D) ≤ 2^200`, far inside the binary64 range. -/
private theorem ifftDeviation_big {k : ℕ} {D V : ℝ} (hD0 : 0 ≤ D) (hV0 : 0 ≤ V)
    (hdev : ifftDeviation k D V < 1 / 2) : 2 * (V + D) ≤ 2 ^ 200 := by
  have hk : (0 : ℝ) < 2 ^ k := by positivity
  have hS : (0 : ℝ) ≤ V + D := by positivity
  have hη : (2 : ℝ) ^ k ≤ (2 + etaI) ^ k :=
    pow_le_pow_left₀ (by norm_num) (by linarith [etaI_nonneg]) k
  have hu := u_pos
  set E1 := ((2 + etaI) ^ k - 2 ^ k) * (V + D) +
    2 ^ k * (2 * (u * (V + D) + 2 ^ (-(64 : ℤ))) + D) with hE1
  have hE : 2 ^ k * (2 * (u * (V + D))) ≤ E1 := by
    have : 0 ≤ ((2 + etaI) ^ k - 2 ^ k) * (V + D) := mul_nonneg (by linarith) hS
    have : (0 : ℝ) ≤ 2 ^ (-(64 : ℤ)) := by positivity
    rw [hE1]; nlinarith
  have hE0 : 0 ≤ ((2 : ℝ) ^ k)⁻¹ * E1 := by
    have : 0 ≤ 2 ^ k * (2 * (u * (V + D))) := by positivity
    positivity
  have hlow : 2 * (u * (V + D)) ≤ ((2 : ℝ) ^ k)⁻¹ * E1 := by
    rw [le_inv_mul_iff₀ hk]; exact hE
  have hdev' : ((2 : ℝ) ^ k)⁻¹ * E1 + u * (V + ((2 : ℝ) ^ k)⁻¹ * E1) < 1 / 2 := by
    rw [ifftDeviation] at hdev; exact hdev
  have : 0 ≤ u * (V + ((2 : ℝ) ^ k)⁻¹ * E1) := by positivity
  have hsmall : 2 * (u * (V + D)) < 1 / 2 := by linarith
  rw [u_eq] at hsmall
  have h52 : (2 : ℝ) ^ (-(52 : ℤ)) = 1 / 2 ^ 52 := by norm_num
  rw [h52] at hsmall
  have : V + D < 2 ^ 50 := by
    have h : 2 * (1 / (2 : ℝ) ^ 52 * (V + D)) = (V + D) / 2 ^ 51 := by ring
    rw [h, div_lt_iff₀ (by positivity)] at hsmall
    linarith
  have : (2 : ℝ) ^ 51 ≤ 2 ^ 200 := pow_le_pow_right₀ (by norm_num) (by norm_num)
  linarith

/-- **The binary64 inverse transform recovers an integer vector.** If the input `v` is within `D`
of the packed FFT of an integer vector `w`, slot by slot, the slots of that packed FFT are bounded
by `V`, and the deviation bound `ifftDeviation k D V` is below `1/2`, then rounding the output of
`fpolyIFFT` on the binary64 reading of `v` returns `w`. -/
theorem fpolyIFFT_round (k : ℕ) (h1 : 1 ≤ k) (h8 : k ≤ 8)
    (v : RealFFTPoly k) (w : Fin (2 * 2 ^ k) → ℤ) (D V : ℝ)
    (hD : ∀ j, ‖RealFFTPoly.coord v j -
      RealFFTPoly.coord (RealFFTPoly.ofCoeffs k fun i => (w i : ℝ)) j‖ ≤ D)
    (hV : ∀ j, ‖RealFFTPoly.coord (RealFFTPoly.ofCoeffs k fun i => (w i : ℝ)) j‖ ≤ V)
    (hdev : ifftDeviation k D V < 1 / 2) (i : Fin (2 * 2 ^ k)) :
    round (toReal ((fpolyIFFT (k + 1)
      (Array.ofFn fun j : Fin (2 * 2 ^ k) => encode (v.get j))).getD i.1 0)) = w i := by
  have h2 : 2 ≤ k + 1 := by omega
  have hD0 : 0 ≤ D := (norm_nonneg _).trans (hD ⟨0, by positivity⟩)
  have hV0 : 0 ≤ V := (norm_nonneg _).trans (hV ⟨0, by positivity⟩)
  have hbig : 2 * (V + D) ≤ 2 ^ 200 := ifftDeviation_big hD0 hV0 hdev
  set arr := Array.ofFn fun j : Fin (2 * 2 ^ k) => encode (v.get j) with harrdef
  have hsize : arr.size = 2 * 2 ^ k := Array.size_ofFn
  have harr : ∀ p (hp : p < 2 * 2 ^ k), arr.getD p FloatLike.zero = encode (v.get ⟨p, hp⟩) := by
    intro p hp; simp [harrdef, hp, Array.getD_eq_getD_getElem?]
  set wR : Fin (2 * 2 ^ k) → ℝ := fun i => (w i : ℝ) with hwR
  set wc := complexify wR with hwc
  have hwcq : ∀ q (hq : q < 2 ^ k),
      wc q = (w ⟨q, by omega⟩ : ℂ) + I * (w ⟨q + 2 ^ k, by omega⟩ : ℂ) := by
    intro q hq
    simp [hwc, complexify, extend, show q < 2 * 2 ^ k by omega,
      show q + 2 ^ k < 2 * 2 ^ k by omega, hwR]
  set what := fwdStages k k wc with hwhat
  have hwhatb : ∀ q < 2 ^ k, ‖what q‖ ≤ V := by
    intro q hq
    have := hV ⟨q, hq⟩
    rwa [coord_ofCoeffs_eq_fwdStages] at this
  -- the integer vector is bounded by `V`
  have hwcV : ∀ q < 2 ^ k, ‖wc q‖ ≤ V := by
    intro q hq
    have h := invStages_norm_le k k le_rfl what V hwhatb q hq
    rw [hwhat, invStages_fwdStages, norm_mul] at h
    have : ‖(2 : ℂ) ^ k‖ = 2 ^ k := by simp
    rw [this] at h
    exact le_of_mul_le_mul_left h (by positivity)
  have hW : ∀ i : Fin (2 * 2 ^ k), |(w i : ℝ)| ≤ V := by
    intro i
    by_cases hi : i.1 < 2 ^ k
    · have := (Complex.abs_re_le_norm _).trans (hwcV i.1 hi)
      rw [hwcq i.1 hi] at this
      simpa using this
    · have hq : i.1 - 2 ^ k < 2 ^ k := by have := i.2; omega
      have := (Complex.abs_im_le_norm _).trans (hwcV _ hq)
      rw [hwcq _ hq] at this
      have hi' : (⟨i.1 - 2 ^ k + 2 ^ k, by omega⟩ : Fin (2 * 2 ^ k)) = i :=
        Fin.ext (show i.1 - 2 ^ k + 2 ^ k = i.1 by omega)
      simpa [hi'] using this
  set Ain := V + D with hAin
  have hAin0 : 0 ≤ Ain := by positivity
  have hcv : ∀ q (hq : q < 2 ^ k), ‖RealFFTPoly.coord v ⟨q, hq⟩ - what q‖ ≤ D := by
    intro q hq
    have := hD ⟨q, hq⟩
    rwa [coord_ofCoeffs_eq_fwdStages] at this
  have hvb : ∀ q (hq : q < 2 ^ k), ‖RealFFTPoly.coord v ⟨q, hq⟩‖ ≤ Ain := by
    intro q hq
    calc _ = ‖(RealFFTPoly.coord v ⟨q, hq⟩ - what q) + what q‖ := by rw [sub_add_cancel]
      _ ≤ _ := norm_add_le _ _
      _ ≤ D + V := add_le_add (hcv q hq) (hwhatb q hq)
      _ = Ain := by rw [hAin]; ring
  have hbig' : 2 * Ain ≤ 2 ^ 200 := hbig
  have hAbig : Ain < (2 : ℝ) ^ (1023 : ℤ) := by
    calc Ain ≤ 2 ^ 200 := by linarith
      _ < (2 : ℝ) ^ 1023 := pow_lt_pow_right₀ (by norm_num) (by norm_num)
      _ = (2 : ℝ) ^ (1023 : ℤ) := (zpow_natCast 2 1023).symm
  -- the binary64 reading of the slots
  have hXq : ∀ q (hq : q < 2 ^ k), cv (2 ^ k) arr q =
      (encode (RealFFTPoly.re v ⟨q, hq⟩), encode (RealFFTPoly.im v ⟨q, hq⟩)) := by
    intro q hq
    rw [cv_eq_getD _ _ _ (by omega), harr q (by omega), harr (q + 2 ^ k) (by omega)]
    rfl
  have hcomp : ∀ q (hq : q < 2 ^ k),
      |RealFFTPoly.re v ⟨q, hq⟩| ≤ Ain ∧ |RealFFTPoly.im v ⟨q, hq⟩| ≤ Ain := by
    intro q hq
    have h := hvb q hq
    exact ⟨(show |RealFFTPoly.re v ⟨q, hq⟩| ≤ ‖RealFFTPoly.coord v ⟨q, hq⟩‖ by
        simpa using Complex.abs_re_le_norm (RealFFTPoly.coord v ⟨q, hq⟩)).trans h,
      (show |RealFFTPoly.im v ⟨q, hq⟩| ≤ ‖RealFFTPoly.coord v ⟨q, hq⟩‖ by
        simpa using Complex.abs_im_le_norm (RealFFTPoly.coord v ⟨q, hq⟩)).trans h⟩
  have henc : ∀ x : ℝ, |x| ≤ Ain → Good (2 ^ (-(64 : ℤ))) Ain (encode x) ∧
      |toReal (encode x)| ≤ |x| ∧ |toReal (encode x) - x| ≤ u * Ain + 2 ^ (-(64 : ℤ)) := by
    intro x hx
    obtain ⟨e1, e2, e3, e4⟩ := encode_spec (hx.trans_lt hAbig)
    refine ⟨⟨e1, e2, e3.trans hx⟩, e3, e4.trans ?_⟩
    gcongr
    exact u_pos.le
  have hgood : ∀ q < 2 ^ k, GoodP (2 ^ (-(64 : ℤ))) Ain (cv (2 ^ k) arr q) := by
    intro q hq
    rw [hXq q hq]
    exact ⟨(henc _ (hcomp q hq).1).1, (henc _ (hcomp q hq).2).1⟩
  have hXb : ∀ q < 2 ^ k, ‖cplx (cv (2 ^ k) arr q)‖ ≤ Ain := by
    intro q hq
    rw [hXq q hq]
    refine le_trans (norm_le_of_abs_le (z := RealFFTPoly.coord v ⟨q, hq⟩) ?_ ?_) (hvb q hq)
    · simpa using (henc _ (hcomp q hq).1).2.1
    · simpa using (henc _ (hcomp q hq).2).2.1
  have hXw : ∀ q < 2 ^ k, ‖cplx (cv (2 ^ k) arr q) - what q‖ ≤
      2 * (u * Ain + 2 ^ (-(64 : ℤ))) + D := by
    intro q hq
    have h1 : ‖cplx (cv (2 ^ k) arr q) - RealFFTPoly.coord v ⟨q, hq⟩‖ ≤
        2 * (u * Ain + 2 ^ (-(64 : ℤ))) := by
      rw [hXq q hq]
      apply norm_le_of_parts
      · simpa using (henc _ (hcomp q hq).1).2.2
      · simpa using (henc _ (hcomp q hq).2).2.2
    calc _ = ‖(cplx (cv (2 ^ k) arr q) - RealFFTPoly.coord v ⟨q, hq⟩) +
          (RealFFTPoly.coord v ⟨q, hq⟩ - what q)‖ := by rw [sub_add_sub_cancel]
      _ ≤ _ := norm_add_le _ _
      _ ≤ _ := add_le_add h1 (hcv q hq)
  -- the inverse stages
  have hbig'' : Ain ≤ 2 ^ 200 := by linarith
  obtain ⟨hE, hGY, -⟩ := invStagesF_error k h8 (cv (2 ^ k) arr) (2 ^ (-(64 : ℤ))) Ain
    Ain (zpow_le_zpow_right₀ (by norm_num) (by norm_num))
    (eight_pow_bound h8 (by positivity) hbig'') (by positivity) hgood hXb
  have hsub := invStages_sub_le k k le_rfl _ _ _ hXw
  rw [hwhat, invStages_fwdStages] at hsub
  set E1 := ((2 + etaI) ^ k - 2 ^ k) * Ain +
    2 ^ k * (2 * (u * Ain + 2 ^ (-(64 : ℤ))) + D) with hE1
  set Y := invStagesF k k (cv (2 ^ k) arr) with hY
  have hYw : ∀ q < 2 ^ k, ‖cplx (Y q) - 2 ^ k * wc q‖ ≤ E1 := by
    intro q hq
    calc _ = ‖(cplx (Y q) - invStages k k (fun q => cplx (cv (2 ^ k) arr q)) q) +
          (invStages k k (fun q => cplx (cv (2 ^ k) arr q)) q - 2 ^ k * wc q)‖ := by
          rw [sub_add_sub_cancel]
      _ ≤ _ := norm_add_le _ _
      _ ≤ _ := add_le_add (hE q hq) (hsub q hq)
  -- the final scale
  obtain ⟨hsc, hscv⟩ := toReal_ifftScale h2 (by omega)
  set sc : FPR := FloatLike.scaled 4503599627370496 (0 - 51 - (k + 1).toUInt32.toInt32)
    with hscdef
  have hsck : toReal sc = ((2 : ℝ) ^ k)⁻¹ := by
    rw [hsc, show (1 - ((k + 1 : ℕ) : ℤ)) = -(k : ℤ) by push_cast; ring, zpow_neg, zpow_natCast]
  have hgsc : Good (2 ^ (1 - ((k + 1 : ℕ) : ℤ))) (2 ^ (1 - ((k + 1 : ℕ) : ℤ))) sc :=
    ⟨hscv, Or.inr (by rw [hsc, abs_of_pos (by positivity)]),
      by rw [hsc, abs_of_pos (by positivity)]⟩
  have hMsc : 8 ^ k * Ain * 2 ^ (1 - ((k + 1 : ℕ) : ℤ)) ≤ (2 : ℝ) ^ (1023 : ℤ) := by
    have hle : (2 : ℝ) ^ (1 - ((k + 1 : ℕ) : ℤ)) ≤ 1 :=
      zpow_le_one_of_nonpos₀ (by norm_num) (by push_cast; omega)
    have h0 : (0 : ℝ) ≤ 8 ^ k * Ain := by positivity
    calc 8 ^ k * Ain * 2 ^ (1 - ((k + 1 : ℕ) : ℤ)) ≤ 8 ^ k * Ain * 1 :=
          mul_le_mul_of_nonneg_left hle h0
      _ ≤ 16 * (8 ^ k * Ain) := by linarith
      _ ≤ _ := eight_pow_bound h8 (by positivity) hbig''
  have hout : ∀ y : FPR, Good (lowAt (2 ^ (-(64 : ℤ))) k) (8 ^ k * Ain) y →
      |toReal (FPR.mul y sc) - toReal y * ((2 : ℝ) ^ k)⁻¹| ≤
        u * |toReal y * ((2 : ℝ) ^ k)⁻¹| := by
    intro y hy
    have := (good_mul hy hgsc (lowAt_nonneg (by positivity) k) (by positivity)
      (low_scale_ok h8) hMsc).1
    rwa [hsck] at this
  have hcvout : ∀ q (hq : q < 2 ^ k), cv (2 ^ k) (fpolyIFFT (k + 1) arr) q =
      (FPR.mul (Y q).1 sc, FPR.mul (Y q).2 sc) := by
    intro q hq
    exact cv_fpolyIFFT (k + 1) h2 arr hsize q hq
  have hosize : (fpolyIFFT (k + 1) arr).size = 2 * 2 ^ k := size_fpolyIFFT (k + 1) h2 arr hsize
  -- the coefficient
  apply round_eq_of_abs_lt
  refine lt_of_le_of_lt ?_ hdev
  have hmeq : ifftDeviation k D V = ((2 : ℝ) ^ k)⁻¹ * E1 + u * (V + ((2 : ℝ) ^ k)⁻¹ * E1) := by
    rw [ifftDeviation, hE1, hAin]
  rw [hmeq]
  have hW' : ∀ i, |((w i : ℤ) : ℝ)| ≤ V := hW
  have h2k : (2 : ℂ) ^ k = ((2 ^ k : ℝ) : ℂ) := by push_cast; rfl
  by_cases hi : i.1 < 2 ^ k
  · have hci := congrArg Prod.fst (hcvout i.1 hi)
    rw [cv_eq_getD _ _ _ (by omega)] at hci
    have hci' : (fpolyIFFT (k + 1) arr).getD i.1 0 = FPR.mul (Y i.1).1 sc := hci
    rw [hci']
    have hre : |toReal (Y i.1).1 - 2 ^ k * (w i : ℝ)| ≤ E1 := by
      have h := (Complex.abs_re_le_norm _).trans (hYw i.1 hi)
      rw [hwcq i.1 hi, h2k] at h
      have e : (cplx (Y i.1) - ((2 ^ k : ℝ) : ℂ) * ((w ⟨i.1, by omega⟩ : ℂ) +
          I * (w ⟨i.1 + 2 ^ k, by omega⟩ : ℂ))).re = toReal (Y i.1).1 - 2 ^ k * (w i : ℝ) := by
        simp only [Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
          Complex.add_re, Complex.add_im, Complex.intCast_re, Complex.I_re, Complex.I_im,
          Complex.intCast_im, cplx_re, Fin.eta]
        ring
      rwa [e] at h
    exact final_dev hre (hW' i) (hout _ (hGY i.1 hi).1)
  · set q := i.1 - 2 ^ k with hqdef
    have hq : q < 2 ^ k := by have := i.2; omega
    have hci := congrArg Prod.snd (hcvout q hq)
    rw [cv_eq_getD _ _ _ (by omega)] at hci
    have hci' : (fpolyIFFT (k + 1) arr).getD i.1 0 = FPR.mul (Y q).2 sc := by
      rw [show i.1 = q + 2 ^ k by omega]; exact hci
    rw [hci']
    have him : |toReal (Y q).2 - 2 ^ k * (w i : ℝ)| ≤ E1 := by
      have h := (Complex.abs_im_le_norm _).trans (hYw q hq)
      rw [hwcq q hq, h2k] at h
      have hi' : (⟨q + 2 ^ k, by omega⟩ : Fin (2 * 2 ^ k)) = i :=
        Fin.ext (show q + 2 ^ k = i.1 by omega)
      have e : (cplx (Y q) - ((2 ^ k : ℝ) : ℂ) * ((w ⟨q, by omega⟩ : ℂ) +
          I * (w ⟨q + 2 ^ k, by omega⟩ : ℂ))).im = toReal (Y q).2 - 2 ^ k * (w i : ℝ) := by
        simp only [Complex.sub_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
          Complex.add_re, Complex.add_im, Complex.intCast_re, Complex.I_re, Complex.I_im,
          Complex.intCast_im, cplx_im, hi']
        ring
      rwa [e] at h
    exact final_dev him (hW' i) (hout _ (hGY q hq).2)

end Falcon.Concrete.Binary64

end
