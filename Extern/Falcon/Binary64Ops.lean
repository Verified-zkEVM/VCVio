/-
Copyright (c) 2026 XC0R. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XC0R
-/

module
import all LatticeCrypto.Falcon.Concrete.FloatLike
import all Extern.Falcon.FPR.Decode
public import Extern.Falcon.FPRBridge
public import Extern.Falcon.FFTLoops

/-!
# Binary64 butterflies with `#514`'s per-operation bounds

`Extern.Falcon.FPRBridge` bounds each `FPR` operation by the relative error `2^(-52)`, for
operands in `FPR.IsNormalOrZero` whose exact result lies in `FPR.InNormalMagnitudeRange`: zero, or
a magnitude between `2^(-1022)` and the largest finite value. The upper end is a size condition.
The lower end excludes exact results in `(0, 2^(-1022))`, which cancellation could produce, so a
chain of operations needs a positive lower bound on its nonzero intermediates.

This file supplies one. A normal binary64 value is an integer multiple of a power of two that is
more than `2^(-53)` times its magnitude (`exists_grid`), so a nonzero sum of two such values is at
least `2^(-53)` times the smaller one (`min_abs_le_two_pow_mul_abs_add`). `Good m M x` records that
`x` is in the operand domain, is zero or at least `m` in magnitude, and is at most `M`; `good_add`,
`good_sub` and `good_mul` apply the per-operation bounds of `#514` and return `Good` again with
explicit constants.

On complex numbers stored as `(re, im)` pairs, `fwdBFF_error` and `invBFF_error` bound one
forward and one inverse butterfly of `fpolyFFT` / `fpolyIFFT` against the exact butterflies
`Falcon.FFTStages.fwdBF` / `invBF` with an exact twiddle `σ` within `δ` of the stored one.
-/

public section

namespace Falcon.Concrete.Binary64

open Falcon.Concrete.FPRBridge Falcon.Concrete.FPR Falcon.FFTStages Complex

/-- The relative error bound `2^(-52)` of the `FPR` operations. -/
@[expose] noncomputable def u : ℝ := (2 : ℝ) ^ (-(52 : ℤ))

private theorem two_zpow_neg_52 : (2 : ℝ) ^ (-(52 : ℤ)) = u := by unfold u; rfl

/-- `u` is `2^(-52)`. -/
theorem u_eq : u = (2 : ℝ) ^ (-(52 : ℤ)) := two_zpow_neg_52.symm

/-- `u` is positive. -/
theorem u_pos : 0 < u := by unfold u; positivity

private theorem u_le : u ≤ 1 / 1024 := by
  norm_num [u]

/-! ## The integer grid of a binary64 value -/

/-- A finite binary64 value is an integer multiple `N · 2^E` with magnitude below `2^53 · 2^E`. -/
theorem exists_grid (x : FPR) (hx : FPR.IsNormalOrZero x) :
    ∃ N E : ℤ, toReal x = N * (2 : ℝ) ^ E ∧ |toReal x| < 2 ^ 53 * (2 : ℝ) ^ E := by
  have hne : (FPR.decode x).exponent ≠ 2047 := by
    rcases hx with h | h
    · exact h.2
    · rw [h.1]; norm_num
  set b := FPR.decode x
  refine ⟨(if b.sign then -1 else 1) * (b.significand : ℤ), (b.workExp : ℤ) - 1023 - 52, ?_, ?_⟩
  · change b.toReal = _
    rw [FPR.Bits.toReal_eq_of_exponent_ne_2047 b hne]
    split_ifs <;> push_cast <;> ring
  · change |b.toReal| < _
    rw [FPR.Bits.toReal_eq_of_exponent_ne_2047 b hne]
    have hsig : (b.significand : ℝ) < 2 ^ 53 := by
      have hm : b.mantissa < 2 ^ 52 := FPR.decode_mantissa_lt x
      have : b.significand < 2 ^ 53 := by
        unfold FPR.Bits.significand; split_ifs <;> omega
      exact_mod_cast this
    have hsgn : |(if b.sign then (-1 : ℝ) else 1)| = 1 := by split_ifs <;> simp
    rw [abs_mul, abs_mul, hsgn, one_mul, Nat.abs_cast, abs_of_pos (by positivity)]
    exact mul_lt_mul_of_pos_right hsig (by positivity)

/-- **No subnormal cancellation.** A nonzero sum of two finite binary64 values is at least
`2^(-53)` times the smaller magnitude. -/
theorem min_abs_le_two_pow_mul_abs_add (a b : FPR) (ha : FPR.IsNormalOrZero a)
    (hb : FPR.IsNormalOrZero b) (hs : toReal a + toReal b ≠ 0) :
    min |toReal a| |toReal b| ≤ 2 ^ 53 * |toReal a + toReal b| := by
  obtain ⟨Na, Ea, hNa, hlta⟩ := exists_grid a ha
  obtain ⟨Nb, Eb, hNb, hltb⟩ := exists_grid b hb
  have key : ∀ E : ℤ, E ≤ Ea → E ≤ Eb → (2 : ℝ) ^ E ≤ |toReal a + toReal b| := by
    intro E h1 h2
    have e1 : (2 : ℝ) ^ Ea = ((2 ^ (Ea - E).toNat : ℕ) : ℝ) * 2 ^ E := by
      rw [Nat.cast_pow, Nat.cast_ofNat, ← zpow_natCast, ← zpow_add₀ (by norm_num)]
      congr 1; omega
    have e2 : (2 : ℝ) ^ Eb = ((2 ^ (Eb - E).toNat : ℕ) : ℝ) * 2 ^ E := by
      rw [Nat.cast_pow, Nat.cast_ofNat, ← zpow_natCast, ← zpow_add₀ (by norm_num)]
      congr 1; omega
    set M : ℤ := Na * (2 ^ (Ea - E).toNat : ℕ) + Nb * (2 ^ (Eb - E).toNat : ℕ)
    have hM : toReal a + toReal b = (M : ℝ) * 2 ^ E := by
      rw [hNa, hNb, e1, e2]; simp only [M]; push_cast; ring
    have hM0 : M ≠ 0 := by
      rintro h; rw [h, Int.cast_zero, zero_mul] at hM; exact hs hM
    rw [hM, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ E)]
    have : (1 : ℝ) ≤ |(M : ℝ)| := by exact_mod_cast Int.one_le_abs hM0
    nlinarith [(by positivity : (0 : ℝ) < 2 ^ E)]
  rcases le_total Ea Eb with h | h
  · calc min |toReal a| |toReal b| ≤ |toReal a| := min_le_left _ _
      _ ≤ 2 ^ 53 * 2 ^ Ea := hlta.le
      _ ≤ 2 ^ 53 * |toReal a + toReal b| := by gcongr; exact key Ea le_rfl h
  · calc min |toReal a| |toReal b| ≤ |toReal b| := min_le_right _ _
      _ ≤ 2 ^ 53 * 2 ^ Eb := hltb.le
      _ ≤ 2 ^ 53 * |toReal a + toReal b| := by gcongr; exact key Eb h le_rfl

/-! ## Operands with a magnitude window -/

/-- `x` is in the operand domain of `#514`'s bounds, is zero or at least `m` in magnitude, and is
at most `M` in magnitude. -/
@[expose] def Good (m M : ℝ) (x : FPR) : Prop :=
  FPR.IsNormalOrZero x ∧ (toReal x = 0 ∨ m ≤ |toReal x|) ∧ |toReal x| ≤ M

/-- `Good` is monotone in both bounds. -/
theorem Good.mono {m M m' M' : ℝ} {x : FPR} (h : Good m M x) (hm : m' ≤ m) (hM : M ≤ M') :
    Good m' M' x :=
  ⟨h.1, h.2.1.imp id (le_trans hm), h.2.2.trans hM⟩

private theorem inRange_of {r : ℝ}
    (h : r = 0 ∨ ((2 : ℝ) ^ (-(1022 : ℤ)) ≤ |r| ∧ |r| ≤ 2 ^ (1023 : ℤ))) :
    FPR.InNormalMagnitudeRange r := by
  rcases h with h | ⟨h1, h2⟩
  · exact Or.inl h
  · refine Or.inr ⟨h1, h2.trans ?_⟩
    unfold FPR.maxFiniteReal
    have : (1 : ℝ) ≤ 2 - 2 ^ (-(52 : ℤ)) := by
      have : (2 : ℝ) ^ (-(52 : ℤ)) ≤ 1 := zpow_le_one_of_nonpos₀ (by norm_num) (by norm_num)
      linarith
    exact le_mul_of_one_le_left (by positivity) this

private theorem lower_of_rel {r s : ℝ} (h : |r - s| ≤ u * |s|) : (1 - u) * |s| ≤ |r| := by
  have := abs_sub_abs_le_abs_sub s r
  rw [abs_sub_comm] at this
  linarith

private theorem upper_of_rel {r s : ℝ} (h : |r - s| ≤ u * |s|) : |r| ≤ (1 + u) * |s| := by
  have := abs_sub_abs_le_abs_sub r s
  linarith

private theorem zero_of_rel {r : ℝ} (h : |r - 0| ≤ u * |0|) : r = 0 := by
  simpa using h

private theorem lb_sum {m M M' : ℝ} {a b : FPR} (hm : 0 ≤ m) (ha : Good m M a) (hb : Good m M' b)
    (hs : toReal a + toReal b ≠ 0) : (2 : ℝ) ^ (-(53 : ℤ)) * m ≤ |toReal a + toReal b| := by
  have h53 : (2 : ℝ) ^ (-(53 : ℤ)) * 2 ^ 53 = 1 := by norm_num
  have hle1 : (2 : ℝ) ^ (-(53 : ℤ)) ≤ 1 := zpow_le_one_of_nonpos₀ (by norm_num) (by norm_num)
  rcases ha.2.1 with ha0 | ha0
  · rw [ha0, zero_add] at hs ⊢
    rcases hb.2.1 with hb0 | hb0
    · exact absurd hb0 hs
    · nlinarith
  · rcases hb.2.1 with hb0 | hb0
    · rw [hb0, add_zero] at hs ⊢; nlinarith
    · have := min_abs_le_two_pow_mul_abs_add a b ha.1 hb.1 hs
      have hmin : m ≤ min |toReal a| |toReal b| := le_min ha0 hb0
      have h2 : (0 : ℝ) < 2 ^ (-(53 : ℤ)) := by positivity
      calc (2 : ℝ) ^ (-(53 : ℤ)) * m ≤ 2 ^ (-(53 : ℤ)) * (2 ^ 53 * |toReal a + toReal b|) :=
            mul_le_mul_of_nonneg_left (hmin.trans this) h2.le
        _ = |toReal a + toReal b| := by rw [← mul_assoc, h53, one_mul]

private theorem half_le_one_sub_u : (1 : ℝ) / 2 ≤ 1 - u := by linarith [u_le]

/-- Addition keeps operands `Good`, losing `2^54` on the lower bound. -/
theorem good_add {m M : ℝ} {a b : FPR} (ha : Good m M a) (hb : Good m M b)
    (hm : (2 : ℝ) ^ (-(1022 : ℤ)) ≤ 2 ^ (-(53 : ℤ)) * m) (hM : 2 * M ≤ 2 ^ (1023 : ℤ)) :
    |toReal (FPR.add a b) - (toReal a + toReal b)| ≤ u * |toReal a + toReal b| ∧
      Good (2 ^ (-(54 : ℤ)) * m) (2 * M * (1 + u)) (FPR.add a b) := by
  have hm0 : 0 ≤ m := by
    have : (0 : ℝ) < 2 ^ (-(53 : ℤ)) * m := lt_of_lt_of_le (by positivity) hm
    exact (pos_of_mul_pos_right this (by positivity)).le
  have hub : |toReal a + toReal b| ≤ 2 * M := by
    linarith [abs_add_le (toReal a) (toReal b), ha.2.2, hb.2.2]
  have hlb : toReal a + toReal b = 0 ∨ 2 ^ (-(53 : ℤ)) * m ≤ |toReal a + toReal b| := by
    by_cases hs : toReal a + toReal b = 0
    · exact Or.inl hs
    · exact Or.inr (lb_sum hm0 ha hb hs)
  have hr : FPR.InNormalMagnitudeRange (toReal a + toReal b) :=
    inRange_of (hlb.imp id fun h => ⟨hm.trans h, hub.trans hM⟩)
  have herr := add_error a b ha.1 hb.1 hr
  rw [two_zpow_neg_52] at herr
  refine ⟨herr, add_isNormalOrZero a b ha.1 hb.1 hr, ?_, ?_⟩
  · rcases hlb with h0 | h0
    · left; rw [h0] at herr; exact zero_of_rel herr
    · right
      have := lower_of_rel herr
      have h54 : (2 : ℝ) ^ (-(54 : ℤ)) = 2 ^ (-(53 : ℤ)) / 2 := by
        rw [show (-(54 : ℤ)) = -(53 : ℤ) + (-1) by norm_num, zpow_add₀ (by norm_num)]
        simp [div_eq_mul_inv]
      rw [h54]
      calc (2 : ℝ) ^ (-(53 : ℤ)) / 2 * m = 1 / 2 * (2 ^ (-(53 : ℤ)) * m) := by ring
        _ ≤ 1 / 2 * |toReal a + toReal b| := by gcongr
        _ ≤ (1 - u) * |toReal a + toReal b| := by gcongr; exact half_le_one_sub_u
        _ ≤ _ := this
  · have := upper_of_rel herr
    nlinarith [u_pos]

private theorem toReal_sub_eq (a b : FPR) :
    toReal a + toReal (FPR.neg b) = toReal a - toReal b := by
  rw [toReal_neg]; ring

/-- Subtraction keeps operands `Good`, losing `2^54` on the lower bound. -/
theorem good_sub {m M : ℝ} {a b : FPR} (ha : Good m M a) (hb : Good m M b)
    (hm : (2 : ℝ) ^ (-(1022 : ℤ)) ≤ 2 ^ (-(53 : ℤ)) * m) (hM : 2 * M ≤ 2 ^ (1023 : ℤ)) :
    |toReal (FPR.sub a b) - (toReal a - toReal b)| ≤ u * |toReal a - toReal b| ∧
      Good (2 ^ (-(54 : ℤ)) * m) (2 * M * (1 + u)) (FPR.sub a b) := by
  have hnb : Good m M (FPR.neg b) := by
    refine ⟨FPR.isNormalOrZero_neg hb.1, ?_, ?_⟩
    · rw [toReal_neg, abs_neg, neg_eq_zero]; exact hb.2.1
    · rw [toReal_neg, abs_neg]; exact hb.2.2
  have h := good_add ha hnb hm hM
  rw [toReal_sub_eq] at h
  exact h

/-- Multiplication keeps operands `Good`. -/
theorem good_mul {m₁ M₁ m₂ M₂ : ℝ} {a b : FPR} (ha : Good m₁ M₁ a) (hb : Good m₂ M₂ b)
    (hm₁ : 0 ≤ m₁) (hm₂ : 0 ≤ m₂) (hm : (2 : ℝ) ^ (-(1022 : ℤ)) ≤ m₁ * m₂)
    (hM : M₁ * M₂ ≤ 2 ^ (1023 : ℤ)) :
    |toReal (FPR.mul a b) - toReal a * toReal b| ≤ u * |toReal a * toReal b| ∧
      Good (m₁ * m₂ / 2) (M₁ * M₂ * (1 + u)) (FPR.mul a b) := by
  have hM₁ : 0 ≤ M₁ := (abs_nonneg _).trans ha.2.2
  have hub : |toReal a * toReal b| ≤ M₁ * M₂ := by
    rw [abs_mul]; exact mul_le_mul ha.2.2 hb.2.2 (abs_nonneg _) hM₁
  have hlb : toReal a * toReal b = 0 ∨ m₁ * m₂ ≤ |toReal a * toReal b| := by
    rcases ha.2.1 with h | h
    · left; rw [h, zero_mul]
    · rcases hb.2.1 with h' | h'
      · left; rw [h', mul_zero]
      · right; rw [abs_mul]; exact mul_le_mul h h' hm₂ (hm₁.trans h)
  have hr : FPR.InNormalMagnitudeRange (toReal a * toReal b) :=
    inRange_of (hlb.imp id fun h => ⟨hm.trans h, hub.trans hM⟩)
  have herr := mul_error a b ha.1 hb.1 hr
  rw [two_zpow_neg_52] at herr
  refine ⟨herr, mul_isNormalOrZero a b ha.1 hb.1 hr, ?_, ?_⟩
  · rcases hlb with h0 | h0
    · left; rw [h0] at herr; exact zero_of_rel herr
    · right
      have := lower_of_rel herr
      calc m₁ * m₂ / 2 = 1 / 2 * (m₁ * m₂) := by ring
        _ ≤ 1 / 2 * |toReal a * toReal b| := by gcongr
        _ ≤ (1 - u) * |toReal a * toReal b| := by gcongr; exact half_le_one_sub_u
        _ ≤ _ := this
  · have := upper_of_rel herr
    nlinarith [u_pos]

/-! ## Two-step error accumulation -/

private theorem sum_err {p q P Q z B : ℝ} (hP : |P| ≤ B) (hQ : |Q| ≤ B) (hp : |p - P| ≤ u * |P|)
    (hq : |q - Q| ≤ u * |Q|) (hz : |z - (p + q)| ≤ u * |p + q|) :
    |z - (P + Q)| ≤ 5 * u * B ∧ |z| ≤ 3 * B := by
  have hu := u_pos
  have hu1 := u_le
  have hB : 0 ≤ B := (abs_nonneg _).trans hP
  have hpq : |p + q| ≤ (1 + u) * (2 * B) := by
    have h1 : |p| ≤ (1 + u) * |P| := upper_of_rel hp
    have h2 : |q| ≤ (1 + u) * |Q| := upper_of_rel hq
    calc |p + q| ≤ |p| + |q| := abs_add_le _ _
      _ ≤ (1 + u) * |P| + (1 + u) * |Q| := add_le_add h1 h2
      _ ≤ (1 + u) * B + (1 + u) * B := by gcongr
      _ = (1 + u) * (2 * B) := by ring
  have herr : |z - (P + Q)| ≤ 5 * u * B := by
    calc |z - (P + Q)| = |(z - (p + q)) + (p - P) + (q - Q)| := by ring_nf
      _ ≤ |z - (p + q)| + |p - P| + |q - Q| := abs_add_three _ _ _
      _ ≤ u * ((1 + u) * (2 * B)) + u * B + u * B := by
          gcongr
          · exact hz.trans (by gcongr)
          · exact hp.trans (by gcongr)
          · exact hq.trans (by gcongr)
      _ ≤ 5 * u * B := by
          nlinarith [mul_nonneg (mul_nonneg hu.le hB) (by linarith : (0 : ℝ) ≤ 1 - 2 * u)]
  refine ⟨herr, ?_⟩
  calc |z| = |(z - (P + Q)) + (P + Q)| := by ring_nf
    _ ≤ |z - (P + Q)| + (|P| + |Q|) := (abs_add_le _ _).trans (by gcongr; exact abs_add_le _ _)
    _ ≤ 5 * u * B + (B + B) := by gcongr
    _ ≤ 3 * B := by nlinarith [mul_nonneg hB (by linarith : (0 : ℝ) ≤ 1 - 5 * u)]

private theorem add_err {x z Z o B : ℝ} (hx : |x| ≤ B) (hzb : |z| ≤ 3 * B)
    (hz : |z - Z| ≤ 5 * u * B) (ho : |o - (x + z)| ≤ u * |x + z|) : |o - (x + Z)| ≤ 9 * u * B := by
  have hu := u_pos
  calc |o - (x + Z)| = |(o - (x + z)) + (z - Z)| := by ring_nf
    _ ≤ |o - (x + z)| + |z - Z| := abs_add_le _ _
    _ ≤ u * (B + 3 * B) + 5 * u * B := by
        gcongr
        exact ho.trans (by gcongr; exact (abs_add_le _ _).trans (add_le_add hx hzb))
    _ = 9 * u * B := by ring

/-! ## Complex numbers as pairs -/

/-- A pair `(re, im)` of binary64 values as a complex number. -/
@[expose] noncomputable def cplx (p : FPR × FPR) : ℂ := ⟨toReal p.1, toReal p.2⟩

/-- The real part of a pair read as a complex number. -/
@[simp] theorem cplx_re (p : FPR × FPR) : (cplx p).re = toReal p.1 := rfl

/-- The imaginary part of a pair read as a complex number. -/
@[simp] theorem cplx_im (p : FPR × FPR) : (cplx p).im = toReal p.2 := rfl

/-- Both parts of a pair are `Good`. -/
@[expose] def GoodP (m M : ℝ) (p : FPR × FPR) : Prop := Good m M p.1 ∧ Good m M p.2

/-- `GoodP` is monotone in both bounds. -/
theorem GoodP.mono {m M m' M' : ℝ} {p : FPR × FPR} (h : GoodP m M p) (hm : m' ≤ m)
    (hM : M ≤ M') : GoodP m' M' p :=
  ⟨h.1.mono hm hM, h.2.mono hm hM⟩

/-- A complex number whose parts are at most `e` has modulus at most `2 · e`. -/
theorem norm_le_of_parts {z : ℂ} {e : ℝ} (hre : |z.re| ≤ e) (him : |z.im| ≤ e) : ‖z‖ ≤ 2 * e :=
  (Complex.norm_le_abs_re_add_abs_im z).trans (by linarith)

private theorem re_le {z : ℂ} {B : ℝ} (h : ‖z‖ ≤ B) : |z.re| ≤ B :=
  (Complex.abs_re_le_norm z).trans h

private theorem im_le {z : ℂ} {B : ℝ} (h : ‖z‖ ≤ B) : |z.im| ≤ B :=
  (Complex.abs_im_le_norm z).trans h

private theorem prod_le {x e B : ℝ} (hx : |x| ≤ B) (he : |e| ≤ 1) : |x * e| ≤ B := by
  rw [abs_mul]; nlinarith [abs_nonneg x, abs_nonneg e]

private theorem lowExp_le (m : ℝ) (hm : 0 ≤ m) (ms : ℝ) (hms : 0 ≤ ms) (hms1 : ms ≤ 1) :
    (2 : ℝ) ^ (-(54 : ℤ)) * (2 ^ (-(54 : ℤ)) * (m * ms / 2)) ≤ 2 ^ (-(54 : ℤ)) * (m * ms / 2) ∧
      (2 : ℝ) ^ (-(54 : ℤ)) * (m * ms / 2) ≤ m * ms / 2 ∧ m * ms / 2 ≤ m ∧
      (2 : ℝ) ^ (-(54 : ℤ)) * m ≤ m := by
  have h54 : (2 : ℝ) ^ (-(54 : ℤ)) ≤ 1 := zpow_le_one_of_nonpos₀ (by norm_num) (by norm_num)
  have h0 : 0 ≤ m * ms / 2 := by positivity
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact mul_le_of_le_one_left (by positivity) h54
  · exact mul_le_of_le_one_left h0 h54
  · nlinarith
  · exact mul_le_of_le_one_left hm h54

/-- The lower bound after one butterfly: `2^(-108) · m · ms / 2`. -/
@[expose] noncomputable def nextLow (m ms : ℝ) : ℝ :=
  2 ^ (-(54 : ℤ)) * (2 ^ (-(54 : ℤ)) * (m * ms / 2))

private theorem one_add_u_cube : (1 + u) ^ 3 ≤ 2 := by
  calc (1 + u) ^ 3 ≤ (1 + 1 / 1024) ^ 3 :=
        pow_le_pow_left₀ (by linarith [u_pos]) (by linarith [u_le]) 3
    _ ≤ 2 := by norm_num

private theorem one_add_u_sq : (1 + u) ^ 2 ≤ 2 := by
  calc (1 + u) ^ 2 ≤ (1 + 1 / 1024) ^ 2 :=
        pow_le_pow_left₀ (by linarith [u_pos]) (by linarith [u_le]) 2
    _ ≤ 2 := by norm_num

private theorem cM_le {M X c : ℝ} (hM0 : 0 ≤ M) (hc : c ≤ 16) (h : 16 * M ≤ X) : c * M ≤ X :=
  le_trans (mul_le_mul_of_nonneg_right hc hM0) h

/-- **One forward butterfly of `fpolyFFT` in binary64.** With `Good` inputs bounded by `B` and
a stored twiddle within `δ` of the unit `σ`, both outputs are within `(δ + 18 · 2^(-52)) · B` of
the exact butterfly `x ± σ · y`, and are `Good` with the lower bound `nextLow m ms`. -/
theorem fwdBFF_error {m M B ms δ : ℝ} {σ : ℂ} (x y s : FPR × FPR) (hx : GoodP m M x)
    (hy : GoodP m M y) (hs : GoodP ms 1 s) (hm : 0 ≤ m) (hms : 0 ≤ ms) (hms1 : ms ≤ 1)
    (hlow : (2 : ℝ) ^ (-(1022 : ℤ)) ≤ 2 ^ (-(53 : ℤ)) * (2 ^ (-(54 : ℤ)) * (m * ms / 2)))
    (hM : 16 * M ≤ 2 ^ (1023 : ℤ)) (hδ : ‖cplx s - σ‖ ≤ δ)
    (hxB : ‖cplx x‖ ≤ B) (hyB : ‖cplx y‖ ≤ B) :
    ‖cplx (FFTOps.fwdBFF s (x, y)).1 - (cplx x + σ * cplx y)‖ ≤ (δ + 18 * u) * B ∧
      ‖cplx (FFTOps.fwdBFF s (x, y)).2 - (cplx x - σ * cplx y)‖ ≤ (δ + 18 * u) * B ∧
      GoodP (nextLow m ms) (8 * M) (FFTOps.fwdBFF s (x, y)).1 ∧
      GoodP (nextLow m ms) (8 * M) (FFTOps.fwdBFF s (x, y)).2 := by
  have hu := u_pos
  have hu1 := u_le
  have hM0 : 0 ≤ M := (abs_nonneg _).trans hx.1.2.2
  obtain ⟨hl1, hl2, hl3, hl4⟩ := lowExp_le m hm ms hms hms1
  have h2 : (2 : ℝ) ^ (-(53 : ℤ)) ≤ 1 := zpow_le_one_of_nonpos₀ (by norm_num) (by norm_num)
  have h54 : (2 : ℝ) ^ (-(54 : ℤ)) ≤ 1 := zpow_le_one_of_nonpos₀ (by norm_num) (by norm_num)
  have hpos54 : (0 : ℝ) < 2 ^ (-(54 : ℤ)) := by positivity
  have hpos53 : (0 : ℝ) < 2 ^ (-(53 : ℤ)) := by positivity
  -- the four products
  have hmul : (2 : ℝ) ^ (-(1022 : ℤ)) ≤ m * ms := by
    have : 2 ^ (-(53 : ℤ)) * (2 ^ (-(54 : ℤ)) * (m * ms / 2)) ≤ m * ms := by
      have := mul_le_of_le_one_left (by positivity : (0 : ℝ) ≤ 2 ^ (-(54 : ℤ)) * (m * ms / 2)) h2
      nlinarith
    linarith
  have hMm : M * 1 ≤ (2 : ℝ) ^ (1023 : ℤ) := by
    rw [mul_one]; simpa using cM_le hM0 (by norm_num : (1 : ℝ) ≤ 16) hM
  obtain ⟨e1, g1⟩ := good_mul hy.1 hs.1 hm hms hmul hMm
  obtain ⟨e2, g2⟩ := good_mul hy.2 hs.2 hm hms hmul hMm
  obtain ⟨e3, g3⟩ := good_mul hy.2 hs.1 hm hms hmul hMm
  obtain ⟨e4, g4⟩ := good_mul hy.1 hs.2 hm hms hmul hMm
  -- the twiddled value
  have hsub : (2 : ℝ) ^ (-(1022 : ℤ)) ≤ 2 ^ (-(53 : ℤ)) * (m * ms / 2) := by
    calc (2 : ℝ) ^ (-(1022 : ℤ)) ≤ _ := hlow
      _ ≤ 2 ^ (-(53 : ℤ)) * (m * ms / 2) := by gcongr
  have hM2 : 2 * (M * 1 * (1 + u)) ≤ (2 : ℝ) ^ (1023 : ℤ) := by
    calc 2 * (M * 1 * (1 + u)) = (2 * (1 + u)) * M := by ring
      _ ≤ _ := cM_le hM0 (by linarith) hM
  obtain ⟨ez1, gz1⟩ := good_sub g1 g2 hsub hM2
  obtain ⟨ez2, gz2⟩ := good_add g3 g4 hsub hM2
  -- the outputs
  set m2 := 2 ^ (-(54 : ℤ)) * (m * ms / 2)
  set M2 := 2 * (M * 1 * (1 + u)) * (1 + u)
  have hMM2 : M ≤ M2 := by
    calc M = 1 * M := by ring
      _ ≤ (2 * (1 + u) ^ 2) * M := by gcongr; nlinarith
      _ = M2 := by simp only [M2]; ring
  have hxa : Good m2 M2 x.1 := hx.1.mono (hl2.trans hl3) hMM2
  have hxb : Good m2 M2 x.2 := hx.2.mono (hl2.trans hl3) hMM2
  have hM3 : 2 * M2 ≤ (2 : ℝ) ^ (1023 : ℤ) := by
    calc 2 * M2 = (4 * (1 + u) ^ 2) * M := by simp only [M2]; ring
      _ ≤ _ := cM_le hM0 (by nlinarith [one_add_u_sq]) hM
  have hM8 : 2 * M2 * (1 + u) ≤ 8 * M := by
    calc 2 * M2 * (1 + u) = (4 * (1 + u) ^ 3) * M := by simp only [M2]; ring
      _ ≤ 8 * M := by gcongr; nlinarith [one_add_u_cube]
  obtain ⟨eo1, go1⟩ := good_add hxa gz1 hlow hM3
  obtain ⟨eo2, go2⟩ := good_add hxb gz2 hlow hM3
  obtain ⟨eo3, go3⟩ := good_sub hxa gz1 hlow hM3
  obtain ⟨eo4, go4⟩ := good_sub hxb gz2 hlow hM3
  -- error of the twiddled value
  have hc := re_le hyB
  have hd := im_le hyB
  have he : |toReal s.1| ≤ 1 := hs.1.2.2
  have hf : |toReal s.2| ≤ 1 := hs.2.2.2
  simp only [cplx_re, cplx_im] at hc hd
  have e2' : |-toReal (FPR.mul y.2 s.2) - -(toReal y.2 * toReal s.2)| ≤
      u * |-(toReal y.2 * toReal s.2)| := by
    rw [← neg_sub', abs_neg, abs_neg]; exact e2
  have ez1' : |toReal (FPR.sub (FPR.mul y.1 s.1) (FPR.mul y.2 s.2)) -
      (toReal (FPR.mul y.1 s.1) + -toReal (FPR.mul y.2 s.2))| ≤
      u * |toReal (FPR.mul y.1 s.1) + -toReal (FPR.mul y.2 s.2)| := by
    rw [← sub_eq_add_neg]; exact ez1
  have hdf : |-(toReal y.2 * toReal s.2)| ≤ B := by rw [abs_neg]; exact prod_le hd hf
  obtain ⟨hz1, hz1b⟩ := sum_err (prod_le hc he) hdf e1 e2' ez1'
  obtain ⟨hz2, hz2b⟩ := sum_err (prod_le hd he) (prod_le hc hf) e3 e4 ez2
  have ha := re_le hxB
  have hb := im_le hxB
  simp only [cplx_re, cplx_im] at ha hb
  have o1 := add_err ha hz1b hz1 eo1
  have o2 := add_err hb hz2b hz2 eo2
  have o3 := add_err (z := -toReal (FPR.sub (FPR.mul y.1 s.1) (FPR.mul y.2 s.2)))
    (Z := -(toReal y.1 * toReal s.1 + -(toReal y.2 * toReal s.2)))
    (o := toReal (FPR.sub x.1 (FPR.sub (FPR.mul y.1 s.1) (FPR.mul y.2 s.2)))) ha
    (by rw [abs_neg]; exact hz1b) (by rw [← neg_add', abs_neg]; exact hz1)
    (by rw [← sub_eq_add_neg]; exact eo3)
  have o4 := add_err (z := -toReal (FPR.add (FPR.mul y.2 s.1) (FPR.mul y.1 s.2)))
    (Z := -(toReal y.2 * toReal s.1 + toReal y.1 * toReal s.2))
    (o := toReal (FPR.sub x.2 (FPR.add (FPR.mul y.2 s.1) (FPR.mul y.1 s.2)))) hb
    (by rw [abs_neg]; exact hz2b) (by rw [← neg_add', abs_neg]; exact hz2)
    (by rw [← sub_eq_add_neg]; exact eo4)
  -- the twiddle error
  have htw : ‖(cplx s - σ) * cplx y‖ ≤ δ * B := by
    rw [norm_mul]; exact mul_le_mul hδ hyB (norm_nonneg _) ((norm_nonneg _).trans hδ)
  have hr1 : (FFTOps.fwdBFF s (x, y)).1 =
      (FPR.add x.1 (FPR.sub (FPR.mul y.1 s.1) (FPR.mul y.2 s.2)),
      FPR.add x.2 (FPR.add (FPR.mul y.2 s.1) (FPR.mul y.1 s.2))) := rfl
  have hr2 : (FFTOps.fwdBFF s (x, y)).2 =
      (FPR.sub x.1 (FPR.sub (FPR.mul y.1 s.1) (FPR.mul y.2 s.2)),
      FPR.sub x.2 (FPR.add (FPR.mul y.2 s.1) (FPR.mul y.1 s.2))) := rfl
  rw [hr1, hr2]
  refine ⟨?_, ?_, ⟨go1.mono le_rfl hM8, go2.mono le_rfl hM8⟩,
    ⟨go3.mono le_rfl hM8, go4.mono le_rfl hM8⟩⟩
  · have hpart : ‖cplx (FPR.add x.1 (FPR.sub (FPR.mul y.1 s.1) (FPR.mul y.2 s.2)),
        FPR.add x.2 (FPR.add (FPR.mul y.2 s.1) (FPR.mul y.1 s.2))) - (cplx x + cplx s * cplx y)‖ ≤
        18 * u * B := by
      have h := norm_le_of_parts (e := 9 * u * B)
        (z := cplx (FPR.add x.1 (FPR.sub (FPR.mul y.1 s.1) (FPR.mul y.2 s.2)),
          FPR.add x.2 (FPR.add (FPR.mul y.2 s.1) (FPR.mul y.1 s.2))) - (cplx x + cplx s * cplx y))
        (by simp only [Complex.sub_re, Complex.add_re, Complex.mul_re, cplx_re, cplx_im]
            convert o1 using 2; ring)
        (by simp only [Complex.sub_im, Complex.add_im, Complex.mul_im, cplx_re, cplx_im]
            convert o2 using 2; ring)
      exact h.trans (le_of_eq (by ring))
    calc _ = ‖(cplx (FPR.add x.1 (FPR.sub (FPR.mul y.1 s.1) (FPR.mul y.2 s.2)),
          FPR.add x.2 (FPR.add (FPR.mul y.2 s.1) (FPR.mul y.1 s.2))) - (cplx x + cplx s * cplx y)) +
          (cplx s - σ) * cplx y‖ := by ring_nf
      _ ≤ _ := norm_add_le _ _
      _ ≤ 18 * u * B + δ * B := add_le_add hpart htw
      _ = (δ + 18 * u) * B := by ring
  · have hpart : ‖cplx (FPR.sub x.1 (FPR.sub (FPR.mul y.1 s.1) (FPR.mul y.2 s.2)),
        FPR.sub x.2 (FPR.add (FPR.mul y.2 s.1) (FPR.mul y.1 s.2))) - (cplx x - cplx s * cplx y)‖ ≤
        18 * u * B := by
      have h := norm_le_of_parts (e := 9 * u * B)
        (z := cplx (FPR.sub x.1 (FPR.sub (FPR.mul y.1 s.1) (FPR.mul y.2 s.2)),
          FPR.sub x.2 (FPR.add (FPR.mul y.2 s.1) (FPR.mul y.1 s.2))) - (cplx x - cplx s * cplx y))
        (by simp only [Complex.sub_re, Complex.mul_re, cplx_re, cplx_im]
            convert o3 using 2; ring)
        (by simp only [Complex.sub_im, Complex.mul_im, cplx_re, cplx_im]
            convert o4 using 2; ring)
      exact h.trans (le_of_eq (by ring))
    calc _ = ‖(cplx (FPR.sub x.1 (FPR.sub (FPR.mul y.1 s.1) (FPR.mul y.2 s.2)),
          FPR.sub x.2 (FPR.add (FPR.mul y.2 s.1) (FPR.mul y.1 s.2))) - (cplx x - cplx s * cplx y)) -
          (cplx s - σ) * cplx y‖ := by ring_nf
      _ ≤ _ := norm_sub_le _ _
      _ ≤ 18 * u * B + δ * B := add_le_add hpart htw
      _ = (δ + 18 * u) * B := by ring

private theorem good_neg {m M : ℝ} {a : FPR} (h : Good m M a) : Good m M (FPR.neg a) := by
  refine ⟨FPR.isNormalOrZero_neg h.1, ?_, ?_⟩
  · rw [toReal_neg, abs_neg, neg_eq_zero]; exact h.2.1
  · rw [toReal_neg, abs_neg]; exact h.2.2

private theorem four_u_le {δ B : ℝ} (hδ0 : 0 ≤ δ) (hB : 0 ≤ B) :
    2 * (2 * u * B) ≤ (2 * δ + 38 * u) * B := by
  have := u_pos
  nlinarith [mul_nonneg hδ0 hB, mul_nonneg this.le hB]

private theorem abs_le_three {r s B : ℝ} (h : |r - s| ≤ u * |s|) (hs : |s| ≤ 2 * B) :
    |r| ≤ 3 * B := by
  have h1 := upper_of_rel h
  have hu := u_le
  have hu0 := u_pos
  have hB : 0 ≤ B := by linarith [abs_nonneg s]
  nlinarith [abs_nonneg s]

private theorem err_two {r s B : ℝ} (h : |r - s| ≤ u * |s|) (hs : |s| ≤ 2 * B) :
    |r - s| ≤ 2 * u * B :=
  h.trans (by have := u_pos; nlinarith)

private theorem abs_sub_le_two {a c B : ℝ} (ha : |a| ≤ B) (hc : |c| ≤ B) : |a - c| ≤ 2 * B :=
  (abs_sub _ _).trans (by linarith)

private theorem abs_add_le_two {a c B : ℝ} (ha : |a| ≤ B) (hc : |c| ≤ B) : |a + c| ≤ 2 * B :=
  (abs_add_le _ _).trans (by linarith)

/-- **One inverse butterfly of `fpolyIFFT` in binary64.** With `Good` inputs bounded by `B` and
a stored twiddle within `δ` of `σ`, the outputs are within `(2δ + 38 · 2^(-52)) · B` of the exact
butterfly `(x + y, (x - y) · σ̄)`, and are `Good` with the lower bound `nextLow m ms`. -/
theorem invBFF_error {m M B ms δ : ℝ} {σ : ℂ} (x y s : FPR × FPR) (hx : GoodP m M x)
    (hy : GoodP m M y) (hs : GoodP ms 1 s) (hm : 0 ≤ m) (hms : 0 ≤ ms) (hms1 : ms ≤ 1)
    (hlow : (2 : ℝ) ^ (-(1022 : ℤ)) ≤ 2 ^ (-(53 : ℤ)) * (2 ^ (-(54 : ℤ)) * (m * ms / 2)))
    (hM : 16 * M ≤ 2 ^ (1023 : ℤ)) (hδ : ‖cplx s - σ‖ ≤ δ)
    (hxB : ‖cplx x‖ ≤ B) (hyB : ‖cplx y‖ ≤ B) :
    ‖cplx (FFTOps.invBFF s (x, y)).1 - (cplx x + cplx y)‖ ≤ (2 * δ + 38 * u) * B ∧
      ‖cplx (FFTOps.invBFF s (x, y)).2 - (cplx x - cplx y) * (starRingEnd ℂ) σ‖ ≤
        (2 * δ + 38 * u) * B ∧
      GoodP (nextLow m ms) (8 * M) (FFTOps.invBFF s (x, y)).1 ∧
      GoodP (nextLow m ms) (8 * M) (FFTOps.invBFF s (x, y)).2 := by
  have hu := u_pos
  have hu1 := u_le
  have hM0 : 0 ≤ M := (abs_nonneg _).trans hx.1.2.2
  have hB : 0 ≤ B := (norm_nonneg _).trans hxB
  have hδ0 : 0 ≤ δ := (norm_nonneg _).trans hδ
  obtain ⟨hl1, hl2, hl3, hl4⟩ := lowExp_le m hm ms hms hms1
  have h2 : (2 : ℝ) ^ (-(53 : ℤ)) ≤ 1 := zpow_le_one_of_nonpos₀ (by norm_num) (by norm_num)
  have h54 : (2 : ℝ) ^ (-(54 : ℤ)) ≤ 1 := zpow_le_one_of_nonpos₀ (by norm_num) (by norm_num)
  -- sums and differences
  have hadd : (2 : ℝ) ^ (-(1022 : ℤ)) ≤ 2 ^ (-(53 : ℤ)) * m := by
    calc (2 : ℝ) ^ (-(1022 : ℤ)) ≤ _ := hlow
      _ ≤ 2 ^ (-(53 : ℤ)) * m := by gcongr; exact hl2.trans hl3
  have hM2 : 2 * M ≤ (2 : ℝ) ^ (1023 : ℤ) := cM_le hM0 (by norm_num) hM
  obtain ⟨ea1, ga1⟩ := good_add hx.1 hy.1 hadd hM2
  obtain ⟨ea2, ga2⟩ := good_add hx.2 hy.2 hadd hM2
  obtain ⟨eu1, gu1⟩ := good_sub hx.1 hy.1 hadd hM2
  obtain ⟨eu2, gu2⟩ := good_sub hx.2 hy.2 hadd hM2
  set m1 := 2 ^ (-(54 : ℤ)) * m
  set M1 := 2 * M * (1 + u)
  have hm1 : 0 ≤ m1 := by positivity
  -- products with the twiddle
  have hmul : (2 : ℝ) ^ (-(1022 : ℤ)) ≤ m1 * ms := by
    calc (2 : ℝ) ^ (-(1022 : ℤ)) ≤ _ := hlow
      _ = 2 ^ (-(53 : ℤ)) * (m1 * ms / 2) := by simp only [m1]; ring
      _ ≤ m1 * ms := by
          have : 0 ≤ m1 * ms := by positivity
          nlinarith
  have hMm : M1 * 1 ≤ (2 : ℝ) ^ (1023 : ℤ) := by
    calc M1 * 1 = (2 * (1 + u)) * M := by simp only [M1]; ring
      _ ≤ _ := cM_le hM0 (by linarith) hM
  have hns := good_neg hs.2
  obtain ⟨ep1, gp1⟩ := good_mul gu1 hs.1 hm1 hms hmul hMm
  obtain ⟨ep2, gp2⟩ := good_mul gu2 hns hm1 hms hmul hMm
  obtain ⟨ep3, gp3⟩ := good_mul gu2 hs.1 hm1 hms hmul hMm
  obtain ⟨ep4, gp4⟩ := good_mul gu1 hns hm1 hms hmul hMm
  have hsub : (2 : ℝ) ^ (-(1022 : ℤ)) ≤ 2 ^ (-(53 : ℤ)) * (m1 * ms / 2) := by
    calc (2 : ℝ) ^ (-(1022 : ℤ)) ≤ _ := hlow
      _ = 2 ^ (-(53 : ℤ)) * (m1 * ms / 2) := by simp only [m1]; ring
  have hM3 : 2 * (M1 * 1 * (1 + u)) ≤ (2 : ℝ) ^ (1023 : ℤ) := by
    calc 2 * (M1 * 1 * (1 + u)) = (4 * (1 + u) ^ 2) * M := by simp only [M1]; ring
      _ ≤ _ := cM_le hM0 (by nlinarith [one_add_u_sq]) hM
  obtain ⟨eo1, go1⟩ := good_sub gp1 gp2 hsub hM3
  obtain ⟨eo2, go2⟩ := good_add gp3 gp4 hsub hM3
  have hlowEq : 2 ^ (-(54 : ℤ)) * (m1 * ms / 2) = nextLow m ms := by
    simp only [m1, nextLow]; ring
  have hM8 : 2 * (M1 * 1 * (1 + u)) * (1 + u) ≤ 8 * M := by
    calc 2 * (M1 * 1 * (1 + u)) * (1 + u) = (4 * (1 + u) ^ 3) * M := by simp only [M1]; ring
      _ ≤ 8 * M := by gcongr; nlinarith [one_add_u_cube]
  have hM8' : 2 * M * (1 + u) ≤ 8 * M := by nlinarith
  have hnl : nextLow m ms ≤ 2 ^ (-(54 : ℤ)) * m := by
    simp only [nextLow]
    gcongr
    exact hl2.trans hl3
  -- real-valued errors
  have ha := re_le hxB
  have hb := im_le hxB
  have hc := re_le hyB
  have hd := im_le hyB
  have he : |toReal s.1| ≤ 1 := hs.1.2.2
  have hf : |toReal (FPR.neg s.2)| ≤ 1 := hns.2.2
  simp only [cplx_re, cplx_im] at ha hb hc hd
  have hac : |toReal x.1 - toReal y.1| ≤ 2 * B := abs_sub_le_two ha hc
  have hbd : |toReal x.2 - toReal y.2| ≤ 2 * B := abs_sub_le_two hb hd
  have hu1b : |toReal (FPR.sub x.1 y.1)| ≤ 3 * B := abs_le_three eu1 hac
  have hu2b : |toReal (FPR.sub x.2 y.2)| ≤ 3 * B := abs_le_three eu2 hbd
  have eu1' := err_two eu1 hac
  have eu2' := err_two eu2 hbd
  have ep2' : |-toReal (FPR.mul (FPR.sub x.2 y.2) (FPR.neg s.2)) -
      -(toReal (FPR.sub x.2 y.2) * toReal (FPR.neg s.2))| ≤
      u * |-(toReal (FPR.sub x.2 y.2) * toReal (FPR.neg s.2))| := by
    rw [← neg_sub', abs_neg, abs_neg]; exact ep2
  have eo1' : |toReal (FPR.sub (FPR.mul (FPR.sub x.1 y.1) s.1)
      (FPR.mul (FPR.sub x.2 y.2) (FPR.neg s.2))) -
      (toReal (FPR.mul (FPR.sub x.1 y.1) s.1) +
        -toReal (FPR.mul (FPR.sub x.2 y.2) (FPR.neg s.2)))| ≤
      u * |toReal (FPR.mul (FPR.sub x.1 y.1) s.1) +
        -toReal (FPR.mul (FPR.sub x.2 y.2) (FPR.neg s.2))| := by
    rw [← sub_eq_add_neg]; exact eo1
  obtain ⟨hr1, -⟩ :=
    sum_err (prod_le hu1b he) (by rw [abs_neg]; exact prod_le hu2b hf) ep1 ep2' eo1'
  obtain ⟨hr2, -⟩ := sum_err (prod_le hu2b he) (prod_le hu1b hf) ep3 ep4 eo2
  have hfe : toReal (FPR.neg s.2) = -toReal s.2 := toReal_neg _
  have hre : |toReal (FPR.sub (FPR.mul (FPR.sub x.1 y.1) s.1)
      (FPR.mul (FPR.sub x.2 y.2) (FPR.neg s.2))) -
      ((toReal x.1 - toReal y.1) * toReal s.1 + (toReal x.2 - toReal y.2) * toReal s.2)| ≤
      19 * u * B := by
    have h1 : |(toReal (FPR.sub x.1 y.1) - (toReal x.1 - toReal y.1)) * toReal s.1| ≤ 2 * u * B :=
      prod_le eu1' he
    have h2 : |(toReal (FPR.sub x.2 y.2) - (toReal x.2 - toReal y.2)) * toReal s.2| ≤ 2 * u * B :=
      prod_le eu2' (by rw [← abs_neg, ← hfe]; exact hf)
    calc _ = |(toReal (FPR.sub (FPR.mul (FPR.sub x.1 y.1) s.1)
          (FPR.mul (FPR.sub x.2 y.2) (FPR.neg s.2))) -
          (toReal (FPR.sub x.1 y.1) * toReal s.1 + -(toReal (FPR.sub x.2 y.2) *
            toReal (FPR.neg s.2)))) +
          (toReal (FPR.sub x.1 y.1) - (toReal x.1 - toReal y.1)) * toReal s.1 +
          (toReal (FPR.sub x.2 y.2) - (toReal x.2 - toReal y.2)) * toReal s.2| := by
          rw [hfe]; ring_nf
      _ ≤ _ := abs_add_three _ _ _
      _ ≤ 15 * u * B + 2 * u * B + 2 * u * B :=
          add_le_add_three (hr1.trans (le_of_eq (by ring))) h1 h2
      _ = 19 * u * B := by ring
  have him : |toReal (FPR.add (FPR.mul (FPR.sub x.2 y.2) s.1)
      (FPR.mul (FPR.sub x.1 y.1) (FPR.neg s.2))) -
      ((toReal x.2 - toReal y.2) * toReal s.1 - (toReal x.1 - toReal y.1) * toReal s.2)| ≤
      19 * u * B := by
    have h1 : |(toReal (FPR.sub x.2 y.2) - (toReal x.2 - toReal y.2)) * toReal s.1| ≤ 2 * u * B :=
      prod_le eu2' he
    have h2 : |(toReal (FPR.sub x.1 y.1) - (toReal x.1 - toReal y.1)) * toReal (FPR.neg s.2)| ≤
        2 * u * B :=
      prod_le eu1' hf
    calc _ = |(toReal (FPR.add (FPR.mul (FPR.sub x.2 y.2) s.1)
          (FPR.mul (FPR.sub x.1 y.1) (FPR.neg s.2))) -
          (toReal (FPR.sub x.2 y.2) * toReal s.1 + toReal (FPR.sub x.1 y.1) *
            toReal (FPR.neg s.2))) +
          (toReal (FPR.sub x.2 y.2) - (toReal x.2 - toReal y.2)) * toReal s.1 +
          (toReal (FPR.sub x.1 y.1) - (toReal x.1 - toReal y.1)) * toReal (FPR.neg s.2)| := by
          rw [hfe]; ring_nf
      _ ≤ _ := abs_add_three _ _ _
      _ ≤ 15 * u * B + 2 * u * B + 2 * u * B :=
          add_le_add_three (hr2.trans (le_of_eq (by ring))) h1 h2
      _ = 19 * u * B := by ring
  have hr1def : (FFTOps.invBFF s (x, y)).1 = (FPR.add x.1 y.1, FPR.add x.2 y.2) := rfl
  have hr2def : (FFTOps.invBFF s (x, y)).2 = (FPR.sub (FPR.mul (FPR.sub x.1 y.1) s.1)
      (FPR.mul (FPR.sub x.2 y.2) (FPR.neg s.2)), FPR.add (FPR.mul (FPR.sub x.2 y.2) s.1)
      (FPR.mul (FPR.sub x.1 y.1) (FPR.neg s.2))) := rfl
  rw [hr1def, hr2def]
  refine ⟨?_, ?_, ⟨ga1.mono hnl hM8', ga2.mono hnl hM8'⟩,
    ⟨go1.mono (le_of_eq hlowEq.symm) hM8, go2.mono (le_of_eq hlowEq.symm) hM8⟩⟩
  · have h := norm_le_of_parts (e := 2 * u * B)
      (z := cplx (FPR.add x.1 y.1, FPR.add x.2 y.2) - (cplx x + cplx y))
      (by simp only [Complex.sub_re, Complex.add_re, cplx_re]
          exact err_two ea1 (abs_add_le_two ha hc))
      (by simp only [Complex.sub_im, Complex.add_im, cplx_im]
          exact err_two ea2 (abs_add_le_two hb hd))
    calc _ ≤ 2 * (2 * u * B) := h
      _ ≤ (2 * δ + 38 * u) * B := four_u_le hδ0 hB
  · have hpart : ‖cplx (FPR.sub (FPR.mul (FPR.sub x.1 y.1) s.1)
        (FPR.mul (FPR.sub x.2 y.2) (FPR.neg s.2)), FPR.add (FPR.mul (FPR.sub x.2 y.2) s.1)
        (FPR.mul (FPR.sub x.1 y.1) (FPR.neg s.2))) -
        (cplx x - cplx y) * (starRingEnd ℂ) (cplx s)‖ ≤ 38 * u * B := by
      have h := norm_le_of_parts (e := 19 * u * B)
        (z := cplx (FPR.sub (FPR.mul (FPR.sub x.1 y.1) s.1)
          (FPR.mul (FPR.sub x.2 y.2) (FPR.neg s.2)), FPR.add (FPR.mul (FPR.sub x.2 y.2) s.1)
          (FPR.mul (FPR.sub x.1 y.1) (FPR.neg s.2))) - (cplx x - cplx y) * (starRingEnd ℂ) (cplx s))
        (by simp only [Complex.sub_re, Complex.mul_re, Complex.conj_re, Complex.conj_im,
              Complex.sub_im, cplx_re, cplx_im]
            convert hre using 2; ring)
        (by simp only [Complex.sub_im, Complex.mul_im, Complex.conj_re, Complex.conj_im,
              Complex.sub_re, cplx_re, cplx_im]
            convert him using 2; ring)
      exact h.trans (le_of_eq (by ring))
    have htw : ‖(cplx x - cplx y) * ((starRingEnd ℂ) (cplx s) - (starRingEnd ℂ) σ)‖ ≤
        2 * B * δ := by
      rw [norm_mul, ← map_sub, Complex.norm_conj]
      exact mul_le_mul ((norm_sub_le _ _).trans (by linarith)) hδ (norm_nonneg _) (by positivity)
    calc _ = ‖(cplx (FPR.sub (FPR.mul (FPR.sub x.1 y.1) s.1)
          (FPR.mul (FPR.sub x.2 y.2) (FPR.neg s.2)), FPR.add (FPR.mul (FPR.sub x.2 y.2) s.1)
          (FPR.mul (FPR.sub x.1 y.1) (FPR.neg s.2))) -
          (cplx x - cplx y) * (starRingEnd ℂ) (cplx s)) +
          (cplx x - cplx y) * ((starRingEnd ℂ) (cplx s) - (starRingEnd ℂ) σ)‖ := by ring_nf
      _ ≤ _ := norm_add_le _ _
      _ ≤ 38 * u * B + 2 * B * δ := add_le_add hpart htw
      _ = (2 * δ + 38 * u) * B := by ring

end Falcon.Concrete.Binary64

end
