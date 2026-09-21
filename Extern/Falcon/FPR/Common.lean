/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

import all LatticeCrypto.Falcon.Concrete.FPR
import all Extern.Falcon.FPR.Rounding
public import LatticeCrypto.Falcon.Concrete.FPR
public import Extern.Falcon.FPR.Rounding

/-!
# Shared lemmas for the FPR operation proofs

Word-arithmetic and real-valued facts used by more than one of the `FPR.add`, `FPR.mul`,
`FPR.div` and `FPR.sqrt` proofs: field extraction and non-wrapping `UInt32` / `UInt64`
arithmetic, the significand-times-power-of-two reading of a normal operand, the no-carry
assembly bound, the multiplicative error-combination lemmas, and the zero-operand facts the
closure theorems share.

Keeping these here, below every operation module, is what lets the operation proofs compile in
parallel rather than in a chain.
-/

public section

namespace Falcon.Concrete.FPRBridge

open Falcon.Concrete.FPR

noncomputable section

/-- Masking an `FPR` word with `M52` computes exactly its decoded mantissa. -/
private theorem toNat_and_M52_eq_mantissa (w : FPR) :
    (w &&& M52).toNat = (FPR.decode w).mantissa := by
  have h : (w &&& M52).toNat = w.toNat % 2 ^ 52 :=
    toNat_and_one_shiftLeft_sub_one w (52 : UInt64) (by decide)
  rw [h]
  rfl

/-- Masking with the all-ones word is the identity. -/
private theorem and_allOnes_uint64 (v : UInt64) : v &&& 0xFFFFFFFFFFFFFFFF = v := by
  rw [← UInt64.toNat_inj, UInt64.toNat_and,
    show (0xFFFFFFFFFFFFFFFF : UInt64).toNat = 2 ^ 64 - 1 from by decide,
    Nat.and_two_pow_sub_one_eq_mod]
  exact Nat.mod_eq_of_lt v.toNat_lt_size

/-- Masking with the zero word annihilates. -/
private theorem and_zero_uint64 (v : UInt64) : v &&& 0 = 0 := by
  rw [← UInt64.toNat_inj, UInt64.toNat_and]
  exact Nat.and_zero _

/-- A `UInt32` right shift by `31` extracts the top bit as a quotient. -/
private theorem toNat_shiftRight_31_uint32 (w : UInt32) : (w >>> 31).toNat = w.toNat / 2 ^ 31 := by
  rw [UInt32.toNat_shiftRight, show (31 : UInt32).toNat % 32 = 31 from by decide,
    Nat.shiftRight_eq_div_pow]

/-- The magnitude of a decoded field triple's real value, in the uniform
`significand * 2 ^ (exponent - 1075)` shape (a restatement of `FPR.Bits.abs_toReal_eq` folding the
implicit leading bit into `FPR.Bits.significand`, dropping the subnormal/normal case split
entirely once `exponent ≠ 0` is known). -/
private theorem abs_toReal_eq_significand_mul_two_zpow {bx : FPR.Bits} (h0 : bx.exponent ≠ 0)
    (h2047 : bx.exponent ≠ 2047) :
    |bx.toReal| = (bx.significand : ℝ) * (2 : ℝ) ^ ((bx.exponent : ℤ) - 1075) := by
  rw [FPR.Bits.abs_toReal_eq, ite_eq_right h0, ite_eq_right h2047]
  unfold FPR.Bits.significand
  rw [ite_eq_right h0]
  push_cast
  rw [show ((bx.exponent : ℤ) - 1075) = ((bx.exponent : ℤ) - 1023) + (-52 : ℤ) by ring,
    zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
  ring

private theorem toRealBits_make_of_no_carry (s : UInt64) (e : Int32) (m : UInt64)
    (hs : s.toNat ≤ 1) (he1 : -1076 ≤ e.toInt) (he2 : e.toInt ≤ 969)
    (hm1 : 2 ^ 54 ≤ m.toNat) (hm2 : m.toNat < 2 ^ 55)
    (hnc : roundQuarterTiesEven m.toNat < 2 ^ 53) :
    toRealBits (make s e m) =
      (if s.toNat = 1 then (-1 : ℝ) else 1) * (roundQuarterTiesEven m.toNat : ℝ) *
        (2 : ℝ) ^ (e.toInt + 2) := by
  obtain ⟨hlo, hhi⟩ := roundQuarterTiesEven_mem_of_normalized m.toNat hm1 hm2
  have hE : ((e.toInt + 1076).toNat : ℤ) = e.toInt + 1076 := Int.toNat_of_nonneg (by omega)
  have hEle : (e.toInt + 1076).toNat ≤ 2045 := by omega
  rw [toRealBits, FPR.decode_make_of_no_carry s e m hs he1 he2 hm1 hm2 hnc]
  unfold FPR.Bits.toReal
  simp only [decide_eq_true_eq]
  rw [ite_eq_right (by omega : ¬ (e.toInt + 1076).toNat + 1 = 0),
    ite_eq_right (by omega : ¬ (e.toInt + 1076).toNat + 1 = 2047)]
  have hcast : (((roundQuarterTiesEven m.toNat - 2 ^ 52 : ℕ)) : ℝ) =
      (roundQuarterTiesEven m.toNat : ℝ) - 2 ^ 52 := by
    rw [Nat.cast_sub hlo]; norm_num
  have hexp : (((e.toInt + 1076).toNat + 1 : ℕ) : ℤ) - 1023 = e.toInt + 54 := by
    push_cast [hE]; ring
  rw [hcast, hexp,
    show (2 : ℝ) ^ (e.toInt + 54) = (2 : ℝ) ^ (e.toInt + 2) * 2 ^ (52 : ℕ) from by
      rw [show e.toInt + 54 = (e.toInt + 2) + (52 : ℤ) from by ring,
        zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
      norm_num]
  field_simp
  ring

private theorem abs_toRealBits_make_sub_le_of_no_carry (s : UInt64) (e : Int32) (m : UInt64)
    (hs : s.toNat ≤ 1) (he1 : -1076 ≤ e.toInt) (he2 : e.toInt ≤ 969)
    (hm1 : 2 ^ 54 ≤ m.toNat) (hm2 : m.toNat < 2 ^ 55)
    (hnc : roundQuarterTiesEven m.toNat < 2 ^ 53) :
    |toRealBits (make s e m) -
        (if s.toNat = 1 then (-1 : ℝ) else 1) * (m.toNat : ℝ) * (2 : ℝ) ^ e.toInt| ≤
      (2 : ℝ) ^ (-(53 : ℤ)) *
        |(if s.toNat = 1 then (-1 : ℝ) else 1) * (m.toNat : ℝ) * (2 : ℝ) ^ e.toInt| := by
  rw [toRealBits_make_of_no_carry s e m hs he1 he2 hm1 hm2 hnc]
  have hpe : (0 : ℝ) < (2 : ℝ) ^ e.toInt := zpow_pos (by norm_num) _
  have hsg1 : |(if s.toNat = 1 then (-1 : ℝ) else 1)| = 1 := by split_ifs <;> norm_num
  have hpow : (2 : ℝ) ^ (e.toInt + 2) = (2 : ℝ) ^ e.toInt * 4 := by
    rw [zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]; norm_num
  have hσ := abs_roundQuarterTiesEven_sub_div_four_le m.toNat
  have hm : (2 : ℝ) ^ (54 : ℕ) ≤ (m.toNat : ℝ) := by exact_mod_cast hm1
  have hc : (2 : ℝ) ^ (-(53 : ℤ)) * (2 : ℝ) ^ (54 : ℕ) = 2 := by
    rw [← zpow_natCast (2 : ℝ) 54, ← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
    norm_num
  have hcpos : (0 : ℝ) < (2 : ℝ) ^ (-(53 : ℤ)) := zpow_pos (by norm_num) _
  rw [hpow,
    show (if s.toNat = 1 then (-1 : ℝ) else 1) * (roundQuarterTiesEven m.toNat : ℝ) *
          ((2 : ℝ) ^ e.toInt * 4) -
        (if s.toNat = 1 then (-1 : ℝ) else 1) * (m.toNat : ℝ) * (2 : ℝ) ^ e.toInt =
      (if s.toNat = 1 then (-1 : ℝ) else 1) * (2 : ℝ) ^ e.toInt *
        (4 * ((roundQuarterTiesEven m.toNat : ℝ) - (m.toNat : ℝ) / 4)) from by ring]
  simp only [abs_mul, hsg1, one_mul, abs_of_pos hpe,
    abs_of_nonneg (show (0 : ℝ) ≤ (m.toNat : ℝ) by positivity),
    show |(4 : ℝ)| = 4 from by norm_num]
  have h1 : (2 : ℝ) ^ e.toInt * (4 * |(roundQuarterTiesEven m.toNat : ℝ) - (m.toNat : ℝ) / 4|) ≤
      (2 : ℝ) ^ e.toInt * 2 := by
    have : (4 : ℝ) * |(roundQuarterTiesEven m.toNat : ℝ) - (m.toNat : ℝ) / 4| ≤ 2 := by linarith
    exact mul_le_mul_of_nonneg_left this (le_of_lt hpe)
  have h2 : (2 : ℝ) ^ e.toInt * 2 ≤
      (2 : ℝ) ^ (-(53 : ℤ)) * ((m.toNat : ℝ) * (2 : ℝ) ^ e.toInt) := by
    have hstep : (2 : ℝ) ^ (-(53 : ℤ)) * (2 : ℝ) ^ (54 : ℕ) ≤
        (2 : ℝ) ^ (-(53 : ℤ)) * (m.toNat : ℝ) := mul_le_mul_of_nonneg_left hm (le_of_lt hcpos)
    rw [hc] at hstep
    nlinarith
  exact h1.trans h2

private theorem two_pow_mul_zpow (k : ℕ) (m : ℤ) :
    (2 : ℝ) ^ (k : ℕ) * (2 : ℝ) ^ m = (2 : ℝ) ^ ((k : ℤ) + m) := by
  rw [← zpow_natCast (2 : ℝ) k, ← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]

private theorem maxFiniteReal_eq :
    FPR.maxFiniteReal = (2 : ℝ) ^ (1024 : ℤ) - (2 : ℝ) ^ (971 : ℤ) := by
  unfold FPR.maxFiniteReal
  have e1 : (2 : ℝ) * (2 : ℝ) ^ (1023 : ℤ) = (2 : ℝ) ^ (1024 : ℤ) := by
    rw [show (1024 : ℤ) = 1023 + 1 from by norm_num, zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
    ring
  have e2 : (2 : ℝ) ^ (-(52 : ℤ)) * (2 : ℝ) ^ (1023 : ℤ) = (2 : ℝ) ^ (971 : ℤ) := by
    rw [← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
    norm_num
  rw [sub_mul, e1, e2]

private theorem le_stickyShift (v k : ℕ) : v / 2 ^ k ≤ stickyShift v k := by
  rw [stickyShift, Nat.shiftRight_eq_div_pow]
  split
  · rw [Nat.or_zero]
  · rw [or_one_eq]; omega

private theorem stickyShift_lt_two_pow {v k m : ℕ} (hm : 1 ≤ m) (h : v / 2 ^ k < 2 ^ m) :
    stickyShift v k < 2 ^ m := by
  rw [stickyShift, Nat.shiftRight_eq_div_pow]
  have hp : (2 : ℕ) ^ m = 2 * 2 ^ (m - 1) := by
    rw [← pow_succ']; congr 1; omega
  split
  · rw [Nat.or_zero]; exact h
  · rw [or_one_eq]; omega

private theorem stickyShift_zero (v : ℕ) : stickyShift v 0 = v := by
  rw [stickyShift]
  norm_num [Nat.mod_one]

private theorem uint32_zero_and (w : UInt32) : (0 : UInt32) &&& w = 0 := by
  rw [← UInt32.toNat_inj, UInt32.toNat_and]; simp

private theorem uint32_xor_zero (w : UInt32) : w ^^^ (0 : UInt32) = w := by
  rw [← UInt32.toNat_inj, UInt32.toNat_xor]; simp

private theorem toReal_eq_sign_mul_abs (w : FPR) (h0 : (FPR.decode w).exponent ≠ 0)
    (h2047 : (FPR.decode w).exponent ≠ 2047) :
    toReal w = (if (FPR.decode w).sign then (-1 : ℝ) else 1) * |toReal w| := by
  change (FPR.decode w).toReal = (if (FPR.decode w).sign then (-1 : ℝ) else 1)
    * |(FPR.decode w).toReal|
  rw [abs_toReal_eq_significand_mul_two_zpow h0 h2047,
    FPR.Bits.toReal_eq_of_exponent_ne_2047 _ h2047,
    show (FPR.decode w).workExp = (FPR.decode w).exponent from
      max_eq_left (by have := Nat.one_le_iff_ne_zero.mpr h0; omega),
    show ((FPR.decode w).exponent : ℤ) - 1023 - 52 = ((FPR.decode w).exponent : ℤ) - 1075 by ring]
  ring

private theorem toNat_shiftRight_63_uint64 (w : UInt64) :
    (w >>> 63).toNat = w.toNat / 2 ^ 63 := by
  rw [UInt64.toNat_shiftRight, show (63 : UInt64).toNat % 64 = 63 from by decide,
    Nat.shiftRight_eq_div_pow]

private theorem div_two_pow_63_eq_testBit (n : ℕ) (hn : n < 2 ^ 64) :
    n / 2 ^ 63 = if n.testBit 63 then 1 else 0 := by
  rw [Nat.testBit_eq_decide_div_mod_eq]
  have h2 : n / 2 ^ 63 < 2 := by omega
  interval_cases h : (n / 2 ^ 63) <;> simp_all

/-- The sign word `(x ^^^ y) >>> 63` that `FPR.mul` and `FPR.div` both compute is the
exclusive-or of the two operands' sign bits. -/
private theorem signWord_toNat (x y : FPR) :
    ((x ^^^ y) >>> 63).toNat
      = if xor (FPR.decode x).sign (FPR.decode y).sign then 1 else 0 := by
  rw [toNat_shiftRight_63_uint64, UInt64.toNat_xor,
    div_two_pow_63_eq_testBit _ (Nat.xor_lt_two_pow x.toNat_lt_size y.toNat_lt_size),
    Nat.testBit_xor]
  rfl

private theorem mul_scale_lt {W absQ S : ℝ} (hW1 : (2 : ℝ) ^ (54 : ℕ) ≤ W)
    (h1 : (W - 1) * S < absQ)
    (hhi : absQ ≤ (2 : ℝ) ^ (1024 : ℤ) - (2 : ℝ) ^ (971 : ℤ)) : S < (2 : ℝ) ^ (970 : ℤ) := by
  by_contra hc
  push Not at hc
  set t : ℝ := (2 : ℝ) ^ (970 : ℤ) with ht
  have htpos : 0 < t := zpow_pos (by norm_num) _
  have e1 : (2 : ℝ) ^ (1024 : ℤ) = (2 : ℝ) ^ (54 : ℕ) * t := by
    rw [ht, two_pow_mul_zpow]; norm_num
  have e2 : (2 : ℝ) ^ (971 : ℤ) = 2 * t := by
    rw [ht, show (971 : ℤ) = 1 + 970 from by norm_num,
      zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
    norm_num
  clear_value t
  clear ht
  have hWS : ((2 : ℝ) ^ (54 : ℕ) - 1) * t ≤ (W - 1) * S := by
    have h2 : (0 : ℝ) ≤ (2 : ℝ) ^ (54 : ℕ) - 1 := by norm_num
    exact mul_le_mul (by linarith) hc htpos.le (by linarith)
  rw [e1, e2] at hhi
  rw [show ((2 : ℝ) ^ (54 : ℕ) - 1) * t = (2 : ℝ) ^ (54 : ℕ) * t - t from by ring] at hWS
  norm_num at hhi hWS
  clear e1 e2
  have h3 : (W - 1) * S < 18014398509481984 * t - 2 * t := lt_of_lt_of_le h1 hhi
  linarith

private theorem mul_scale_gt {W absQ S : ℝ} (hW2 : W ≤ (2 : ℝ) ^ (55 : ℕ) - 1)
    (h2 : absQ < (W + 1) * S) (hS : 0 < S)
    (hlo : (2 : ℝ) ^ (-(1022 : ℤ)) ≤ absQ) : (2 : ℝ) ^ (-(1077 : ℤ)) < S := by
  by_contra hc
  push Not at hc
  set t : ℝ := (2 : ℝ) ^ (-(1077 : ℤ)) with ht
  have htpos : 0 < t := zpow_pos (by norm_num) _
  have e1 : (2 : ℝ) ^ (-(1022 : ℤ)) = (2 : ℝ) ^ (55 : ℕ) * t := by
    rw [ht, two_pow_mul_zpow]; norm_num
  clear_value t
  clear ht
  have hWS : (W + 1) * S ≤ (2 : ℝ) ^ (55 : ℕ) * t :=
    mul_le_mul (by linarith) hc hS.le (by norm_num)
  rw [e1] at hlo
  clear e1
  norm_num at hlo hWS
  linarith

private theorem mul_error_combine {M W P K c σ : ℝ}
    (hσ : σ = 1 ∨ σ = -1) (hc : 0 < c) (hW : 0 ≤ W) (hK : 0 < K)
    (hMV : |M - σ * (W * K * c)| ≤ (2 : ℝ) ^ (-(53 : ℤ)) * |σ * (W * K * c)|)
    (hbr1 : (W - 1) * K < P) (hbr2 : P < (W + 1) * K)
    (hkey : (2 : ℝ) ^ (53 : ℕ) * K + K ≤ P) :
    |M - σ * (P * c)| ≤ (2 : ℝ) ^ (-(52 : ℤ)) * |σ * (P * c)| := by
  have hP : 0 < P := by nlinarith
  have hσabs : |σ| = 1 := by rcases hσ with rfl | rfl <;> norm_num
  have habsV : |σ * (W * K * c)| = W * K * c := by
    rw [abs_mul, hσabs, one_mul, abs_of_nonneg (by positivity)]
  have habsQ : |σ * (P * c)| = P * c := by
    rw [abs_mul, hσabs, one_mul, abs_of_nonneg (by positivity)]
  rw [habsV] at hMV
  rw [habsQ]
  have hgap : |σ * (W * K * c) - σ * (P * c)| = |W * K - P| * c := by
    rw [show σ * (W * K * c) - σ * (P * c) = σ * ((W * K - P) * c) by ring, abs_mul, hσabs,
      one_mul, abs_mul, abs_of_pos hc]
  have hWP : |W * K - P| ≤ K := by
    rw [abs_le]; constructor <;> nlinarith
  have hstep : |M - σ * (P * c)| ≤ ((2 : ℝ) ^ (-(53 : ℤ)) * (W * K) + K) * c := by
    calc |M - σ * (P * c)| ≤ |M - σ * (W * K * c)| + |σ * (W * K * c) - σ * (P * c)| :=
          abs_sub_le _ _ _
      _ ≤ (2 : ℝ) ^ (-(53 : ℤ)) * (W * K * c) + |W * K - P| * c := by rw [hgap]; linarith
      _ ≤ ((2 : ℝ) ^ (-(53 : ℤ)) * (W * K) + K) * c := by nlinarith
  rw [show (2 : ℝ) ^ (-(52 : ℤ)) * (P * c) = ((2 : ℝ) ^ (-(52 : ℤ)) * P) * c from by ring]
  refine hstep.trans (mul_le_mul_of_nonneg_right ?_ hc.le)
  have ht : (0 : ℝ) < (2 : ℝ) ^ (-(53 : ℤ)) := zpow_pos (by norm_num) _
  have ht53 : (2 : ℝ) ^ (-(53 : ℤ)) * (2 : ℝ) ^ (53 : ℕ) = 1 := by
    rw [← zpow_natCast (2 : ℝ) 53, ← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]; norm_num
  have h52 : (2 : ℝ) ^ (-(52 : ℤ)) = 2 * (2 : ℝ) ^ (-(53 : ℤ)) := by
    rw [show (-(52 : ℤ)) = 1 + (-(53 : ℤ)) from by norm_num,
      zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
    norm_num
  rw [h52]
  have hWK : W * K < P + K := by nlinarith
  have hKP : (2 : ℝ) ^ (-(53 : ℤ)) * K + K ≤ (2 : ℝ) ^ (-(53 : ℤ)) * P := by
    have := mul_le_mul_of_nonneg_left hkey ht.le
    calc (2 : ℝ) ^ (-(53 : ℤ)) * K + K
        = (2 : ℝ) ^ (-(53 : ℤ)) * ((2 : ℝ) ^ (53 : ℕ) * K + K) := by
          rw [mul_add, ← mul_assoc, ht53, one_mul]; ring
      _ ≤ (2 : ℝ) ^ (-(53 : ℤ)) * P := this
  nlinarith

private theorem toReal_ne_zero_of_isNormal {w : FPR} (h : FPR.IsNormal w) : toReal w ≠ 0 := by
  intro hz
  have habs : |toReal w| = ((FPR.decode w).significand : ℝ)
      * (2 : ℝ) ^ (((FPR.decode w).exponent : ℤ) - 1075) := by
    change |(FPR.decode w).toReal| = _
    exact abs_toReal_eq_significand_mul_two_zpow h.1 h.2
  rw [hz, abs_zero] at habs
  have hsig : (2 : ℝ) ^ (52 : ℕ) ≤ ((FPR.decode w).significand : ℝ) := by
    have : (2 : ℕ) ^ 52 ≤ (FPR.decode w).significand := by
      unfold FPR.Bits.significand; rw [ite_eq_right h.1]; omega
    exact_mod_cast this
  have hp : (0 : ℝ) < (2 : ℝ) ^ (((FPR.decode w).exponent : ℤ) - 1075) := zpow_pos (by norm_num) _
  nlinarith

/-! ## Widening to the operand domain binary64 is closed under

Every bound above assumes `FPR.IsNormal` operands, while the domain the arithmetic is actually
closed under is `FPR.IsNormalOrZero` (`add_isNormalOrZero_of_isNormal` and friends can return the
zero encodings, and Falcon feeds exact zeros constantly). This section closes the gap.

The zero cases are exact rather than approximate, so no new error analysis is involved — what
they need is each pipeline traced at an operand whose exponent field is `0`:

* `FPR.add` reassembles the other operand unchanged. Nothing is aligned in (`yu` vanishes), the
  renormalising count is forced to `8`, and the nine-bit sticky fold divides exactly, so the
  packing round-trips. This is `add_decode_eq_of_significand_eq_zero`, stated on the pipeline's
  ordered `x'` so that one trace covers both argument orders.
* `FPR.mul` and `FPR.div` carry an explicit flush guard (`dzu`) that fires on a zero exponent
  field, clearing the significand *and* substituting the exponent `-1076`, which `make` packs as
  a bare sign bit.
* `FPR.sqrt` masks its significand against the same test, and `make_z` collapses on it.

Note `FPR.add` is not bit-preserving here — `(+0) + (-0)` is `+0` — so the statements are phrased
on `toReal` and on the decoded fields, never on the bit pattern.
-/

/-- A zero encoding has empty significand. -/
private theorem significand_eq_zero_of_isZero {x : FPR} (h : FPR.IsZero x) :
    (FPR.decode x).significand = 0 := by
  unfold FPR.Bits.significand
  rw [h.1, h.2]; simp

private theorem magKey_eq_zero_of_isZero {x : FPR} (h : FPR.IsZero x) :
    (FPR.decode x).magKey = 0 := by
  unfold FPR.Bits.magKey; rw [h.1, h.2]; simp

private theorem two_pow_le_magKey_of_isNormal {x : FPR} (h : FPR.IsNormal x) :
    2 ^ 52 ≤ (FPR.decode x).magKey := by
  unfold FPR.Bits.magKey
  have : 1 ≤ (FPR.decode x).exponent := Nat.one_le_iff_ne_zero.mpr h.1
  nlinarith [Nat.zero_le (FPR.decode x).mantissa]

/-- Both zero encodings denote `0`. -/
private theorem toReal_eq_zero_of_isZero {x : FPR} (h : FPR.IsZero x) : toReal x = 0 := by
  change (FPR.decode x).toReal = 0
  unfold FPR.Bits.toReal
  rw [ite_eq_left h.1, h.2]
  simp

/-- Equal decoded fields denote equal reals. -/
private theorem toReal_eq_of_decode_eq {x y : FPR} (h : FPR.decode x = FPR.decode y) :
    toReal x = toReal y := by
  change (FPR.decode x).toReal = (FPR.decode y).toReal
  rw [h]

/-- `FPR.make` on the flushed exponent that `FPR.mul` and `FPR.div` substitute for a zero
operand: `e + 1076` is `0` and the significand is empty, so nothing but the sign bit survives. -/
private theorem make_flushed (s : UInt64) :
    make s (((0 : UInt32) - 1076).toInt32) 0 = s <<< 63 := by
  have h1 : (((((0 : UInt32) - 1076).toInt32 + 1076).toUInt32.toUInt64) <<< 52 : UInt64) = 0 := by
    decide
  have h2 : (((0xC8 : UInt64) >>> ((0 : UInt64).toUInt32 &&& (7 : UInt32)).toUInt64)
      &&& (1 : UInt64)) = 0 := by decide
  change (s <<< 63) + (((((0 : UInt32) - 1076).toInt32 + 1076).toUInt32.toUInt64) <<< 52)
      + ((0 : UInt64) >>> 2)
      + (((0xC8 : UInt64) >>> ((0 : UInt64).toUInt32 &&& (7 : UInt32)).toUInt64)
        &&& (1 : UInt64)) = s <<< 63
  rw [h1, h2, show ((0 : UInt64) >>> 2) = 0 from by decide]
  simp

/-- Decode of a bare sign bit: the IEEE-754 signed zero. -/
private theorem decode_shiftLeft_63 (s : UInt64) (hs : s.toNat ≤ 1) :
    FPR.decode (s <<< 63) = { sign := decide (s.toNat = 1), exponent := 0, mantissa := 0 } := by
  rw [← make_z_of_zero s 0]
  exact FPR.decode_make_z_of_zero s 0 hs

/-- A wrapping `UInt32` decrement of `0` is the all-ones word. -/
private theorem uint32_zero_sub_one_toNat : ((0 : UInt32) - 1).toNat = 2 ^ 32 - 1 := by decide

/-- Masking a `UInt32` with the all-ones word is the identity. -/
private theorem uint32_allOnes_and (w : UInt32) : (0xFFFFFFFF : UInt32) &&& w = w := by
  have hsize : (UInt32.size : Nat) = 2 ^ 32 := by decide
  have hlt := w.toNat_lt_size
  rw [← UInt32.toNat_inj, UInt32.toNat_and,
    show (0xFFFFFFFF : UInt32).toNat = 2 ^ 32 - 1 from by decide, Nat.and_comm,
    Nat.and_two_pow_sub_one_eq_mod]
  omega

/-- The `+0` word is a zero encoding. -/
private theorem isZero_zero : FPR.IsZero (0 : FPR) := by
  unfold FPR.IsZero FPR.Bits.IsZero FPR.decode; exact ⟨rfl, rfl⟩

/-- The `FPR` constant `0` is in the closure domain (in its zero disjunct). -/
theorem FPR.isNormalOrZero_zero : FPR.IsNormalOrZero FPR.zero :=
  Or.inr (by unfold FPR.IsZero FPR.Bits.IsZero FPR.decode FPR.zero; decide)

/-- The `FPR` constant `1` is in the closure domain (in its normal disjunct). -/
theorem FPR.isNormalOrZero_one : FPR.IsNormalOrZero FPR.one :=
  Or.inl (by unfold FPR.IsNormal FPR.Bits.IsNormal FPR.decode FPR.one; decide)

end

end Falcon.Concrete.FPRBridge
