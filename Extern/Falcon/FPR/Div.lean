/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

import all LatticeCrypto.Falcon.Concrete.FPR
import all Extern.Falcon.FPR.Loop
public import LatticeCrypto.Falcon.Concrete.FPR
public import Extern.Falcon.FPR.Loop

/-!
# Correct rounding of `FPR.div`

The restoring-division loop's invariant, the renormalisation step and the real-valued quotient
bracket, giving `div_error` and the closure fact `div_isNormalOrZero`.
-/

public section

namespace Falcon.Concrete.FPRBridge

open Falcon.Concrete.FPR

noncomputable section

/-! ## Trading the `FPR.div` / `FPR.sqrt` loops for induction

Unlike `FPR.add` and `FPR.mul`, these two kernels are not straight-line: each runs a fixed-length
`for _ in [0:n]` loop over a mutable state. Neither body reads the loop index, so the fold is
iteration of a single step function, and an invariant of the state becomes ordinary induction on
the step count. The pipeline records below name the loop's result as a field, pinned to the kernel
term by `rfl` exactly as `addPipeline` and `mulPipeline` are; `divPipeline_loop_induction` and
`sqrtPipeline_loop_induction` are the entry points for reasoning about what the loops compute. -/

/-- One iteration of `FPR.div`'s restoring-division loop, over the state `(q, x)`. -/
private def divStep (yu : UInt64) (s : UInt64 × UInt64) : UInt64 × UInt64 :=
  let q_ := s.1
  let xu_ := s.2
  let b := (xu_ - yu) >>> 63 - 1
  let xu_ := xu_ - (b &&& yu)
  let q_ := q_ ||| b &&& 1
  let xu_ := xu_ <<< 1
  let q_ := q_ <<< 1
  (q_, xu_)

private structure DivPipeline where
  /-- The extended significand of the numerator. -/
  xu : UInt64
  /-- The extended significand of the divisor. -/
  yu : UInt64
  /-- The state `(q, x)` left by the restoring-division loop. -/
  loopRes : UInt64 × UInt64
  /-- The quotient with its final sticky bit folded in. -/
  q0 : UInt64
  /-- The renormalising right-shift count. -/
  es : UInt64
  /-- The renormalised quotient handed to `make`. -/
  q1 : UInt64
  ex : UInt32
  ey : UInt32
  e : UInt32
  sg : UInt64
  /-- All-ones when the numerator's exponent field is zero (the flush-to-zero guard). -/
  dzu : UInt32
  e' : Int32
  dm : UInt64

private def divPipeline (x y : FPR) : DivPipeline :=
  let xu : UInt64 := (x &&& M52) ||| ((1 : UInt64) <<< 52)
  let yu : UInt64 := (y &&& M52) ||| ((1 : UInt64) <<< 52)
  let loopRes : UInt64 × UInt64 :=
    (forIn [0:55] ((0 : UInt64), xu) (fun _ s => pure (ForInStep.yield (divStep yu s)))
      : Id (UInt64 × UInt64))
  let q0 := loopRes.1 ||| ((loopRes.2 ||| (0 - loopRes.2)) >>> 63)
  let es := q0 >>> 55
  let q1 := (q0 >>> es) ||| (q0 &&& 1)
  let ex := (x >>> 52).toUInt32 &&& 0x7FF
  let ey := (y >>> 52).toUInt32 &&& 0x7FF
  let e := ex - ey - 55 + es.toUInt32
  let sg := (x ^^^ y) >>> 63
  let dzu := tbmask (ex - 1)
  let e' : Int32 := (e ^^^ (dzu &&& (e ^^^ ((0 : UInt32) - 1076)))).toInt32
  let dm := (dzu &&& 1).toUInt64 - 1
  { xu, yu, loopRes, q0, es, q1, ex, ey, e, sg, dzu, e', dm }

/-- `FPR.div` is the final assembly call `make` over three fields of `divPipeline`. -/
private theorem div_eq_make (x y : FPR) :
    FPR.div x y =
      make ((divPipeline x y).sg &&& (divPipeline x y).dm) (divPipeline x y).e'
        ((divPipeline x y).q1 &&& (divPipeline x y).dm) :=
  rfl

/-- The loop field is exactly `55` iterations of `divStep`: this is where the `for` loop is
traded for an induction principle. -/
private theorem divPipeline_loopRes (x y : FPR) :
    (divPipeline x y).loopRes
      = (divStep ((y &&& M52) ||| ((1 : UInt64) <<< 52)))^[55]
          (0, (x &&& M52) ||| ((1 : UInt64) <<< 52)) :=
  forIn_range_eq_iterate _ _ _

private theorem divPipeline_xu (x y : FPR) :
    (divPipeline x y).xu = (x &&& M52) ||| ((1 : UInt64) <<< 52) := rfl

private theorem divPipeline_yu (x y : FPR) :
    (divPipeline x y).yu = (y &&& M52) ||| ((1 : UInt64) <<< 52) := rfl

/-- Induction over `FPR.div`'s loop: prove an invariant of the state `(q, x)` holds initially and
is preserved by one restoring-division step, and it holds of the state the loop leaves. -/
private theorem divPipeline_loop_induction (x y : FPR)
    (P : ℕ → UInt64 × UInt64 → Prop)
    (h0 : P 0 (0, (x &&& M52) ||| ((1 : UInt64) <<< 52)))
    (hstep : ∀ k s, P k s → P (k + 1) (divStep ((y &&& M52) ||| ((1 : UInt64) <<< 52)) s)) :
    P 55 (divPipeline x y).loopRes := by
  rw [divPipeline_loopRes]
  induction 55 with
  | zero => exact h0
  | succ k ih => rw [Function.iterate_succ_apply']; exact hstep k _ ih

/-- Induction over `FPR.sqrt`'s loop. -/
private theorem sqrtPipeline_loop_induction (x : FPR)
    (P : ℕ → UInt64 × UInt64 × UInt64 × UInt64 → Prop)
    (h0 : P 0 ((sqrtPipeline x).xu <<< 1, 0, 0, (1 : UInt64) <<< 53))
    (hstep : ∀ k v, P k v → P (k + 1) (sqrtStep v)) :
    P 54 (sqrtPipeline x).loopRes := by
  rw [sqrtPipeline_loopRes]
  induction 54 with
  | zero => exact h0
  | succ k ih => rw [Function.iterate_succ_apply']; exact hstep k _ ih

/-! ### What one restoring-division step does -/

/-- The division loop's comparison mask: all-ones exactly when the running remainder is at least
the divisor, zero otherwise. -/
private theorem divStep_mask (r yu : UInt64) (hr : r.toNat < 2 ^ 54) (hy : yu.toNat < 2 ^ 53) :
    ((r - yu) >>> 63) - 1 = if yu.toNat ≤ r.toNat then (0 : UInt64) - 1 else 0 :=
  sub_mask_of_lt r yu (by omega) (by omega)

/-- One restoring-division step, read as arithmetic: conditionally subtract the divisor, append
the quotient bit, then double both. -/
private theorem divStep_toNat (yu : UInt64) (s : UInt64 × UInt64)
    (hy : yu.toNat < 2 ^ 53) (hr : s.2.toNat < 2 * yu.toNat)
    (hq : s.1.toNat < 2 ^ 62) (hqe : s.1.toNat % 2 = 0) :
    (divStep yu s).1.toNat = 2 * (s.1.toNat + (if yu.toNat ≤ s.2.toNat then 1 else 0))
      ∧ (divStep yu s).2.toNat
        = 2 * (s.2.toNat - (if yu.toNat ≤ s.2.toNat then yu.toNat else 0)) := by
  simp only [divStep]
  rw [divStep_mask _ _ (by omega) hy]
  by_cases h : yu.toNat ≤ s.2.toNat
  · rw [ite_eq_left h]
    have hand : ((0 : UInt64) - 1) &&& yu = yu := allOnes_and yu
    have hand1 : ((0 : UInt64) - 1) &&& 1 = 1 := by decide
    rw [hand, hand1]
    have hsub : (s.2 - yu).toNat = s.2.toNat - yu.toNat := toNat_sub_of_le_uint64 _ _ h
    have hor : (s.1 ||| 1).toNat = s.1.toNat + 1 := by
      rw [UInt64.toNat_or, show (1 : UInt64).toNat = 1 from rfl, or_one_eq]; omega
    refine ⟨?_, ?_⟩
    · rw [toNat_shiftLeft_one, hor, ite_eq_left h]
      have : (s.1.toNat + 1) * 2 < 2 ^ 64 := by omega
      omega
    · rw [toNat_shiftLeft_one, hsub, ite_eq_left h]
      have : (s.2.toNat - yu.toNat) * 2 < 2 ^ 64 := by omega
      omega
  · rw [ite_eq_right h]
    push Not at h
    rw [uint64_zero_and, uint64_zero_and]
    have hsub : (s.2 - 0).toNat = s.2.toNat := by simp
    have hor : (s.1 ||| 0).toNat = s.1.toNat := by rw [UInt64.toNat_or]; simp
    refine ⟨?_, ?_⟩
    · rw [toNat_shiftLeft_one, hor, ite_eq_right (by omega)]
      have : s.1.toNat * 2 < 2 ^ 64 := by omega
      omega
    · rw [toNat_shiftLeft_one, hsub, ite_eq_right (by omega)]
      have : s.2.toNat * 2 < 2 ^ 64 := by omega
      omega

/-! ### What the whole division loop computes

The loop is exact restoring division: after `n` steps the running remainder and the quotient
satisfy `yu * q + r = 2 ^ n * xu`, with `r` held below `2 * yu`. At `n = 55` this pins the
quotient `FPR.div` hands to its sticky and renormalisation steps. -/

private theorem divLoop_invariant (xu yu : UInt64)
    (hx : xu.toNat < 2 ^ 53) (hy1 : 2 ^ 52 ≤ yu.toNat) (hy2 : yu.toNat < 2 ^ 53) :
    ∀ n : ℕ, n ≤ 60 →
    yu.toNat * ((divStep yu)^[n] (0, xu)).1.toNat + ((divStep yu)^[n] (0, xu)).2.toNat
        = 2 ^ n * xu.toNat
      ∧ ((divStep yu)^[n] (0, xu)).2.toNat < 2 * yu.toNat
      ∧ ((divStep yu)^[n] (0, xu)).1.toNat < 2 ^ (n + 1)
      ∧ ((divStep yu)^[n] (0, xu)).1.toNat % 2 = 0 := by
  intro n
  induction n with
  | zero =>
    intro _
    simp only [Function.iterate_zero, id_eq]
    exact ⟨by simp, by simpa using (show xu.toNat < 2 * yu.toNat by omega), by simp, by simp⟩
  | succ k ih =>
    intro hk
    obtain ⟨hinv, hrem, hqlt, hqe⟩ := ih (by omega)
    have hq62 : ((divStep yu)^[k] (0, xu)).1.toNat < 2 ^ 62 := by
      have : (2 : ℕ) ^ (k + 1) ≤ 2 ^ 61 := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    rw [Function.iterate_succ_apply']
    obtain ⟨hq', hr'⟩ := divStep_toNat yu ((divStep yu)^[k] (0, xu)) hy2 hrem hq62 hqe
    set q := ((divStep yu)^[k] (0, xu)).1.toNat with hqdef
    set r := ((divStep yu)^[k] (0, xu)).2.toNat with hrdef
    have hpow : (2 : ℕ) ^ (k + 1) * xu.toNat = 2 * (2 ^ k * xu.toNat) := by ring
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [hq', hr', hpow]
      by_cases h : yu.toNat ≤ r
      · rw [ite_eq_left h, ite_eq_left h,
          show yu.toNat * (2 * (q + 1)) = 2 * (yu.toNat * q) + 2 * yu.toNat from by ring]
        omega
      · rw [ite_eq_right h, ite_eq_right h,
          show yu.toNat * (2 * (q + 0)) = 2 * (yu.toNat * q) from by ring]
        omega
    · rw [hr']
      by_cases h : yu.toNat ≤ r
      · rw [ite_eq_left h]; omega
      · rw [ite_eq_right h]; omega
    · rw [hq']
      have hp : (2 : ℕ) ^ (k + 1 + 1) = 2 * 2 ^ (k + 1) := by ring
      by_cases h : yu.toNat ≤ r
      · rw [ite_eq_left h, hp]; omega
      · rw [ite_eq_right h, hp]; omega
    · rw [hq']; omega

/-- The invariant, read off `FPR.div`'s pipeline. -/
private theorem divPipeline_loop_invariant (x y : FPR) :
    (divPipeline x y).yu.toNat * (divPipeline x y).loopRes.1.toNat
        + (divPipeline x y).loopRes.2.toNat
      = 2 ^ 55 * (divPipeline x y).xu.toNat
    ∧ (divPipeline x y).loopRes.2.toNat < 2 * (divPipeline x y).yu.toNat
    ∧ (divPipeline x y).loopRes.1.toNat < 2 ^ 56
    ∧ (divPipeline x y).loopRes.1.toNat % 2 = 0 := by
  have hxu : ((x &&& M52) ||| ((1 : UInt64) <<< 52)).toNat = (FPR.decode x).mantissa + 2 ^ 52 :=
    significand_pack_toNat x
  have hyu : ((y &&& M52) ||| ((1 : UInt64) <<< 52)).toNat = (FPR.decode y).mantissa + 2 ^ 52 :=
    significand_pack_toNat y
  have hmx := FPR.decode_mantissa_lt x
  have hmy := FPR.decode_mantissa_lt y
  have h := divLoop_invariant ((x &&& M52) ||| ((1 : UInt64) <<< 52))
    ((y &&& M52) ||| ((1 : UInt64) <<< 52)) (by omega) (by omega) (by omega) 55 (by norm_num)
  rw [divPipeline_xu, divPipeline_yu, divPipeline_loopRes]
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2⟩

/-- The quotient word `FPR.div` hands to its renormalisation step: the loop's quotient with a
sticky bit recording whether the division was inexact. -/
private theorem divPipeline_q0_toNat (x y : FPR) :
    (divPipeline x y).q0.toNat
      = (divPipeline x y).loopRes.1.toNat
        + (if (divPipeline x y).loopRes.2.toNat = 0 then 0 else 1) := by
  have hqe := (divPipeline_loop_invariant x y).2.2.2
  change ((divPipeline x y).loopRes.1 |||
    (((divPipeline x y).loopRes.2 ||| (0 - (divPipeline x y).loopRes.2)) >>> 63)).toNat = _
  rw [or_bit_of_even hqe (by rw [or_neg_shiftRight_63]; split <;> omega),
    or_neg_shiftRight_63]

/-- One unit in the last place is all the division loop plus its sticky bit can be off by: the
quotient word brackets the exact `2 ^ 55 * xu / yu` from both sides. -/
private theorem divPipeline_q0_bracket (x y : FPR) :
    (divPipeline x y).q0.toNat * (divPipeline x y).yu.toNat
        < 2 ^ 55 * (divPipeline x y).xu.toNat + (divPipeline x y).yu.toNat
      ∧ 2 ^ 55 * (divPipeline x y).xu.toNat
        < (divPipeline x y).q0.toNat * (divPipeline x y).yu.toNat
          + (divPipeline x y).yu.toNat := by
  obtain ⟨hinv, hrem, -, -⟩ := divPipeline_loop_invariant x y
  have hq0 := divPipeline_q0_toNat x y
  have hyu : (divPipeline x y).yu.toNat = (FPR.decode y).mantissa + 2 ^ 52 := by
    rw [divPipeline_yu]; exact significand_pack_toNat y
  have hypos : 0 < (divPipeline x y).yu.toNat := by omega
  rw [hq0]
  by_cases h : (divPipeline x y).loopRes.2.toNat = 0
  · rw [ite_eq_left h, add_zero,
      show (divPipeline x y).loopRes.1.toNat * (divPipeline x y).yu.toNat
        = (divPipeline x y).yu.toNat * (divPipeline x y).loopRes.1.toNat from by ring]
    omega
  · rw [ite_eq_right h,
      show ((divPipeline x y).loopRes.1.toNat + 1) * (divPipeline x y).yu.toNat
        = (divPipeline x y).yu.toNat * (divPipeline x y).loopRes.1.toNat
          + (divPipeline x y).yu.toNat from by ring]
    omega

/-- A one-bit sticky shift moves the value by at most one unit — sharper than the generic
`stickyShift_mul_lt` / `lt_stickyShift_mul_add` pair, which would allow two. This sharpness is
what keeps `FPR.div`'s renormalisation inside the error budget. -/
private theorem stickyShift_one_bracket (v : ℕ) :
    stickyShift v 1 * 2 ≤ v + 1 ∧ v ≤ stickyShift v 1 * 2 + 1 := by
  rw [stickyShift_eq v 1]
  have h4 : v % 4 < 4 := Nat.mod_lt _ (by norm_num)
  have hd : v = 4 * (v / 2 ^ (1 + 1)) + v % 4 := by
    rw [show (2 : ℕ) ^ (1 + 1) = 4 from by norm_num]; omega
  by_cases h : v % 2 ^ (1 + 1) = 0
  · rw [ite_eq_left h]
    rw [show (2 : ℕ) ^ (1 + 1) = 4 from by norm_num] at h
    omega
  · rw [ite_eq_right h]
    rw [show (2 : ℕ) ^ (1 + 1) = 4 from by norm_num] at h
    omega

/-! ### The renormalisation step -/

private theorem divPipeline_q0_lt (x y : FPR) : (divPipeline x y).q0.toNat < 2 ^ 56 := by
  obtain ⟨-, -, hqlt, hqe⟩ := divPipeline_loop_invariant x y
  have h := divPipeline_q0_toNat x y
  rw [h]; split <;> omega

private theorem divPipeline_le_q0 (x y : FPR) : 2 ^ 54 ≤ (divPipeline x y).q0.toNat := by
  obtain ⟨-, hbr⟩ := divPipeline_q0_bracket x y
  have hxu : (divPipeline x y).xu.toNat = (FPR.decode x).mantissa + 2 ^ 52 := by
    rw [divPipeline_xu]; exact significand_pack_toNat x
  have hyu : (divPipeline x y).yu.toNat = (FPR.decode y).mantissa + 2 ^ 52 := by
    rw [divPipeline_yu]; exact significand_pack_toNat y
  have hmx := FPR.decode_mantissa_lt x
  have hmy := FPR.decode_mantissa_lt y
  by_contra hc
  push Not at hc
  have h1 : (2 : ℕ) ^ 107 ≤ 2 ^ 55 * (divPipeline x y).xu.toNat := by
    calc (2 : ℕ) ^ 107 = 2 ^ 55 * 2 ^ 52 := by norm_num
      _ ≤ 2 ^ 55 * (divPipeline x y).xu.toNat := Nat.mul_le_mul_left _ (by omega)
  have hprod : (divPipeline x y).q0.toNat * (divPipeline x y).yu.toNat
      ≤ (2 ^ 54 - 1) * (2 ^ 53 - 1) := Nat.mul_le_mul (by omega) (by omega)
  norm_num at hprod h1
  omega

private theorem divPipeline_es_toNat (x y : FPR) :
    (divPipeline x y).es.toNat = (divPipeline x y).q0.toNat / 2 ^ 55 := by
  change ((divPipeline x y).q0 >>> 55).toNat = _
  rw [UInt64.toNat_shiftRight, show (55 : UInt64).toNat % 64 = 55 from by decide,
    Nat.shiftRight_eq_div_pow]

private theorem divPipeline_es_le_one (x y : FPR) : (divPipeline x y).es.toNat ≤ 1 := by
  rw [divPipeline_es_toNat]
  have := divPipeline_q0_lt x y
  omega

private theorem divPipeline_q1_toNat (x y : FPR) :
    (divPipeline x y).q1.toNat
      = stickyShift (divPipeline x y).q0.toNat (divPipeline x y).es.toNat := by
  change (((divPipeline x y).q0 >>> (divPipeline x y).es) ||| ((divPipeline x y).q0 &&& 1)).toNat
    = _
  exact toNat_shiftRight_or_and_one _ _ (divPipeline_es_le_one x y)

/-- The renormalised quotient lands in the window `FPR.make`'s rounding analysis needs. -/
private theorem divPipeline_q1_mem (x y : FPR) :
    2 ^ 54 ≤ (divPipeline x y).q1.toNat ∧ (divPipeline x y).q1.toNat < 2 ^ 55 := by
  have hes := divPipeline_es_le_one x y
  have hlo := divPipeline_le_q0 x y
  have hhi := divPipeline_q0_lt x y
  have hsr := divPipeline_es_toNat x y
  rw [divPipeline_q1_toNat]
  interval_cases h : (divPipeline x y).es.toNat
  · rw [stickyShift_zero]
    omega
  · refine ⟨le_trans ?_ (le_stickyShift _ _), stickyShift_lt_two_pow (by norm_num) ?_⟩ <;>
      · simp only [pow_one]; omega

/-- The renormalised quotient still brackets the exact value to one unit in *its* last place.
The one-bit sticky shift is what keeps this at one unit rather than two. -/
private theorem divPipeline_q1_bracket (x y : FPR) :
    (divPipeline x y).q1.toNat * 2 ^ (divPipeline x y).es.toNat * (divPipeline x y).yu.toNat
        < 2 ^ 55 * (divPipeline x y).xu.toNat
          + 2 ^ (divPipeline x y).es.toNat * (divPipeline x y).yu.toNat
      ∧ 2 ^ 55 * (divPipeline x y).xu.toNat
        < (divPipeline x y).q1.toNat * 2 ^ (divPipeline x y).es.toNat
            * (divPipeline x y).yu.toNat
          + 2 ^ (divPipeline x y).es.toNat * (divPipeline x y).yu.toNat := by
  obtain ⟨hb1, hb2⟩ := divPipeline_q0_bracket x y
  have hes := divPipeline_es_le_one x y
  have hq1 := divPipeline_q1_toNat x y
  interval_cases h : (divPipeline x y).es.toNat
  · rw [hq1, stickyShift_zero]; simpa using ⟨hb1, hb2⟩
  · have hsb := stickyShift_one_bracket (divPipeline x y).q0.toNat
    have hmul1 : stickyShift (divPipeline x y).q0.toNat 1 * 2 * (divPipeline x y).yu.toNat
        ≤ ((divPipeline x y).q0.toNat + 1) * (divPipeline x y).yu.toNat :=
      Nat.mul_le_mul_right _ hsb.1
    have hmul2 : (divPipeline x y).q0.toNat * (divPipeline x y).yu.toNat
        ≤ (stickyShift (divPipeline x y).q0.toNat 1 * 2 + 1) * (divPipeline x y).yu.toNat :=
      Nat.mul_le_mul_right _ hsb.2
    rw [add_mul, one_mul] at hmul1 hmul2
    rw [hq1]
    simp only [pow_one]
    constructor
    · calc stickyShift (divPipeline x y).q0.toNat 1 * 2 * (divPipeline x y).yu.toNat
          ≤ (divPipeline x y).q0.toNat * (divPipeline x y).yu.toNat
            + (divPipeline x y).yu.toNat := hmul1
        _ < 2 ^ 55 * (divPipeline x y).xu.toNat + 2 * (divPipeline x y).yu.toNat := by omega
    · calc 2 ^ 55 * (divPipeline x y).xu.toNat
          < (divPipeline x y).q0.toNat * (divPipeline x y).yu.toNat
            + (divPipeline x y).yu.toNat := hb2
        _ ≤ stickyShift (divPipeline x y).q0.toNat 1 * 2 * (divPipeline x y).yu.toNat
            + 2 * (divPipeline x y).yu.toNat := by omega

/-! ### The flush-to-zero guard is inactive on a normal numerator -/

private theorem divPipeline_ex_toNat (x y : FPR) :
    (divPipeline x y).ex.toNat = (FPR.decode x).exponent := by
  change (((x >>> 52).toUInt32) &&& 0x7FF).toNat = _
  exact toNat_ex_field_of x

private theorem divPipeline_ey_toNat (x y : FPR) :
    (divPipeline x y).ey.toNat = (FPR.decode y).exponent := by
  change (((y >>> 52).toUInt32) &&& 0x7FF).toNat = _
  exact toNat_ex_field_of y

private theorem divPipeline_dzu_eq_zero (x y : FPR) (ha : FPR.IsNormal x) :
    (divPipeline x y).dzu = 0 := by
  have hx1 : 1 ≤ (divPipeline x y).ex.toNat := by
    rw [divPipeline_ex_toNat]; exact Nat.one_le_iff_ne_zero.mpr ha.1
  have hxlt : (divPipeline x y).ex.toNat < 2 ^ 11 := by
    rw [divPipeline_ex_toNat]; exact FPR.decode_exponent_lt x
  have hsx : ((divPipeline x y).ex - 1).toNat = (divPipeline x y).ex.toNat - 1 :=
    toNat_sub_of_le_uint32 (by simpa using hx1)
  have hsh : (((divPipeline x y).ex - 1) >>> 31) = 0 := by
    rw [← UInt32.toNat_inj, toNat_shiftRight_31_uint32, show (0 : UInt32).toNat = 0 from rfl]
    omega
  change tbmask ((divPipeline x y).ex - 1) = 0
  unfold tbmask
  rw [hsh]
  decide

private theorem divPipeline_dm_eq (x y : FPR) (ha : FPR.IsNormal x) :
    (divPipeline x y).dm = 0xFFFFFFFFFFFFFFFF := by
  change (((divPipeline x y).dzu &&& 1).toUInt64 - 1) = _
  rw [divPipeline_dzu_eq_zero x y ha]
  decide

private theorem divPipeline_e_toInt (x y : FPR)
    (hx1 : 1 ≤ (divPipeline x y).ex.toNat) (hx2 : (divPipeline x y).ex.toNat ≤ 2046)
    (hy1 : 1 ≤ (divPipeline x y).ey.toNat) (hy2 : (divPipeline x y).ey.toNat ≤ 2046) :
    (divPipeline x y).e.toInt32.toInt
      = ((divPipeline x y).ex.toNat : ℤ) - ((divPipeline x y).ey.toNat : ℤ) - 55
        + ((divPipeline x y).es.toNat : ℤ) := by
  have hes := divPipeline_es_le_one x y
  have hES : ((divPipeline x y).es.toUInt32).toNat = (divPipeline x y).es.toNat := by
    rw [UInt64.toNat_toUInt32]; omega
  change ((divPipeline x y).ex - (divPipeline x y).ey - 55
      + (divPipeline x y).es.toUInt32).toInt32.toInt = _
  rw [UInt32.toInt32_add, Int32.toInt_add, UInt32.toInt32_sub, Int32.toInt_sub,
    UInt32.toInt32_sub, Int32.toInt_sub,
    toInt_toInt32_of_lt (show (divPipeline x y).ex.toNat < 2 ^ 31 by omega),
    toInt_toInt32_of_lt (show (divPipeline x y).ey.toNat < 2 ^ 31 by omega),
    toInt_toInt32_of_lt (show (55 : UInt32).toNat < 2 ^ 31 by decide),
    toInt_toInt32_of_lt (show ((divPipeline x y).es.toUInt32).toNat < 2 ^ 31 by omega),
    show (55 : UInt32).toNat = 55 from by decide, hES]
  push_cast
  rw [show (((divPipeline x y).ex.toNat : ℤ) - ((divPipeline x y).ey.toNat : ℤ)).bmod 4294967296
        = ((divPipeline x y).ex.toNat : ℤ) - ((divPipeline x y).ey.toNat : ℤ) from
      Int.bmod_eq_of_le_mul_two (by omega) (by omega)]
  rw [show (((divPipeline x y).ex.toNat : ℤ) - ((divPipeline x y).ey.toNat : ℤ)
          - 55).bmod 4294967296
        = ((divPipeline x y).ex.toNat : ℤ) - ((divPipeline x y).ey.toNat : ℤ) - 55 from
      Int.bmod_eq_of_le_mul_two (by omega) (by omega)]
  exact Int.bmod_eq_of_le_mul_two (by omega) (by omega)

private theorem divPipeline_e'_eq (x y : FPR) (ha : FPR.IsNormal x) :
    (divPipeline x y).e' = (divPipeline x y).e.toInt32 := by
  change ((divPipeline x y).e ^^^ ((divPipeline x y).dzu
      &&& ((divPipeline x y).e ^^^ ((0 : UInt32) - 1076)))).toInt32 = _
  rw [divPipeline_dzu_eq_zero x y ha, uint32_zero_and, uint32_xor_zero]

/-- The sign word of `FPR.div` is the exclusive-or of the operands' sign bits. -/
private theorem divPipeline_sign_factor (x y : FPR) :
    (if (divPipeline x y).sg.toNat = 1 then (-1 : ℝ) else 1)
      = (if (FPR.decode x).sign then (-1 : ℝ) else 1)
        * (if (FPR.decode y).sign then (-1 : ℝ) else 1) := by
  change (if ((x ^^^ y) >>> 63).toNat = 1 then (-1 : ℝ) else 1) = _
  rw [signWord_toNat]
  cases hx : (FPR.decode x).sign <;> cases hy : (FPR.decode y).sign <;> norm_num

private theorem divPipeline_abs_toReal_x (x y : FPR) (ha : FPR.IsNormal x) :
    |toReal x| = ((divPipeline x y).xu.toNat : ℝ)
      * (2 : ℝ) ^ (((FPR.decode x).exponent : ℤ) - 1075) := by
  rw [divPipeline_xu, significand_pack_toNat]
  change |(FPR.decode x).toReal| = _
  rw [abs_toReal_eq_significand_mul_two_zpow ha.1 ha.2]
  unfold FPR.Bits.significand
  rw [ite_eq_right ha.1]

private theorem divPipeline_abs_toReal_y (x y : FPR) (hb : FPR.IsNormal y) :
    |toReal y| = ((divPipeline x y).yu.toNat : ℝ)
      * (2 : ℝ) ^ (((FPR.decode y).exponent : ℤ) - 1075) := by
  rw [divPipeline_yu, significand_pack_toNat]
  change |(FPR.decode y).toReal| = _
  rw [abs_toReal_eq_significand_mul_two_zpow hb.1 hb.2]
  unfold FPR.Bits.significand
  rw [ite_eq_right hb.1]

/-- The exact quotient's magnitude, in the scale `FPR.div`'s exponent field uses. -/
private theorem divPipeline_abs_quotient (x y : FPR) (ha : FPR.IsNormal x) (hb : FPR.IsNormal y) :
    |toReal x / toReal y|
      = ((2 ^ 55 * ((divPipeline x y).xu.toNat : ℝ)) / ((divPipeline x y).yu.toNat : ℝ))
        * (2 : ℝ) ^ ((((FPR.decode x).exponent : ℤ) - ((FPR.decode y).exponent : ℤ)) - 55) := by
  have hyne : ((divPipeline x y).yu.toNat : ℝ) ≠ 0 := by
    have hyu := significand_pack_toNat y
    rw [← divPipeline_yu x y] at hyu
    have hpos : (0 : ℕ) < (divPipeline x y).yu.toNat := by omega
    exact_mod_cast hpos.ne'
  have key : (2 : ℝ) ^ (((FPR.decode x).exponent : ℤ) - 1075)
      = (2 : ℝ) ^ (((FPR.decode y).exponent : ℤ) - 1075) * (2 : ℝ) ^ (55 : ℕ) *
          (2 : ℝ) ^ ((((FPR.decode x).exponent : ℤ) - ((FPR.decode y).exponent : ℤ)) - 55) := by
    rw [mul_assoc, two_pow_mul_zpow, ← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0),
      show (((FPR.decode y).exponent : ℤ) - 1075) + (((55 : ℕ) : ℤ)
          + ((((FPR.decode x).exponent : ℤ) - ((FPR.decode y).exponent : ℤ)) - 55))
        = ((FPR.decode x).exponent : ℤ) - 1075 by push_cast; ring]
  rw [abs_div, divPipeline_abs_toReal_x x y ha, divPipeline_abs_toReal_y x y hb]
  field_simp
  rw [key]
  ring

/-! ### The real-valued quotient bracket -/

private theorem divPipeline_sg_le_one (x y : FPR) : (divPipeline x y).sg.toNat ≤ 1 := by
  change ((x ^^^ y) >>> 63).toNat ≤ 1
  rw [toNat_shiftRight_63_uint64]
  have h64 : (x ^^^ y).toNat < 2 ^ 64 := (x ^^^ y).toNat_lt_size
  omega

private theorem divPipeline_yu_pos (x y : FPR) : (0 : ℝ) < ((divPipeline x y).yu.toNat : ℝ) := by
  have h : (divPipeline x y).yu.toNat = (FPR.decode y).mantissa + 2 ^ 52 := by
    rw [divPipeline_yu]; exact significand_pack_toNat y
  have : 0 < (divPipeline x y).yu.toNat := by omega
  exact_mod_cast this

/-- The real form of the renormalised bracket, divided through by the divisor. -/
private theorem divPipeline_real_bracket (x y : FPR) :
    (((divPipeline x y).q1.toNat : ℝ) - 1) * (2 : ℝ) ^ (divPipeline x y).es.toNat
        < (2 ^ 55 * ((divPipeline x y).xu.toNat : ℝ)) / ((divPipeline x y).yu.toNat : ℝ)
      ∧ (2 ^ 55 * ((divPipeline x y).xu.toNat : ℝ)) / ((divPipeline x y).yu.toNat : ℝ)
        < (((divPipeline x y).q1.toNat : ℝ) + 1) * (2 : ℝ) ^ (divPipeline x y).es.toNat := by
  obtain ⟨hb1, hb2⟩ := divPipeline_q1_bracket x y
  have hy := divPipeline_yu_pos x y
  have hb1' : ((divPipeline x y).q1.toNat : ℝ) * (2 : ℝ) ^ (divPipeline x y).es.toNat
      * ((divPipeline x y).yu.toNat : ℝ)
      < 2 ^ 55 * ((divPipeline x y).xu.toNat : ℝ)
        + (2 : ℝ) ^ (divPipeline x y).es.toNat * ((divPipeline x y).yu.toNat : ℝ) := by
    exact_mod_cast hb1
  have hb2' : (2 : ℝ) ^ 55 * ((divPipeline x y).xu.toNat : ℝ)
      < ((divPipeline x y).q1.toNat : ℝ) * (2 : ℝ) ^ (divPipeline x y).es.toNat
          * ((divPipeline x y).yu.toNat : ℝ)
        + (2 : ℝ) ^ (divPipeline x y).es.toNat * ((divPipeline x y).yu.toNat : ℝ) := by
    exact_mod_cast hb2
  constructor
  · rw [lt_div_iff₀ hy, sub_mul]
    nlinarith [hb1']
  · rw [div_lt_iff₀ hy, add_mul]
    nlinarith [hb2']

/-- The error bound and the closure property for `FPR.div`, proved together: both rest on the
same exponent-window analysis. -/
private theorem div_error_aux (a b : FPR) (hb : toReal b ≠ 0) (ha : FPR.IsNormal a)
    (hb' : FPR.IsNormal b)
    (hr : FPR.InNormalMagnitudeRange (toReal a / toReal b)) :
    (|toReal (FPR.div a b) - toReal a / toReal b| ≤
      (2 : ℝ) ^ (-(52 : ℤ)) * |toReal a / toReal b|)
    ∧ FPR.IsNormal (FPR.div a b) := by
  have hne : toReal a / toReal b ≠ 0 :=
    div_ne_zero (toReal_ne_zero_of_isNormal ha) hb
  rcases hr with h0 | ⟨hlo, hhi⟩
  · exact absurd h0 hne
  have hx1 : 1 ≤ (divPipeline a b).ex.toNat := by
    rw [divPipeline_ex_toNat]; exact Nat.one_le_iff_ne_zero.mpr ha.1
  have hy1 : 1 ≤ (divPipeline a b).ey.toNat := by
    rw [divPipeline_ey_toNat]; exact Nat.one_le_iff_ne_zero.mpr hb'.1
  have hx2 : (divPipeline a b).ex.toNat ≤ 2046 := by
    rw [divPipeline_ex_toNat]; have := FPR.decode_exponent_lt a; have := ha.2; omega
  have hy2 : (divPipeline a b).ey.toNat ≤ 2046 := by
    rw [divPipeline_ey_toNat]; have := FPR.decode_exponent_lt b; have := hb'.2; omega
  have hmem := divPipeline_q1_mem a b
  set c : ℝ := (2 : ℝ) ^ ((((FPR.decode a).exponent : ℤ) - ((FPR.decode b).exponent : ℤ)) - 55)
    with hcdef
  have hc : 0 < c := zpow_pos (by norm_num) _
  set K : ℝ := (2 : ℝ) ^ (divPipeline a b).es.toNat with hKdef
  have hK : 0 < K := by rw [hKdef]; positivity
  set W : ℝ := ((divPipeline a b).q1.toNat : ℝ) with hWdef
  set P : ℝ := (2 ^ 55 * ((divPipeline a b).xu.toNat : ℝ)) / ((divPipeline a b).yu.toNat : ℝ)
    with hPdef
  have habsQ : |toReal a / toReal b| = P * c := divPipeline_abs_quotient a b ha hb'
  obtain ⟨hbr1, hbr2⟩ := divPipeline_real_bracket a b
  have hW1 : (2 : ℝ) ^ (54 : ℕ) ≤ W := by rw [hWdef]; exact_mod_cast hmem.1
  have hW2 : W ≤ (2 : ℝ) ^ (55 : ℕ) - 1 := by
    rw [hWdef]
    have hnat : (divPipeline a b).q1.toNat + 1 ≤ 2 ^ 55 := hmem.2
    have hR : (((divPipeline a b).q1.toNat + 1 : ℕ) : ℝ) ≤ ((2 ^ 55 : ℕ) : ℝ) := by
      exact_mod_cast hnat
    push_cast at hR; linarith
  have hkey : (2 : ℝ) ^ (53 : ℕ) * K + K ≤ P := by
    have hstep : ((2 : ℝ) ^ (53 : ℕ) + 1) * K ≤ (W - 1) * K :=
      mul_le_mul_of_nonneg_right (by norm_num at hW1 ⊢; linarith) hK.le
    nlinarith [hbr1, hstep]
  -- the exponent window
  have he'I : (divPipeline a b).e'.toInt
      = ((divPipeline a b).ex.toNat : ℤ) - ((divPipeline a b).ey.toNat : ℤ) - 55
        + ((divPipeline a b).es.toNat : ℤ) := by
    rw [divPipeline_e'_eq a b ha]; exact divPipeline_e_toInt a b hx1 hx2 hy1 hy2
  rw [divPipeline_ex_toNat, divPipeline_ey_toNat] at he'I
  have hScale : (2 : ℝ) ^ (divPipeline a b).e'.toInt = K * c := by
    rw [he'I, hKdef, hcdef, ← zpow_natCast (2 : ℝ) (divPipeline a b).es.toNat,
      ← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
    congr 1
    omega
  have hSpos : (0 : ℝ) < (2 : ℝ) ^ (divPipeline a b).e'.toInt := zpow_pos (by norm_num) _
  have hb1 : (W - 1) * ((2 : ℝ) ^ (divPipeline a b).e'.toInt) < |toReal a / toReal b| := by
    rw [hScale, habsQ, show (W - 1) * (K * c) = ((W - 1) * K) * c from by ring]
    exact mul_lt_mul_of_pos_right hbr1 hc
  have hb2 : |toReal a / toReal b|
      < (W + 1) * ((2 : ℝ) ^ (divPipeline a b).e'.toInt) := by
    rw [hScale, habsQ, show (W + 1) * (K * c) = ((W + 1) * K) * c from by ring]
    exact mul_lt_mul_of_pos_right hbr2 hc
  have hhi' : |toReal a / toReal b| ≤ (2 : ℝ) ^ (1024 : ℤ) - (2 : ℝ) ^ (971 : ℤ) := by
    rw [← maxFiniteReal_eq]; exact hhi
  have hlo' : (2 : ℝ) ^ (-(1022 : ℤ)) ≤ |toReal a / toReal b| := hlo
  have hle969 : (divPipeline a b).e'.toInt ≤ 969 := by
    have h := (zpow_lt_zpow_iff_right₀ (by norm_num : (1 : ℝ) < 2)).mp
      (mul_scale_lt hW1 hb1 hhi')
    omega
  have hge : -1076 ≤ (divPipeline a b).e'.toInt := by
    have h := (zpow_lt_zpow_iff_right₀ (by norm_num : (1 : ℝ) < 2)).mp
      (mul_scale_gt hW2 hb2 hSpos hlo')
    omega
  -- no carry out of the mantissa field at the very top of the range
  have hnc : (divPipeline a b).e'.toInt = 969 →
      roundQuarterTiesEven (divPipeline a b).q1.toNat < 2 ^ 53 := by
    intro h969
    by_contra hcc
    push Not at hcc
    have hround := (roundQuarterTiesEven_mem_of_normalized _ hmem.1 hmem.2).2
    have heq : roundQuarterTiesEven (divPipeline a b).q1.toNat = 2 ^ 53 := by omega
    have h4 := four_mul_roundQuarterTiesEven_le (divPipeline a b).q1.toNat
    rw [heq] at h4
    have hWbig : (2 : ℝ) ^ (55 : ℕ) - 2 ≤ W := by
      rw [hWdef]
      have hn : (2 : ℕ) ^ 55 ≤ (divPipeline a b).q1.toNat + 2 := by omega
      have hR : (((2 : ℕ) ^ 55 : ℕ) : ℝ) ≤ (((divPipeline a b).q1.toNat + 2 : ℕ) : ℝ) := by
        exact_mod_cast hn
      push_cast at hR; linarith
    rw [h969] at hb1
    set t : ℝ := (2 : ℝ) ^ (969 : ℤ) with ht
    have htpos : 0 < t := zpow_pos (by norm_num) _
    have e1 : (2 : ℝ) ^ (1024 : ℤ) = (2 : ℝ) ^ (55 : ℕ) * t := by
      rw [ht, two_pow_mul_zpow]; norm_num
    have e2 : (2 : ℝ) ^ (971 : ℤ) = 4 * t := by
      rw [ht, show (971 : ℤ) = 2 + 969 from by norm_num,
        zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
      norm_num
    rw [e1, e2] at hhi'
    clear_value t
    clear ht e1 e2
    have hlow : ((2 : ℝ) ^ (55 : ℕ) - 3) * t ≤ (W - 1) * t :=
      mul_le_mul_of_nonneg_right (by linarith) htpos.le
    rw [show ((2 : ℝ) ^ (55 : ℕ) - 3) * t = (2 : ℝ) ^ (55 : ℕ) * t - 3 * t from by ring] at hlow
    norm_num at hhi' hlow
    linarith
  -- the rounding step
  have hmul : FPR.div a b
      = make (divPipeline a b).sg (divPipeline a b).e' (divPipeline a b).q1 := by
    rw [div_eq_make, divPipeline_dm_eq a b ha, and_allOnes_uint64, and_allOnes_uint64]
  have hMV : |toReal (FPR.div a b)
        - (if (divPipeline a b).sg.toNat = 1 then (-1 : ℝ) else 1)
          * ((divPipeline a b).q1.toNat : ℝ) * (2 : ℝ) ^ (divPipeline a b).e'.toInt|
      ≤ (2 : ℝ) ^ (-(53 : ℤ))
        * |(if (divPipeline a b).sg.toNat = 1 then (-1 : ℝ) else 1)
            * ((divPipeline a b).q1.toNat : ℝ) * (2 : ℝ) ^ (divPipeline a b).e'.toInt| := by
    rw [show toReal (FPR.div a b) = toRealBits (FPR.div a b) from rfl, hmul]
    by_cases h969 : (divPipeline a b).e'.toInt = 969
    · exact abs_toRealBits_make_sub_le_of_no_carry _ _ _ (divPipeline_sg_le_one a b) hge hle969
        hmem.1 hmem.2 (hnc h969)
    · exact abs_toRealBits_make_sub_le _ _ _ (divPipeline_sg_le_one a b) hge (by omega)
        hmem.1 hmem.2
  -- the exact quotient, with its sign
  have hA := toReal_eq_sign_mul_abs a ha.1 ha.2
  have hB := toReal_eq_sign_mul_abs b hb'.1 hb'.2
  have hQsign : toReal a / toReal b
      = (if (divPipeline a b).sg.toNat = 1 then (-1 : ℝ) else 1) * (P * c) := by
    calc toReal a / toReal b
        = ((if (FPR.decode a).sign then (-1 : ℝ) else 1) * |toReal a|)
          / ((if (FPR.decode b).sign then (-1 : ℝ) else 1) * |toReal b|) := by rw [← hA, ← hB]
      _ = ((if (FPR.decode a).sign then (-1 : ℝ) else 1)
            * (if (FPR.decode b).sign then (-1 : ℝ) else 1)) * (|toReal a| / |toReal b|) := by
          rcases (by split_ifs <;> simp :
            (if (FPR.decode a).sign then (-1 : ℝ) else 1) = 1 ∨
            (if (FPR.decode a).sign then (-1 : ℝ) else 1) = -1) with h | h <;>
          rcases (by split_ifs <;> simp :
            (if (FPR.decode b).sign then (-1 : ℝ) else 1) = 1 ∨
            (if (FPR.decode b).sign then (-1 : ℝ) else 1) = -1) with h' | h' <;>
          rw [h, h'] <;> ring
      _ = (if (divPipeline a b).sg.toNat = 1 then (-1 : ℝ) else 1)
            * |toReal a / toReal b| := by rw [divPipeline_sign_factor, abs_div]
      _ = (if (divPipeline a b).sg.toNat = 1 then (-1 : ℝ) else 1) * (P * c) := by rw [habsQ]
  refine ⟨?_, ?_⟩
  · rw [hQsign]
    refine mul_error_combine (by split_ifs <;> simp) hc (by positivity) hK ?_
      hbr1 hbr2 hkey
    rw [show (if (divPipeline a b).sg.toNat = 1 then (-1 : ℝ) else 1) * (W * K * c)
        = (if (divPipeline a b).sg.toNat = 1 then (-1 : ℝ) else 1) * W
          * (2 : ℝ) ^ (divPipeline a b).e'.toInt from by rw [hScale]; ring]
    exact hMV
  · rw [hmul]
    exact FPR.isNormal_make _ _ _ (divPipeline_sg_le_one a b) hge hle969 hmem.1 hmem.2 hnc

/-- Relative error bound for `FPR.div`, on normal operands whose exact quotient stays in the
correctly-rounded binary64 magnitude window (`FPR.InNormalMagnitudeRange`); see `add_error` for
why both the operand- and result-side restrictions are necessary. -/
private theorem div_error_of_isNormal (a b : FPR) (hb : toReal b ≠ 0) (ha : FPR.IsNormal a)
    (hb' : FPR.IsNormal b)
    (hr : FPR.InNormalMagnitudeRange (toReal a / toReal b)) :
    |toReal (FPR.div a b) - toReal a / toReal b| ≤
    (2 : ℝ) ^ (-(52 : ℤ)) * |toReal a / toReal b| :=
  (div_error_aux a b hb ha hb' hr).1

/-- Closure for `FPR.div` on the domain `div_error` covers. A quotient of nonzero normals is
nonzero, so as with multiplication the result is always normal. -/
private theorem div_isNormalOrZero_of_isNormal (a b : FPR) (hb : toReal b ≠ 0)
    (ha : FPR.IsNormal a) (hb' : FPR.IsNormal b)
    (hr : FPR.InNormalMagnitudeRange (toReal a / toReal b)) :
    FPR.IsNormalOrZero (FPR.div a b) :=
  Or.inl (div_error_aux a b hb ha hb' hr).2

/-- `FPR.div`'s flush guard fires when the numerator's exponent field is `0`. -/
private theorem divPipeline_dzu_eq_allOnes (x y : FPR) (h : (FPR.decode x).exponent = 0) :
    (divPipeline x y).dzu = 0xFFFFFFFF := by
  have hex : (divPipeline x y).ex = 0 := by
    rw [← UInt32.toNat_inj, divPipeline_ex_toNat, h]; rfl
  have hsh : (((divPipeline x y).ex - 1) >>> 31) = 1 := by
    rw [← UInt32.toNat_inj, toNat_shiftRight_31_uint32, show (1 : UInt32).toNat = 1 from rfl,
      hex, uint32_zero_sub_one_toNat]
    norm_num
  change tbmask ((divPipeline x y).ex - 1) = 0xFFFFFFFF
  unfold tbmask
  rw [hsh]
  decide

/-- **`FPR.div` flushes to `+0` when the numerator is a zero encoding.** The guard `dzu` fires on
a zero numerator exponent field, clearing both the sign and the quotient and substituting the
flushed exponent. -/
private theorem div_eq_zero_of_exponent_eq_zero (a b : FPR) (h : (FPR.decode a).exponent = 0) :
    FPR.div a b = 0 := by
  have hdzu := divPipeline_dzu_eq_allOnes a b h
  have hdm : (divPipeline a b).dm = 0 := by
    change (((divPipeline a b).dzu &&& 1).toUInt64 - 1) = _
    rw [hdzu]; decide
  have he : (divPipeline a b).e' = ((0 : UInt32) - 1076).toInt32 := by
    change ((divPipeline a b).e ^^^ ((divPipeline a b).dzu
      &&& ((divPipeline a b).e ^^^ ((0 : UInt32) - 1076)))).toInt32 = _
    rw [hdzu, uint32_allOnes_and, ← UInt32.xor_assoc, UInt32.xor_self, UInt32.zero_xor]
  rw [div_eq_make, hdm, he,
    show ((divPipeline a b).sg &&& (0 : UInt64)) = 0 from by simp,
    show ((divPipeline a b).q1 &&& (0 : UInt64)) = 0 from by simp, make_flushed]
  decide

theorem div_error (a b : FPR) (hbne : toReal b ≠ 0) (ha : FPR.IsNormalOrZero a)
    (hb : FPR.IsNormalOrZero b)
    (hr : FPR.InNormalMagnitudeRange (toReal a / toReal b)) :
    |toReal (FPR.div a b) - toReal a / toReal b| ≤
    (2 : ℝ) ^ (-(52 : ℤ)) * |toReal a / toReal b| := by
  have hbn : FPR.IsNormal b := hb.resolve_right (fun hz => hbne (toReal_eq_zero_of_isZero hz))
  rcases ha with ha | ha
  · exact div_error_of_isNormal a b hbne ha hbn hr
  · rw [div_eq_zero_of_exponent_eq_zero a b ha.1, toReal_eq_zero_of_isZero isZero_zero,
      toReal_eq_zero_of_isZero ha, zero_div, sub_zero, abs_zero]
    positivity

theorem div_isNormalOrZero (a b : FPR) (hbne : toReal b ≠ 0) (ha : FPR.IsNormalOrZero a)
    (hb : FPR.IsNormalOrZero b)
    (hr : FPR.InNormalMagnitudeRange (toReal a / toReal b)) :
    FPR.IsNormalOrZero (FPR.div a b) := by
  have hbn : FPR.IsNormal b := hb.resolve_right (fun hz => hbne (toReal_eq_zero_of_isZero hz))
  rcases ha with ha | ha
  · exact div_isNormalOrZero_of_isNormal a b hbne ha hbn hr
  · exact Or.inr (by rw [div_eq_zero_of_exponent_eq_zero a b ha.1]; exact isZero_zero)

end

end Falcon.Concrete.FPRBridge
