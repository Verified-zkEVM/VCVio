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
# Correct rounding of `FPR.sqrt`

The digit-recurrence loop computes the integer square root; the halved exponent and the
real-valued root bracket then give `sqrt_error` and the closure fact `sqrt_isNormalOrZero`.
-/

public section

namespace Falcon.Concrete.FPRBridge

open Falcon.Concrete.FPR

noncomputable section

/-! ### What `FPR.sqrt`'s digit-recurrence loop computes

Each iteration appends one bit to the root and keeps a scaled remainder. Writing `q` for the
partial root, `s` for its double, `r` for the bit weight and `xp` for the remainder, the loop
maintains `q ^ 2 * 2 ^ k + 2 ^ 53 * xp = 2 ^ (54 + k) * xu`, with `xp` held below
`4 * q + 2 ^ (55 - k)`.
The invariant and the bit weight `r = 2 ^ (53 - k)` are mutually dependent: the quadratic term
telescopes precisely because `r * 2 ^ (k + 1) = 2 ^ 54`. -/

private theorem sqrtStep_toNat (v : UInt64 × UInt64 × UInt64 × UInt64)
    (hq : v.2.1.toNat < 2 ^ 54) (hs : v.2.2.1.toNat < 2 ^ 55) (hr : v.2.2.2.toNat ≤ 2 ^ 53)
    (hxp : v.1.toNat < 2 ^ 57) :
    (sqrtStep v).2.2.2.toNat = v.2.2.2.toNat / 2
      ∧ (sqrtStep v).2.1.toNat = v.2.1.toNat
          + (if v.2.2.1.toNat + v.2.2.2.toNat ≤ v.1.toNat then v.2.2.2.toNat else 0)
      ∧ (sqrtStep v).2.2.1.toNat = v.2.2.1.toNat
          + 2 * (if v.2.2.1.toNat + v.2.2.2.toNat ≤ v.1.toNat then v.2.2.2.toNat else 0)
      ∧ (sqrtStep v).1.toNat = 2 * (v.1.toNat
          - (if v.2.2.1.toNat + v.2.2.2.toNat ≤ v.1.toNat
              then v.2.2.1.toNat + v.2.2.2.toNat else 0)) := by
  simp only [sqrtStep]
  have htr : (v.2.2.1 + v.2.2.2).toNat = v.2.2.1.toNat + v.2.2.2.toNat :=
    toNat_add_of_lt_uint64 (by omega)
  have hb : (v.1 - (v.2.2.1 + v.2.2.2)) >>> 63 - 1
      = if v.2.2.1.toNat + v.2.2.2.toNat ≤ v.1.toNat then (0 : UInt64) - 1 else 0 := by
    rw [sub_mask_of_lt v.1 (v.2.2.1 + v.2.2.2) (by omega) (by rw [htr]; omega), htr]
  rw [hb]
  by_cases hbit : v.2.2.1.toNat + v.2.2.2.toNat ≤ v.1.toNat
  · simp only [ite_eq_left hbit]
    have e2 : v.2.2.2 &&& ((0 : UInt64) - 1) = v.2.2.2 := by rw [UInt64.and_comm, allOnes_and]
    have e3 : ((0 : UInt64) - 1) &&& (v.2.2.2 <<< (1 : UInt64)) = v.2.2.2 <<< (1 : UInt64) :=
      allOnes_and _
    have e4 : (v.2.2.1 + v.2.2.2) &&& ((0 : UInt64) - 1) = v.2.2.1 + v.2.2.2 := by
      rw [UInt64.and_comm, allOnes_and]
    rw [e2, e3, e4]
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [UInt64.toNat_shiftRight, show (1 : UInt64).toNat % 64 = 1 from by decide,
        Nat.shiftRight_eq_div_pow, pow_one]
    · exact toNat_add_of_lt_uint64 (by omega)
    · have hshl : (v.2.2.2 <<< (1 : UInt64)).toNat = 2 * v.2.2.2.toNat := by
        rw [toNat_shiftLeft_one]; omega
      rw [toNat_add_of_lt_uint64 (by rw [hshl]; omega), hshl]
    · have hsub2 : (v.1 - (v.2.2.1 + v.2.2.2)).toNat
          = v.1.toNat - (v.2.2.1.toNat + v.2.2.2.toNat) := by
        rw [toNat_sub_of_le_uint64 _ _ (by rw [htr]; omega), htr]
      rw [toNat_shiftLeft_one, hsub2]
      omega
  · simp only [ite_eq_right hbit]
    have e2 : v.2.2.2 &&& (0 : UInt64) = 0 := by rw [UInt64.and_comm]; exact uint64_zero_and _
    have e3 : (0 : UInt64) &&& (v.2.2.2 <<< (1 : UInt64)) = 0 := uint64_zero_and _
    have e4 : (v.2.2.1 + v.2.2.2) &&& (0 : UInt64) = 0 := by
      rw [UInt64.and_comm]; exact uint64_zero_and _
    rw [e2, e3, e4]
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [UInt64.toNat_shiftRight, show (1 : UInt64).toNat % 64 = 1 from by decide,
        Nat.shiftRight_eq_div_pow, pow_one]
    · simp
    · simp
    · rw [UInt64.sub_zero, toNat_shiftLeft_one]; omega

private theorem sqrtLoop_invariant (xu : UInt64) (hxu : xu.toNat < 2 ^ 54) :
    ∀ n : ℕ, n ≤ 53 →
      (sqrtStep^[n] (xu <<< 1, 0, 0, (1 : UInt64) <<< 53)).2.2.2.toNat = 2 ^ (53 - n)
      ∧ (sqrtStep^[n] (xu <<< 1, 0, 0, (1 : UInt64) <<< 53)).2.2.1.toNat
          = 2 * (sqrtStep^[n] (xu <<< 1, 0, 0, (1 : UInt64) <<< 53)).2.1.toNat
      ∧ (sqrtStep^[n] (xu <<< 1, 0, 0, (1 : UInt64) <<< 53)).2.1.toNat ^ 2 * 2 ^ n
          + 2 ^ 53 * (sqrtStep^[n] (xu <<< 1, 0, 0, (1 : UInt64) <<< 53)).1.toNat
          = 2 ^ (54 + n) * xu.toNat
      ∧ (sqrtStep^[n] (xu <<< 1, 0, 0, (1 : UInt64) <<< 53)).1.toNat
          < 4 * (sqrtStep^[n] (xu <<< 1, 0, 0, (1 : UInt64) <<< 53)).2.1.toNat + 2 ^ (55 - n) := by
  intro n
  induction n with
  | zero =>
    intro _
    simp only [Function.iterate_zero, id_eq]
    have h1 : (xu <<< 1).toNat = 2 * xu.toNat := by rw [toNat_shiftLeft_one]; omega
    refine ⟨?_, ?_, ?_, ?_⟩
    · exact show ((1 : UInt64) <<< 53).toNat = 2 ^ 53 from by decide
    · simp
    · rw [show UInt64.toNat 0 = 0 from rfl, h1]; ring
    · rw [show UInt64.toNat 0 = 0 from rfl, h1]
      have : (2:ℕ) ^ 55 = 2 * 2 ^ 54 := by ring
      omega
  | succ k ih =>
    intro hk
    obtain ⟨hr_k, hs_k, hinv_k, hbnd_k⟩ := ih (by omega)
    set state := sqrtStep^[k] (xu <<< 1, 0, 0, (1 : UInt64) <<< 53) with hstate
    rw [Function.iterate_succ_apply', ← hstate]
    have hq_k54 : state.2.1.toNat < 2 ^ 54 := by
      by_contra hcon
      push Not at hcon
      have hsq : ((2 : ℕ) ^ 54) ^ 2 ≤ state.2.1.toNat ^ 2 := Nat.pow_le_pow_left hcon 2
      have e108 : ((2 : ℕ) ^ 54) ^ 2 = 2 ^ 108 := by rw [← pow_mul]
      have hlow : (2 : ℕ) ^ 108 * 2 ^ k ≤ state.2.1.toNat ^ 2 * 2 ^ k := by
        rw [← e108]; exact Nat.mul_le_mul_right _ hsq
      have hxu54 : (2 : ℕ) ^ (54 + k) * xu.toNat < 2 ^ (54 + k) * 2 ^ 54 :=
        (Nat.mul_lt_mul_left (Nat.two_pow_pos (54 + k))).mpr hxu
      have e108k : (2 : ℕ) ^ (54 + k) * 2 ^ 54 = 2 ^ (108 + k) := by
        rw [← pow_add]; congr 1; omega
      have e108k' : (2 : ℕ) ^ 108 * 2 ^ k = 2 ^ (108 + k) := by rw [← pow_add]
      omega
    have hs_k55 : state.2.2.1.toNat < 2 ^ 55 := by
      have e2 : (2 : ℕ) ^ 55 = 2 * 2 ^ 54 := by norm_num
      omega
    have hr_k53 : state.2.2.2.toNat ≤ 2 ^ 53 := by
      rw [hr_k]; exact Nat.pow_le_pow_right (by norm_num) (by omega)
    have hxp_k57 : state.1.toNat < 2 ^ 57 := by
      have e1 : (2 : ℕ) ^ (55 - k) ≤ 2 ^ 55 := Nat.pow_le_pow_right (by norm_num) (by omega)
      have e2 : (4 : ℕ) * 2 ^ 54 = 2 ^ 56 := by norm_num
      have e3 : (2 : ℕ) ^ 56 + 2 ^ 55 < 2 ^ 57 := by norm_num
      omega
    obtain ⟨hstep_r, hstep_q, hstep_s, hstep_xp⟩ :=
      sqrtStep_toNat state hq_k54 hs_k55 hr_k53 hxp_k57
    have hnewr : (sqrtStep state).2.2.2.toNat = 2 ^ (53 - (k + 1)) := by
      rw [hstep_r, hr_k]
      have hexp : 53 - k = 53 - (k + 1) + 1 := by omega
      rw [hexp, pow_succ]
      omega
    by_cases hbit : state.2.2.1.toNat + state.2.2.2.toNat ≤ state.1.toNat
    · simp only [ite_eq_left hbit] at hstep_q hstep_s hstep_xp
      refine ⟨hnewr, by rw [hstep_s, hstep_q, hs_k]; ring, ?_, ?_⟩
      · obtain ⟨d, hd⟩ := Nat.le.dest hbit
        have hxpd : state.1.toNat - (state.2.2.1.toNat + state.2.2.2.toNat) = d := by omega
        rw [hstep_q, hstep_xp, hxpd]
        rw [show (54 + (k + 1) : ℕ) = 55 + k from by omega]
        have hinv_k' : state.2.1.toNat ^ 2 * 2 ^ k
            + 2 ^ 53 * (state.2.2.1.toNat + state.2.2.2.toNat + d) = 2 ^ (54 + k) * xu.toNat := by
          rw [hd]; exact hinv_k
        rw [hs_k] at hinv_k'
        have hp1 : state.2.2.2.toNat * 2 ^ (k + 2) = 2 ^ 55 := by
          rw [hr_k, ← pow_add]; congr 1; omega
        have hp2 : state.2.2.2.toNat * 2 ^ (k + 1) = 2 ^ 54 := by
          rw [hr_k, ← pow_add]; congr 1; omega
        have hexpand : (state.2.1.toNat + state.2.2.2.toNat) ^ 2 * 2 ^ (k + 1)
            = 2 * (state.2.1.toNat ^ 2 * 2 ^ k)
              + state.2.1.toNat * (state.2.2.2.toNat * 2 ^ (k + 2))
              + state.2.2.2.toNat * (state.2.2.2.toNat * 2 ^ (k + 1)) := by
          ring
        rw [hexpand, hp1, hp2]
        have hdist : (2 : ℕ) ^ 53 * (2 * state.2.1.toNat + state.2.2.2.toNat + d)
            = 2 ^ 54 * state.2.1.toNat + 2 ^ 53 * state.2.2.2.toNat + 2 ^ 53 * d := by ring
        rw [hdist] at hinv_k'
        have hdist2 : (2 : ℕ) ^ 53 * (2 * d) = 2 ^ 54 * d := by ring
        rw [hdist2]
        have h2kxu : (2 : ℕ) * (2 ^ (54 + k) * xu.toNat) = 2 ^ (55 + k) * xu.toNat := by
          rw [show (55 + k : ℕ) = (54 + k) + 1 from by omega, pow_succ]; ring
        omega
      · rw [hstep_q, hstep_xp]
        rw [show (55 - (k + 1) : ℕ) = 54 - k from by omega]
        have h54 : (2 : ℕ) ^ (54 - k) = 2 * 2 ^ (53 - k) := by
          rw [show (54 - k : ℕ) = (53 - k) + 1 from by omega, pow_succ]; ring
        have h55 : (2 : ℕ) ^ (55 - k) = 4 * 2 ^ (53 - k) := by
          rw [show (55 - k : ℕ) = (53 - k) + 2 from by omega, pow_add]; ring
        omega
    · simp only [ite_eq_right hbit] at hstep_q hstep_s hstep_xp
      refine ⟨hnewr, by rw [hstep_s, hstep_q]; omega, ?_, ?_⟩
      · rw [hstep_q, hstep_xp]
        rw [show (54 + (k + 1) : ℕ) = 55 + k from by omega]
        have h2kxu : (2 : ℕ) * (2 ^ (54 + k) * xu.toNat) = 2 ^ (55 + k) * xu.toNat := by
          rw [show (55 + k : ℕ) = (54 + k) + 1 from by omega, pow_succ]; ring
        have hexpand2 : (state.2.1.toNat + 0) ^ 2 * 2 ^ (k + 1)
            = 2 * (state.2.1.toNat ^ 2 * 2 ^ k) := by ring
        have hdist3 : (2 : ℕ) ^ 53 * (2 * (state.1.toNat - 0))
            = 2 * (2 ^ 53 * state.1.toNat) := by
          rw [Nat.sub_zero]; ring
        rw [hexpand2, hdist3]
        omega
      · rw [hstep_q, hstep_xp]
        rw [show (55 - (k + 1) : ℕ) = 54 - k from by omega]
        have h54 : (2 : ℕ) ^ (54 - k) = 2 * 2 ^ (53 - k) := by
          rw [show (54 - k : ℕ) = (53 - k) + 1 from by omega, pow_succ]; ring
        rw [h54]
        omega

/-! ### The loop's closing step, and the integer square root it computes

The bit weight `r` reaches zero on the final iteration, so the `r = 2 ^ (53 - k)` conjunct of
`sqrtLoop_invariant` stops at `k = 53`; the remaining conjuncts survive one more step. That last
step is what turns the invariant into an exact integer square root. -/

private theorem sqrtLoop_at_54 (xu : UInt64) (hxu : xu.toNat < 2 ^ 54) :
    (sqrtStep^[54] (xu <<< 1, 0, 0, (1 : UInt64) <<< 53)).2.1.toNat ^ 2 * 2 ^ 54
        + 2 ^ 53 * (sqrtStep^[54] (xu <<< 1, 0, 0, (1 : UInt64) <<< 53)).1.toNat
        = 2 ^ 108 * xu.toNat
      ∧ (sqrtStep^[54] (xu <<< 1, 0, 0, (1 : UInt64) <<< 53)).1.toNat
        < 4 * (sqrtStep^[54] (xu <<< 1, 0, 0, (1 : UInt64) <<< 53)).2.1.toNat + 2 := by
  obtain ⟨hr, hs, hinv, hbnd⟩ := sqrtLoop_invariant xu hxu 53 (by norm_num)
  set st := sqrtStep^[53] (xu <<< 1, 0, 0, (1 : UInt64) <<< 53) with hst
  rw [show (54 : ℕ) = 53 + 1 from rfl, Function.iterate_succ_apply', ← hst]
  -- the overflow bounds one more step needs
  have hq54 : st.2.1.toNat < 2 ^ 54 := by
    by_contra hcon
    push Not at hcon
    have hsq : ((2 : ℕ) ^ 54) ^ 2 ≤ st.2.1.toNat ^ 2 := Nat.pow_le_pow_left hcon 2
    have e108 : ((2 : ℕ) ^ 54) ^ 2 = 2 ^ 108 := by rw [← pow_mul]
    have hlow : (2 : ℕ) ^ 108 * 2 ^ 53 ≤ st.2.1.toNat ^ 2 * 2 ^ 53 := by
      rw [← e108]; exact Nat.mul_le_mul_right _ hsq
    have hhi : (2 : ℕ) ^ (54 + 53) * xu.toNat < 2 ^ (54 + 53) * 2 ^ 54 :=
      (Nat.mul_lt_mul_left (Nat.two_pow_pos (54 + 53))).mpr hxu
    have e1 : (2 : ℕ) ^ (54 + 53) * 2 ^ 54 = 2 ^ 161 := by rw [← pow_add]
    have e2 : (2 : ℕ) ^ 108 * 2 ^ 53 = 2 ^ 161 := by rw [← pow_add]
    omega
  have hs55 : st.2.2.1.toNat < 2 ^ 55 := by
    have : (2 : ℕ) ^ 55 = 2 * 2 ^ 54 := by norm_num
    omega
  have hr53 : st.2.2.2.toNat ≤ 2 ^ 53 := by rw [hr]; norm_num
  have hxp57 : st.1.toNat < 2 ^ 57 := by
    have e1 : (4 : ℕ) * 2 ^ 54 = 2 ^ 56 := by norm_num
    have e2 : (2 : ℕ) ^ (55 - 53) = 4 := by norm_num
    omega
  obtain ⟨hstep_r, hstep_q, hstep_s, hstep_xp⟩ := sqrtStep_toNat st hq54 hs55 hr53 hxp57
  rw [hr] at hstep_q hstep_s hstep_xp
  norm_num at hstep_q hstep_xp
  have hinv' : st.2.1.toNat ^ 2 * 2 ^ 53 + 2 ^ 53 * st.1.toNat = 2 ^ 107 * xu.toNat := by
    rw [show (54 : ℕ) + 53 = 107 from by norm_num] at hinv; exact hinv
  have hsplit : (2 : ℕ) ^ 108 * xu.toNat = 2 * (2 ^ 107 * xu.toNat) := by ring
  rw [show (53 : ℕ) + 1 = 54 from rfl]
  by_cases hbit : st.2.2.1.toNat < st.1.toNat
  · rw [ite_eq_left hbit] at hstep_q hstep_xp
    rw [hs] at hbit hstep_xp
    obtain ⟨d, hd⟩ := Nat.le.dest hbit
    have hxpd : st.1.toNat - (2 * st.2.1.toNat + 1) = d := by omega
    rw [hstep_q, hstep_xp, hxpd]
    refine ⟨?_, by omega⟩
    rw [hsplit, ← hinv', show st.1.toNat = 2 * st.2.1.toNat + 1 + d from by omega]
    ring
  · rw [ite_eq_right hbit] at hstep_q hstep_xp
    rw [hstep_q, hstep_xp, Nat.sub_zero, add_zero]
    refine ⟨?_, by omega⟩
    rw [hsplit, ← hinv']
    ring

/-- The loop computes an exact integer square root: `q ^ 2 ≤ 2 ^ 54 * xu < (q + 1) ^ 2`. -/
private theorem sqrtLoop_isqrt (xu : UInt64) (hxu : xu.toNat < 2 ^ 54) :
    (sqrtStep^[54] (xu <<< 1, 0, 0, (1 : UInt64) <<< 53)).2.1.toNat ^ 2 ≤ 2 ^ 54 * xu.toNat
      ∧ 2 ^ 54 * xu.toNat
        < ((sqrtStep^[54] (xu <<< 1, 0, 0, (1 : UInt64) <<< 53)).2.1.toNat + 1) ^ 2 := by
  obtain ⟨hinv, hbnd⟩ := sqrtLoop_at_54 xu hxu
  set q := (sqrtStep^[54] (xu <<< 1, 0, 0, (1 : UInt64) <<< 53)).2.1.toNat with hq
  set xp := (sqrtStep^[54] (xu <<< 1, 0, 0, (1 : UInt64) <<< 53)).1.toNat with hxp
  have h108 : (2 : ℕ) ^ 108 = 2 ^ 54 * 2 ^ 54 := by norm_num
  have hexp : (q + 1) ^ 2 * 2 ^ 54 = q ^ 2 * 2 ^ 54 + 2 ^ 55 * q + 2 ^ 54 := by ring
  constructor
  · nlinarith [hinv, h108]
  · nlinarith [hinv, hbnd, hexp, h108]

/-- The integer square root brackets the real one. -/
private theorem nat_sqrt_bracket {q N : ℕ} (h1 : q ^ 2 ≤ N) (h2 : N < (q + 1) ^ 2) :
    (q : ℝ) ≤ Real.sqrt (N : ℝ) ∧ Real.sqrt (N : ℝ) < (q : ℝ) + 1 := by
  constructor
  · rw [show ((q : ℝ)) = Real.sqrt ((q : ℝ) ^ 2) from
      (Real.sqrt_sq (by positivity)).symm]
    exact Real.sqrt_le_sqrt (by exact_mod_cast h1)
  · rw [show ((q : ℝ) + 1) = Real.sqrt (((q : ℝ) + 1) ^ 2) from
      (Real.sqrt_sq (by positivity)).symm]
    refine Real.sqrt_lt_sqrt (by positivity) ?_
    have : ((N : ℕ) : ℝ) < (((q + 1) ^ 2 : ℕ) : ℝ) := by exact_mod_cast h2
    push_cast at this
    linarith

/-! ### `FPR.sqrt`'s pipeline fields -/

private theorem sqrtPipeline_xuRaw (x : FPR) :
    (sqrtPipeline x).xu_ = (x &&& M52) ||| ((1 : UInt64) <<< 52) := rfl

private theorem sqrtPipeline_exRaw (x : FPR) :
    (sqrtPipeline x).ex_ = ((x >>> 52).toUInt32) &&& 0x7FF := rfl

private theorem sqrtPipeline_eRaw (x : FPR) :
    (sqrtPipeline x).e_ = (sqrtPipeline x).ex_.toInt32 - 1023 := rfl

private theorem sqrtPipeline_xu_eq (x : FPR) :
    (sqrtPipeline x).xu
      = (sqrtPipeline x).xu_
        + ((sqrtPipeline x).xu_ &&& (0 - ((sqrtPipeline x).e_.toUInt32 &&& 1).toUInt64)) := rfl

private theorem sqrtPipeline_e_eq (x : FPR) :
    (sqrtPipeline x).e = (fpr_arsh32 (sqrtPipeline x).e_.toUInt32 1).toInt32 := rfl

private theorem sqrtPipeline_q1_eq (x : FPR) :
    (sqrtPipeline x).q1
      = ((sqrtPipeline x).loopRes.2.1 <<< 1)
        ||| (((sqrtPipeline x).loopRes.1 ||| (0 - (sqrtPipeline x).loopRes.1)) >>> 63) := rfl

private theorem sqrtPipeline_e'_eq (x : FPR) : (sqrtPipeline x).e' = (sqrtPipeline x).e - 54 := rfl

private theorem sqrtPipeline_q2_eq (x : FPR) :
    (sqrtPipeline x).q2
      = (sqrtPipeline x).q1 &&& ((0 : UInt64) - (((sqrtPipeline x).ex_ + 0x7FF) >>> 11).toUInt64) :=
  rfl

/-! ### The halved exponent -/

/-- Reinterpreting a large `UInt32` as an `Int32` subtracts the modulus. -/
private theorem toInt_toInt32_of_ge {y : UInt32} (hy : 2 ^ 31 ≤ y.toNat) :
    y.toInt32.toInt = (y.toNat : ℤ) - 2 ^ 32 := by
  have h : y.toNat < 2 ^ 32 := y.toNat_lt_size
  unfold Int32.toInt
  rw [UInt32.toBitVec_toInt32, BitVec.toInt_eq_toNat_bmod, UInt32.toNat_toBitVec]
  simp only [Int.bmod]
  norm_num
  omega

/-- `fpr_arsh32 v 1` is the arithmetic right shift by one: a logical shift with the sign bit
replicated into the vacated top position. -/
private theorem toNat_fpr_arsh32_one (v : UInt32) :
    (fpr_arsh32 v 1).toNat = v.toNat / 2 + (if v.toNat < 2 ^ 31 then 0 else 2 ^ 31) := by
  have hv : v.toNat < 2 ^ 32 := v.toNat_lt_size
  have hsh31 : (v >>> 31).toNat = v.toNat / 2 ^ 31 := toNat_shiftRight_31_uint32 v
  have hsh1 : (v >>> 1).toNat = v.toNat / 2 := by
    rw [UInt32.toNat_shiftRight, show (1 : UInt32).toNat % 32 = 1 from by decide,
      Nat.shiftRight_eq_div_pow, pow_one]
  change ((v >>> 1) ||| (((0 : UInt32) - (v >>> 31)) <<< 31)).toNat = _
  by_cases h : v.toNat < 2 ^ 31
  · have hz : (v >>> 31) = 0 := by
      rw [← UInt32.toNat_inj, hsh31, show (0 : UInt32).toNat = 0 from rfl]; omega
    rw [hz, ite_eq_left h, show (((0 : UInt32) - 0) <<< 31) = 0 from by decide,
      UInt32.toNat_or, hsh1,
      show (0 : UInt32).toNat = 0 from rfl, Nat.or_zero, Nat.add_zero]
  · have hz : (v >>> 31) = 1 := by
      rw [← UInt32.toNat_inj, hsh31, show (1 : UInt32).toNat = 1 from rfl]; omega
    rw [hz, ite_eq_right h, show (((0 : UInt32) - 1) <<< 31) = 0x80000000 from by decide,
      UInt32.toNat_or, hsh1, show (0x80000000 : UInt32).toNat = 2 ^ 31 from by decide]
    exact or_two_pow_add_of_lt _ 31 (by omega)

private theorem sqrtPipeline_exRaw_toNat (x : FPR) :
    (sqrtPipeline x).ex_.toNat = (FPR.decode x).exponent := by
  rw [sqrtPipeline_exRaw]; exact toNat_ex_field_of x

private theorem sqrtPipeline_eRaw_toUInt32 (x : FPR) :
    (sqrtPipeline x).e_.toUInt32 = (sqrtPipeline x).ex_ - 1023 := by
  rw [sqrtPipeline_eRaw, Int32.toUInt32_sub, UInt32.toUInt32_toInt32,
    show ((1023 : Int32).toUInt32) = 1023 from by decide]

private theorem sqrtPipeline_eRaw_toUInt32_toNat (x : FPR) :
    ((sqrtPipeline x).e_.toUInt32).toNat
      = if 1023 ≤ (FPR.decode x).exponent then (FPR.decode x).exponent - 1023
        else 2 ^ 32 + (FPR.decode x).exponent - 1023 := by
  have hex : (sqrtPipeline x).ex_.toNat = (FPR.decode x).exponent := sqrtPipeline_exRaw_toNat x
  have hlt : (FPR.decode x).exponent < 2 ^ 11 := FPR.decode_exponent_lt x
  rw [sqrtPipeline_eRaw_toUInt32, UInt32.toNat_sub,
    show (1023 : UInt32).toNat = 1023 from by decide]
  split_ifs <;> omega

/-- The parity bit `FPR.sqrt` folds into its significand, and the halved exponent it pairs it
with: `e_ = 2 * e + p` with `p = 1` exactly when the biased exponent field is even. -/
private theorem sqrtPipeline_e_spec (x : FPR)
    (h1 : 1 ≤ (FPR.decode x).exponent) (h2 : (FPR.decode x).exponent ≤ 2046) :
    ((sqrtPipeline x).e_.toUInt32 &&& 1).toNat
        = (if (FPR.decode x).exponent % 2 = 0 then 1 else 0)
      ∧ 2 * (sqrtPipeline x).e.toInt
          + (if (FPR.decode x).exponent % 2 = 0 then (1 : ℤ) else 0)
        = ((FPR.decode x).exponent : ℤ) - 1023 := by
  have hu := sqrtPipeline_eRaw_toUInt32_toNat x
  refine ⟨?_, ?_⟩
  · rw [UInt32.toNat_and, show (1 : UInt32).toNat = 2 ^ 1 - 1 from by decide,
      Nat.and_two_pow_sub_one_eq_mod, hu]
    split_ifs <;> omega
  · rw [sqrtPipeline_e_eq]
    have hr := toNat_fpr_arsh32_one (sqrtPipeline x).e_.toUInt32
    by_cases hc : 1023 ≤ (FPR.decode x).exponent
    · rw [ite_eq_left hc] at hu
      rw [hu, ite_eq_left (by omega)] at hr
      rw [toInt_toInt32_of_lt (by omega), hr]
      split_ifs <;> omega
    · rw [ite_eq_right hc] at hu
      rw [hu, ite_eq_right (by omega)] at hr
      rw [toInt_toInt32_of_ge (by omega), hr]
      split_ifs <;> omega

/-- The halved exponent stays far inside `Int32`: `e ∈ [-511, 511]` for a normal operand. -/
private theorem sqrtPipeline_e_mem (x : FPR)
    (h1 : 1 ≤ (FPR.decode x).exponent) (h2 : (FPR.decode x).exponent ≤ 2046) :
    -511 ≤ (sqrtPipeline x).e.toInt ∧ (sqrtPipeline x).e.toInt ≤ 511 := by
  have he := (sqrtPipeline_e_spec x h1 h2).2
  have hcast : (1 : ℤ) ≤ ((FPR.decode x).exponent : ℤ) ∧ ((FPR.decode x).exponent : ℤ) ≤ 2046 := by
    constructor <;> exact_mod_cast ‹_›
  split_ifs at he <;> omega

private theorem sqrtPipeline_e'_toInt (x : FPR)
    (h1 : 1 ≤ (FPR.decode x).exponent) (h2 : (FPR.decode x).exponent ≤ 2046) :
    (sqrtPipeline x).e'.toInt = (sqrtPipeline x).e.toInt - 54 := by
  obtain ⟨hlo, hhi⟩ := sqrtPipeline_e_mem x h1 h2
  rw [sqrtPipeline_e'_eq, Int32.toInt_sub, show ((54 : Int32).toInt) = 54 from by decide]
  exact Int.bmod_eq_of_le_mul_two (by omega) (by omega)

/-! ### The doubled significand -/

private theorem sqrtPipeline_xuRaw_toNat (x : FPR) :
    (sqrtPipeline x).xu_.toNat = (FPR.decode x).mantissa + 2 ^ 52 := by
  rw [sqrtPipeline_xuRaw]; exact significand_pack_toNat x

/-- The parity bit doubles the significand: `xu = xu_ * (1 + p)`. -/
private theorem sqrtPipeline_xu_toNat_of_bit (x : FPR) {p : ℕ} (hp : p ≤ 1)
    (hbit : ((sqrtPipeline x).e_.toUInt32 &&& 1).toNat = p) :
    (sqrtPipeline x).xu.toNat = (sqrtPipeline x).xu_.toNat * (1 + p) := by
  have hxu := sqrtPipeline_xuRaw_toNat x
  have hm := FPR.decode_mantissa_lt x
  rw [sqrtPipeline_xu_eq]
  interval_cases p
  · have hw : ((sqrtPipeline x).e_.toUInt32 &&& 1) = 0 := by
      rw [← UInt32.toNat_inj, hbit]; rfl
    rw [hw, show ((0 : UInt32).toUInt64) = 0 from by decide,
      show ((0 : UInt64) - 0) = 0 from by decide, and_zero_uint64, UInt64.add_zero]
    omega
  · have hw : ((sqrtPipeline x).e_.toUInt32 &&& 1) = 1 := by
      rw [← UInt32.toNat_inj, hbit]; rfl
    rw [hw, show ((1 : UInt32).toUInt64) = 1 from by decide,
      show ((0 : UInt64) - 1) = 0xFFFFFFFFFFFFFFFF from by decide, and_allOnes_uint64,
      toNat_add_of_lt_uint64 (by omega)]
    omega

/-- The loop's operand range: the doubled significand is `54` bits wide. -/
private theorem sqrtPipeline_xu_mem (x : FPR)
    (h1 : 1 ≤ (FPR.decode x).exponent) (h2 : (FPR.decode x).exponent ≤ 2046) :
    2 ^ 52 ≤ (sqrtPipeline x).xu.toNat ∧ (sqrtPipeline x).xu.toNat < 2 ^ 54 := by
  have hbit := (sqrtPipeline_e_spec x h1 h2).1
  have hxu := sqrtPipeline_xuRaw_toNat x
  have hm := FPR.decode_mantissa_lt x
  by_cases hc : (FPR.decode x).exponent % 2 = 0
  · rw [ite_eq_left hc] at hbit
    rw [sqrtPipeline_xu_toNat_of_bit x (by norm_num) hbit]; omega
  · rw [ite_eq_right hc] at hbit
    rw [sqrtPipeline_xu_toNat_of_bit x (by norm_num) hbit]; omega

/-! ### The root word -/

private theorem sqrtPipeline_isqrt (x : FPR) (hxu : (sqrtPipeline x).xu.toNat < 2 ^ 54) :
    (sqrtPipeline x).loopRes.2.1.toNat ^ 2 ≤ 2 ^ 54 * (sqrtPipeline x).xu.toNat
      ∧ 2 ^ 54 * (sqrtPipeline x).xu.toNat
        < ((sqrtPipeline x).loopRes.2.1.toNat + 1) ^ 2 := by
  rw [sqrtPipeline_loopRes]; exact sqrtLoop_isqrt _ hxu

private theorem sqrtPipeline_remainder (x : FPR) (hxu : (sqrtPipeline x).xu.toNat < 2 ^ 54) :
    (sqrtPipeline x).loopRes.2.1.toNat ^ 2 * 2 ^ 54
        + 2 ^ 53 * (sqrtPipeline x).loopRes.1.toNat
      = 2 ^ 108 * (sqrtPipeline x).xu.toNat := by
  rw [sqrtPipeline_loopRes]; exact (sqrtLoop_at_54 _ hxu).1

/-- The root the loop leaves is `54` bits wide. -/
private theorem sqrtPipeline_root_lt (x : FPR) (hxu : (sqrtPipeline x).xu.toNat < 2 ^ 54) :
    (sqrtPipeline x).loopRes.2.1.toNat < 2 ^ 54 := by
  by_contra hcon
  push Not at hcon
  have hsq : ((2 : ℕ) ^ 54) ^ 2 ≤ (sqrtPipeline x).loopRes.2.1.toNat ^ 2 :=
    Nat.pow_le_pow_left hcon 2
  have hle := (sqrtPipeline_isqrt x hxu).1
  have hlt : (2 : ℕ) ^ 54 * (sqrtPipeline x).xu.toNat < 2 ^ 54 * 2 ^ 54 :=
    (Nat.mul_lt_mul_left (Nat.two_pow_pos 54)).mpr hxu
  have he : ((2 : ℕ) ^ 54) ^ 2 = 2 ^ 54 * 2 ^ 54 := by rw [← pow_mul, ← pow_add]
  omega

/-- The root the loop leaves is at least `2 ^ 53`, since the operand is at least `2 ^ 52`. -/
private theorem sqrtPipeline_root_ge (x : FPR) (hlo : 2 ^ 52 ≤ (sqrtPipeline x).xu.toNat)
    (hxu : (sqrtPipeline x).xu.toNat < 2 ^ 54) :
    2 ^ 53 ≤ (sqrtPipeline x).loopRes.2.1.toNat := by
  by_contra hcon
  push Not at hcon
  have hsq : ((sqrtPipeline x).loopRes.2.1.toNat + 1) ^ 2 ≤ ((2 : ℕ) ^ 53) ^ 2 :=
    Nat.pow_le_pow_left (by omega) 2
  have hgt := (sqrtPipeline_isqrt x hxu).2
  have hbig : (2 : ℕ) ^ 54 * 2 ^ 52 ≤ 2 ^ 54 * (sqrtPipeline x).xu.toNat :=
    Nat.mul_le_mul_left _ hlo
  have he : ((2 : ℕ) ^ 53) ^ 2 = 2 ^ 54 * 2 ^ 52 := by rw [← pow_mul, ← pow_add]
  omega

private theorem sqrtPipeline_q1_toNat (x : FPR) (hq : (sqrtPipeline x).loopRes.2.1.toNat < 2 ^ 54) :
    (sqrtPipeline x).q1.toNat
      = 2 * (sqrtPipeline x).loopRes.2.1.toNat
        + (if (sqrtPipeline x).loopRes.1.toNat = 0 then 0 else 1) := by
  have hsl : ((sqrtPipeline x).loopRes.2.1 <<< 1).toNat
      = 2 * (sqrtPipeline x).loopRes.2.1.toNat := by
    rw [toNat_shiftLeft_one]; omega
  rw [sqrtPipeline_q1_eq,
    or_bit_of_even (by rw [hsl]; omega) (by rw [or_neg_shiftRight_63]; split <;> omega),
    or_neg_shiftRight_63, hsl]

/-- The significand `FPR.sqrt` hands to `FPR.make_z` is normalized. -/
private theorem sqrtPipeline_q1_mem (x : FPR)
    (h1 : 1 ≤ (FPR.decode x).exponent) (h2 : (FPR.decode x).exponent ≤ 2046) :
    2 ^ 54 ≤ (sqrtPipeline x).q1.toNat ∧ (sqrtPipeline x).q1.toNat < 2 ^ 55 := by
  obtain ⟨hlo, hhi⟩ := sqrtPipeline_xu_mem x h1 h2
  have hq := sqrtPipeline_root_lt x hhi
  have hq' := sqrtPipeline_root_ge x hlo hhi
  rw [sqrtPipeline_q1_toNat x hq]
  split <;> omega

/-! ### The flush-to-zero guard is inactive on a normal operand -/

private theorem sqrtPipeline_q2_eq_q1 (x : FPR)
    (h1 : 1 ≤ (FPR.decode x).exponent) (h2 : (FPR.decode x).exponent ≤ 2046) :
    (sqrtPipeline x).q2 = (sqrtPipeline x).q1 := by
  have hex := sqrtPipeline_exRaw_toNat x
  have hadd : ((sqrtPipeline x).ex_ + 0x7FF).toNat = (FPR.decode x).exponent + 2047 := by
    rw [UInt32.toNat_add, show (0x7FF : UInt32).toNat = 2047 from by decide]
    omega
  have hsh : (((sqrtPipeline x).ex_ + 0x7FF) >>> 11) = 1 := by
    rw [← UInt32.toNat_inj, UInt32.toNat_shiftRight,
      show (11 : UInt32).toNat % 32 = 11 from by decide, Nat.shiftRight_eq_div_pow, hadd,
      show (1 : UInt32).toNat = 1 from rfl]
    omega
  rw [sqrtPipeline_q2_eq, hsh, show ((1 : UInt32).toUInt64) = 1 from by decide,
    show ((0 : UInt64) - 1) = 0xFFFFFFFFFFFFFFFF from by decide, and_allOnes_uint64]

/-! ### The exact square root, in the scale `FPR.sqrt`'s exponent field uses -/

/-- Both exponent parities collapse to one formula: the operand is exactly `xu * 2 ^ (2 e - 52)`,
with `xu` the (possibly doubled) significand and `e` the halved exponent. -/
private theorem sqrtPipeline_toReal_eq (x : FPR) (ha' : FPR.IsNormal x) (ha : 0 ≤ toReal x)
    (h1 : 1 ≤ (FPR.decode x).exponent) (h2 : (FPR.decode x).exponent ≤ 2046) :
    toReal x = ((sqrtPipeline x).xu.toNat : ℝ)
      * (2 : ℝ) ^ (2 * (sqrtPipeline x).e.toInt - 52) := by
  obtain ⟨hbit, he⟩ := sqrtPipeline_e_spec x h1 h2
  have habs : |toReal x| = ((sqrtPipeline x).xu_.toNat : ℝ)
      * (2 : ℝ) ^ (((FPR.decode x).exponent : ℤ) - 1075) := by
    rw [sqrtPipeline_xuRaw, significand_pack_toNat]
    change |(FPR.decode x).toReal| = _
    rw [abs_toReal_eq_significand_mul_two_zpow ha'.1 ha'.2]
    unfold FPR.Bits.significand
    rw [ite_eq_right ha'.1]
  rw [← abs_of_nonneg ha, habs]
  by_cases hc : (FPR.decode x).exponent % 2 = 0
  · rw [ite_eq_left hc] at hbit he
    rw [sqrtPipeline_xu_toNat_of_bit x (by norm_num) hbit,
      show ((FPR.decode x).exponent : ℤ) - 1075 = (2 * (sqrtPipeline x).e.toInt - 52) + 1 by omega,
      zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0), zpow_one]
    push_cast
    ring
  · rw [ite_eq_right hc] at hbit he
    rw [sqrtPipeline_xu_toNat_of_bit x (by norm_num) hbit,
      show ((FPR.decode x).exponent : ℤ) - 1075 = 2 * (sqrtPipeline x).e.toInt - 52 by omega]
    push_cast
    ring

/-- The exact square root, on the scale the assembled exponent field `e' = e - 54` uses. -/
private theorem sqrtPipeline_sqrt_toReal (x : FPR) (ha' : FPR.IsNormal x) (ha : 0 ≤ toReal x)
    (h1 : 1 ≤ (FPR.decode x).exponent) (h2 : (FPR.decode x).exponent ≤ 2046) :
    Real.sqrt (toReal x)
      = Real.sqrt (2 ^ 54 * ((sqrtPipeline x).xu.toNat : ℝ))
        * (2 : ℝ) ^ ((sqrtPipeline x).e.toInt - 53) := by
  have hnn : (0 : ℝ) ≤ 2 ^ 54 * ((sqrtPipeline x).xu.toNat : ℝ) := by positivity
  have hRnn : (0 : ℝ) ≤ Real.sqrt (2 ^ 54 * ((sqrtPipeline x).xu.toNat : ℝ))
      * (2 : ℝ) ^ ((sqrtPipeline x).e.toInt - 53) := by positivity
  have e1 : ((2 : ℝ) ^ ((sqrtPipeline x).e.toInt - 53)) ^ 2
      = (2 : ℝ) ^ (2 * (sqrtPipeline x).e.toInt - 106) := by
    rw [← zpow_natCast ((2 : ℝ) ^ ((sqrtPipeline x).e.toInt - 53)) 2, ← zpow_mul]
    congr 1
    push_cast
    ring
  have e2 : (2 : ℝ) ^ (54 : ℕ) * (2 : ℝ) ^ (2 * (sqrtPipeline x).e.toInt - 106)
      = (2 : ℝ) ^ (2 * (sqrtPipeline x).e.toInt - 52) := by
    rw [two_pow_mul_zpow]
    congr 1
    push_cast
    ring
  have hsq : (Real.sqrt (2 ^ 54 * ((sqrtPipeline x).xu.toNat : ℝ))
      * (2 : ℝ) ^ ((sqrtPipeline x).e.toInt - 53)) ^ 2 = toReal x := by
    rw [mul_pow, Real.sq_sqrt hnn, e1, sqrtPipeline_toReal_eq x ha' ha h1 h2, ← e2]
    ring
  rw [← hsq, Real.sqrt_sq hRnn]

/-! ### The real-valued root bracket -/

private theorem sqrtPipeline_real_bracket (x : FPR)
    (h1 : 1 ≤ (FPR.decode x).exponent) (h2 : (FPR.decode x).exponent ≤ 2046) :
    (((sqrtPipeline x).q1.toNat : ℝ) - 1) * 1
        < 2 * Real.sqrt (2 ^ 54 * ((sqrtPipeline x).xu.toNat : ℝ))
      ∧ 2 * Real.sqrt (2 ^ 54 * ((sqrtPipeline x).xu.toNat : ℝ))
        < (((sqrtPipeline x).q1.toNat : ℝ) + 1) * 1 := by
  obtain ⟨hlo, hhi⟩ := sqrtPipeline_xu_mem x h1 h2
  have hq := sqrtPipeline_root_lt x hhi
  have hnn : (0 : ℝ) ≤ 2 ^ 54 * ((sqrtPipeline x).xu.toNat : ℝ) := by positivity
  have hcast : ((2 ^ 54 * (sqrtPipeline x).xu.toNat : ℕ) : ℝ)
      = 2 ^ 54 * ((sqrtPipeline x).xu.toNat : ℝ) := by push_cast; ring
  obtain ⟨hb1, hb2⟩ := nat_sqrt_bracket (sqrtPipeline_isqrt x hhi).1 (sqrtPipeline_isqrt x hhi).2
  rw [hcast] at hb1 hb2
  have hq1 := sqrtPipeline_q1_toNat x hq
  have hrem := sqrtPipeline_remainder x hhi
  by_cases hz : (sqrtPipeline x).loopRes.1.toNat = 0
  · rw [ite_eq_left hz] at hq1
    have hexact : (sqrtPipeline x).loopRes.2.1.toNat ^ 2 * 2 ^ 54
        = (2 ^ 54 * (sqrtPipeline x).xu.toNat) * 2 ^ 54 := by
      rw [show (2 ^ 54 * (sqrtPipeline x).xu.toNat) * 2 ^ 54 = 2 ^ 108 * (sqrtPipeline x).xu.toNat
        from by ring, ← hrem, hz]
      ring
    have hroot : (sqrtPipeline x).loopRes.2.1.toNat ^ 2 = 2 ^ 54 * (sqrtPipeline x).xu.toNat :=
      Nat.eq_of_mul_eq_mul_right (Nat.two_pow_pos 54) hexact
    have hR : Real.sqrt (2 ^ 54 * ((sqrtPipeline x).xu.toNat : ℝ))
        = ((sqrtPipeline x).loopRes.2.1.toNat : ℝ) := by
      rw [← hcast, ← hroot]
      push_cast
      exact Real.sqrt_sq (by positivity)
    rw [hq1, hR]
    push_cast
    constructor <;> linarith
  · rw [ite_eq_right hz] at hq1
    have hstrict : (sqrtPipeline x).loopRes.2.1.toNat ^ 2 * 2 ^ 54
        < (2 ^ 54 * (sqrtPipeline x).xu.toNat) * 2 ^ 54 := by
      rw [show (2 ^ 54 * (sqrtPipeline x).xu.toNat) * 2 ^ 54 = 2 ^ 108 * (sqrtPipeline x).xu.toNat
        from by ring, ← hrem]
      have : 0 < 2 ^ 53 * (sqrtPipeline x).loopRes.1.toNat :=
        Nat.mul_pos (Nat.two_pow_pos 53) (Nat.pos_of_ne_zero hz)
      omega
    have hroot : (sqrtPipeline x).loopRes.2.1.toNat ^ 2 < 2 ^ 54 * (sqrtPipeline x).xu.toNat :=
      Nat.lt_of_mul_lt_mul_right hstrict
    have hrootR : (((sqrtPipeline x).loopRes.2.1.toNat : ℝ)) ^ 2
        < 2 ^ 54 * ((sqrtPipeline x).xu.toNat : ℝ) := by
      rw [← hcast]
      exact_mod_cast hroot
    have hS : Real.sqrt (2 ^ 54 * ((sqrtPipeline x).xu.toNat : ℝ)) ^ 2
        = 2 ^ 54 * ((sqrtPipeline x).xu.toNat : ℝ) := Real.sq_sqrt hnn
    have hSnn : (0 : ℝ) ≤ Real.sqrt (2 ^ 54 * ((sqrtPipeline x).xu.toNat : ℝ)) :=
      Real.sqrt_nonneg _
    have hlt : ((sqrtPipeline x).loopRes.2.1.toNat : ℝ)
        < Real.sqrt (2 ^ 54 * ((sqrtPipeline x).xu.toNat : ℝ)) := by nlinarith
    rw [hq1]
    push_cast
    constructor <;> linarith

private theorem sqrtPipeline_key (x : FPR)
    (h1 : 1 ≤ (FPR.decode x).exponent) (h2 : (FPR.decode x).exponent ≤ 2046) :
    (2 : ℝ) ^ (53 : ℕ) * 1 + 1 ≤ 2 * Real.sqrt (2 ^ 54 * ((sqrtPipeline x).xu.toNat : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := sqrtPipeline_xu_mem x h1 h2
  have hq' := sqrtPipeline_root_ge x hlo hhi
  have hcast : ((2 ^ 54 * (sqrtPipeline x).xu.toNat : ℕ) : ℝ)
      = 2 ^ 54 * ((sqrtPipeline x).xu.toNat : ℝ) := by push_cast; ring
  obtain ⟨hb1, -⟩ := nat_sqrt_bracket (sqrtPipeline_isqrt x hhi).1 (sqrtPipeline_isqrt x hhi).2
  rw [hcast] at hb1
  have hqR : (2 : ℝ) ^ (53 : ℕ) ≤ ((sqrtPipeline x).loopRes.2.1.toNat : ℝ) := by
    exact_mod_cast hq'
  have hone : (1 : ℝ) ≤ (2 : ℝ) ^ (53 : ℕ) := one_le_pow₀ (by norm_num)
  linarith

/-! ### The bound -/

/-- Relative error bound for `FPR.sqrt`, on a normal, nonnegative operand. Unlike `add_error` /
`mul_error` / `div_error`, no separate magnitude-range hypothesis on the exact result is needed:
the square root of a value already bracketed in `[FPR.minNormalReal, FPR.maxFiniteReal]` lands in
`[2 ^ (-511), 2 ^ 512]`, hundreds of bits inside that same window on both ends, so a normal operand
can never drive `FPR.sqrt` to overflow or underflow. -/
private theorem sqrt_error_of_isNormal (a : FPR) (ha' : FPR.IsNormal a) (ha : 0 ≤ toReal a) :
    |toReal (FPR.sqrt a) - Real.sqrt (toReal a)| ≤
    (2 : ℝ) ^ (-(52 : ℤ)) * Real.sqrt (toReal a) := by
  have h1 : 1 ≤ (FPR.decode a).exponent := Nat.one_le_iff_ne_zero.mpr ha'.1
  have h2 : (FPR.decode a).exponent ≤ 2046 := by
    have := FPR.decode_exponent_lt a; have := ha'.2; omega
  obtain ⟨hm1, hm2⟩ := sqrtPipeline_q1_mem a h1 h2
  obtain ⟨helo, hehi⟩ := sqrtPipeline_e_mem a h1 h2
  have he' := sqrtPipeline_e'_toInt a h1 h2
  have hq2 := sqrtPipeline_q2_eq_q1 a h1 h2
  have hc : (0 : ℝ) < (2 : ℝ) ^ ((sqrtPipeline a).e.toInt - 54) := zpow_pos (by norm_num) _
  -- the rounding step
  have hMV : |toReal (FPR.sqrt a) - 1 * (((sqrtPipeline a).q1.toNat : ℝ) * 1
        * (2 : ℝ) ^ ((sqrtPipeline a).e.toInt - 54))|
      ≤ (2 : ℝ) ^ (-(53 : ℤ)) * |1 * (((sqrtPipeline a).q1.toNat : ℝ) * 1
        * (2 : ℝ) ^ ((sqrtPipeline a).e.toInt - 54))| := by
    have h := abs_toRealBits_make_z_sub_le 0 (sqrtPipeline a).e' (sqrtPipeline a).q2
      (by decide) (by omega) (by omega) (by rw [hq2]; exact hm1) (by rw [hq2]; exact hm2)
    have hsq : toRealBits (make_z 0 (sqrtPipeline a).e' (sqrtPipeline a).q2)
        = toReal (FPR.sqrt a) := by rw [sqrt_eq_make_z]; rfl
    have hform : (if ((0 : UInt64)).toNat = 1 then (-1 : ℝ) else 1)
        * (((sqrtPipeline a).q2.toNat : ℝ)) * (2 : ℝ) ^ ((sqrtPipeline a).e'.toInt)
        = 1 * (((sqrtPipeline a).q1.toNat : ℝ) * 1
            * (2 : ℝ) ^ ((sqrtPipeline a).e.toInt - 54)) := by
      rw [ite_eq_right (by decide : ¬ ((0 : UInt64)).toNat = 1), hq2, he']
      ring
    rw [hsq, hform] at h
    exact h
  -- the exact root, in the same scale
  have hPc : (1 : ℝ) * ((2 * Real.sqrt (2 ^ 54 * ((sqrtPipeline a).xu.toNat : ℝ)))
      * (2 : ℝ) ^ ((sqrtPipeline a).e.toInt - 54)) = Real.sqrt (toReal a) := by
    rw [sqrtPipeline_sqrt_toReal a ha' ha h1 h2,
      show ((sqrtPipeline a).e.toInt - 53) = 1 + ((sqrtPipeline a).e.toInt - 54) by ring,
      zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0), zpow_one]
    ring
  obtain ⟨hbr1, hbr2⟩ := sqrtPipeline_real_bracket a h1 h2
  have key := mul_error_combine (M := toReal (FPR.sqrt a)) (σ := 1) (K := 1)
    (W := ((sqrtPipeline a).q1.toNat : ℝ))
    (P := 2 * Real.sqrt (2 ^ 54 * ((sqrtPipeline a).xu.toNat : ℝ)))
    (c := (2 : ℝ) ^ ((sqrtPipeline a).e.toInt - 54))
    (Or.inl rfl) hc (by positivity) one_pos hMV hbr1 hbr2 (sqrtPipeline_key a h1 h2)
  rw [hPc, abs_of_nonneg (Real.sqrt_nonneg _)] at key
  exact key

/-- Closure for `FPR.sqrt` on normal operands.

The square root of a normal value cannot cancel, so the result is always normal. It is also the
one operation whose no-carry obligation is vacuous: `sqrtPipeline`'s exponent lands in
`[-565, 457]`, five hundred bits below the `969` at which a rounding carry could reach the
non-finite marker. -/
private theorem sqrt_isNormalOrZero_of_isNormal (a : FPR) (ha' : FPR.IsNormal a) :
    FPR.IsNormalOrZero (FPR.sqrt a) := by
  have h1 : 1 ≤ (FPR.decode a).exponent := Nat.one_le_iff_ne_zero.mpr ha'.1
  have h2 : (FPR.decode a).exponent ≤ 2046 := by
    have := FPR.decode_exponent_lt a; have := ha'.2; omega
  obtain ⟨hm1, hm2⟩ := sqrtPipeline_q1_mem a h1 h2
  obtain ⟨helo, hehi⟩ := sqrtPipeline_e_mem a h1 h2
  have he' := sqrtPipeline_e'_toInt a h1 h2
  have hq2 := sqrtPipeline_q2_eq_q1 a h1 h2
  have hmk : FPR.sqrt a = make 0 (sqrtPipeline a).e' (sqrtPipeline a).q2 := by
    rw [sqrt_eq_make_z,
      FPR.make_z_eq_make _ _ _ (by rw [hq2]; exact hm1) (by rw [hq2]; exact hm2)]
  refine Or.inl ?_
  rw [hmk]
  exact FPR.isNormal_make _ _ _ (by decide) (by omega) (by omega)
    (by rw [hq2]; exact hm1) (by rw [hq2]; exact hm2) (fun h => absurd h (by omega))

/-- **`FPR.sqrt` flushes to `+0` on a zero encoding.** -/
private theorem sqrt_eq_zero_of_exponent_eq_zero (a : FPR) (h : (FPR.decode a).exponent = 0) :
    FPR.sqrt a = 0 := by
  have hex : (sqrtPipeline a).ex_ = 0 := by
    rw [← UInt32.toNat_inj, sqrtPipeline_exRaw_toNat, h]; rfl
  have hq2 : (sqrtPipeline a).q2 = 0 := by
    rw [sqrtPipeline_q2_eq, hex, show (((0 : UInt32) + 0x7FF) >>> 11) = 0 from by decide]
    simp
  rw [sqrt_eq_make_z, hq2, make_z_of_zero]
  decide

theorem sqrt_error (a : FPR) (ha : FPR.IsNormalOrZero a) (h0 : 0 ≤ toReal a) :
    |toReal (FPR.sqrt a) - Real.sqrt (toReal a)| ≤
    (2 : ℝ) ^ (-(52 : ℤ)) * Real.sqrt (toReal a) := by
  rcases ha with ha | ha
  · exact sqrt_error_of_isNormal a ha h0
  · rw [sqrt_eq_zero_of_exponent_eq_zero a ha.1, toReal_eq_zero_of_isZero isZero_zero,
      toReal_eq_zero_of_isZero ha, Real.sqrt_zero, sub_zero, abs_zero]
    positivity

theorem sqrt_isNormalOrZero (a : FPR) (ha : FPR.IsNormalOrZero a) (_h0 : 0 ≤ toReal a) :
    FPR.IsNormalOrZero (FPR.sqrt a) := by
  rcases ha with ha | ha
  · exact sqrt_isNormalOrZero_of_isNormal a ha
  · exact Or.inr (by rw [sqrt_eq_zero_of_exponent_eq_zero a ha.1]; exact isZero_zero)

end

end Falcon.Concrete.FPRBridge
