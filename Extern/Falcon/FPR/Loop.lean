/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

import all LatticeCrypto.Falcon.Concrete.FPR
import all Extern.Falcon.FPR.Common
public import LatticeCrypto.Falcon.Concrete.FPR
public import Extern.Falcon.FPR.Common

/-!
# The loop pipelines of `FPR.div` and `FPR.sqrt`

Trades the `for` loops of the two digit-recurrence kernels for `Nat.iterate`, and names the
`FPR.sqrt` pipeline fields and the loop-step bit identities both proofs use. The loops are
reasoned about by induction on an invariant, never by kernel evaluation.
-/

public section

namespace Falcon.Concrete.FPRBridge

open Falcon.Concrete.FPR

noncomputable section

/-- A `for _ in [a:b]` loop whose body ignores the index is iteration of that body. -/
theorem forIn_range'_eq_iterate {α : Type} (f : α → α) :
    ∀ (n s step : ℕ) (init : α),
      (forIn (List.range' s n step) init (fun _ b => pure (ForInStep.yield (f b))) : Id α)
        = f^[n] init := by
  intro n
  induction n with
  | zero => intro s step init; rfl
  | succ k ih =>
    intro s step init
    rw [List.range'_succ]
    simp only [List.forIn_cons]
    rw [Function.iterate_succ_apply]
    exact ih (s + step) step (f init)

/-- A `for` loop over `[0:n]` that ignores its index is the `n`-fold iterate of its body. -/
theorem forIn_range_eq_iterate {α : Type} (n : ℕ) (init : α) (f : α → α) :
    (forIn [0:n] init (fun _ b => pure (ForInStep.yield (f b))) : Id α) = f^[n] init := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  simpa using forIn_range'_eq_iterate f _ _ _ init

/-- The extended significand of any word: the mantissa with the implicit leading bit folded in.
Shared by the `mul`, `div` and `sqrt` pipelines. -/
private theorem significand_pack_toNat (w : FPR) :
    ((w &&& M52) ||| ((1 : UInt64) <<< 52)).toNat = (FPR.decode w).mantissa + 2 ^ 52 := by
  rw [UInt64.toNat_or, toNat_and_M52_eq_mantissa,
    show ((1 : UInt64) <<< 52).toNat = 2 ^ 52 from by decide]
  exact or_two_pow_add_of_lt _ 52 (FPR.decode_mantissa_lt w)

/-- One iteration of `FPR.sqrt`'s digit-by-digit loop, over the state `(x, q, s, r)`. -/
private def sqrtStep (v : UInt64 × UInt64 × UInt64 × UInt64) :
    UInt64 × UInt64 × UInt64 × UInt64 :=
  let xu' := v.1
  let q_ := v.2.1
  let s_ := v.2.2.1
  let r := v.2.2.2
  let t := s_ + r
  let b := (xu' - t) >>> 63 - 1
  let s_ := s_ + (b &&& r <<< 1)
  let xu' := xu' - (t &&& b)
  let q_ := q_ + (r &&& b)
  let xu' := xu' <<< 1
  let r := r >>> 1
  (xu', q_, s_, r)

private structure SqrtPipeline where
  xu_ : UInt64
  ex_ : UInt32
  e_ : Int32
  xu : UInt64
  e : Int32
  /-- The state `(x, q, s, r)` left by the digit-by-digit loop. -/
  loopRes : UInt64 × UInt64 × UInt64 × UInt64
  /-- The root, doubled and with its final sticky bit folded in. -/
  q1 : UInt64
  e' : Int32
  /-- The root after the zero-operand flush guard. -/
  q2 : UInt64

private def sqrtPipeline (x : FPR) : SqrtPipeline :=
  let xu_ : UInt64 := (x &&& M52) ||| ((1 : UInt64) <<< 52)
  let ex_ := (x >>> 52).toUInt32 &&& 0x7FF
  let e_ : Int32 := ex_.toInt32 - 1023
  let xu := xu_ + (xu_ &&& (0 - (e_.toUInt32 &&& 1).toUInt64))
  let e := (fpr_arsh32 e_.toUInt32 1).toInt32
  let loopRes : UInt64 × UInt64 × UInt64 × UInt64 :=
    (forIn [0:54] (xu <<< 1, (0 : UInt64), (0 : UInt64), (1 : UInt64) <<< 53)
      (fun _ v => pure (ForInStep.yield (sqrtStep v)))
      : Id (UInt64 × UInt64 × UInt64 × UInt64))
  let q1 := (loopRes.2.1 <<< 1) ||| ((loopRes.1 ||| (0 - loopRes.1)) >>> 63)
  let e' := e - 54
  let q2 := q1 &&& ((0 : UInt64) - ((ex_ + 0x7FF) >>> 11).toUInt64)
  { xu_, ex_, e_, xu, e, loopRes, q1, e', q2 }

/-- `FPR.sqrt` is the final assembly call `make_z` over two fields of `sqrtPipeline`. -/
private theorem sqrt_eq_make_z (x : FPR) :
    FPR.sqrt x = make_z 0 (sqrtPipeline x).e' (sqrtPipeline x).q2 :=
  rfl

private theorem sqrtPipeline_loopRes (x : FPR) :
    (sqrtPipeline x).loopRes
      = sqrtStep^[54] ((sqrtPipeline x).xu <<< 1, 0, 0, (1 : UInt64) <<< 53) :=
  forIn_range_eq_iterate _ _ _

/-- Generalised comparison mask: all-ones exactly when `c ≤ a`, zero otherwise. Same shape as
`divStep_mask`, but with bounds tailored to the square-root loop's operands. -/
private theorem sub_mask_of_lt (a c : UInt64) (ha : a.toNat < 2 ^ 63) (hc : c.toNat < 2 ^ 63) :
    ((a - c) >>> 63) - 1 = if c.toNat ≤ a.toNat then (0 : UInt64) - 1 else 0 := by
  by_cases h : c.toNat ≤ a.toNat
  · rw [ite_eq_left h]
    have hsub : (a - c).toNat = a.toNat - c.toNat := toNat_sub_of_le_uint64 a c h
    have hsh : ((a - c) >>> 63) = 0 := by
      rw [← UInt64.toNat_inj, toNat_shiftRight_63_uint64, hsub]
      simp only [UInt64.toNat_ofNat]
      omega
    rw [hsh]
  · rw [ite_eq_right h]
    push Not at h
    have hsub : (a - c).toNat = 2 ^ 64 - (c.toNat - a.toNat) := by
      rw [UInt64.toNat_sub]
      have := c.toNat_lt_size
      omega
    have hsh : ((a - c) >>> 63) = 1 := by
      rw [← UInt64.toNat_inj, toNat_shiftRight_63_uint64, hsub]
      simp only [UInt64.toNat_ofNat]
      omega
    rw [hsh]
    decide

private theorem uint64_zero_and (w : UInt64) : (0 : UInt64) &&& w = 0 := by
  rw [← UInt64.toNat_inj, UInt64.toNat_and]; simp

/-- The loop's closing sticky test: `r ||| (0 - r)` has its top bit set exactly when `r` is
nonzero, since one of `r` and its two's-complement negation always does. -/
private theorem or_neg_shiftRight_63 (r : UInt64) :
    ((r ||| (0 - r)) >>> 63).toNat = if r.toNat = 0 then 0 else 1 := by
  rw [toNat_shiftRight_63_uint64, UInt64.toNat_or]
  by_cases h : r.toNat = 0
  · rw [ite_eq_left h]
    have hr : r = 0 := by rw [← UInt64.toNat_inj, h]; rfl
    rw [hr]
    simp
  · rw [ite_eq_right h]
    have hneg : ((0 : UInt64) - r).toNat = 2 ^ 64 - r.toNat := by
      rw [UInt64.toNat_sub]
      have := r.toNat_lt_size
      simp only [UInt64.toNat_ofNat]
      omega
    have hlt := r.toNat_lt_size
    have hbig : 2 ^ 63 ≤ r.toNat ||| ((0 : UInt64) - r).toNat := by
      rcases Nat.lt_or_ge r.toNat (2 ^ 63) with hc | hc
      · refine le_trans ?_ (Nat.right_le_or)
        rw [hneg]; omega
      · exact le_trans hc (Nat.left_le_or)
    have hsmall : r.toNat ||| ((0 : UInt64) - r).toNat < 2 ^ 64 :=
      Nat.or_lt_two_pow hlt (by rw [hneg]; omega)
    omega

private theorem or_bit_of_even {q b : UInt64} (hqe : q.toNat % 2 = 0) (hb : b.toNat ≤ 1) :
    (q ||| b).toNat = q.toNat + b.toNat := by
  rw [UInt64.toNat_or]
  interval_cases h : b.toNat
  · rw [Nat.or_zero]; omega
  · rw [or_one_eq]; omega

end

end Falcon.Concrete.FPRBridge
