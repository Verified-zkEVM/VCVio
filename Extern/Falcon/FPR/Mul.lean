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
# Correct rounding of `FPR.mul`

The `FPR.mul` pipeline read field by field — the 25-bit limb split, the four partial products
and their carry chain, the 50-bit sticky fold — and the resulting bound `mul_error` together with
the closure fact `mul_isNormalOrZero`.
-/

public section

namespace Falcon.Concrete.FPRBridge

open Falcon.Concrete.FPR

noncomputable section

/-! ## The `FPR.mul` pipeline, named field by field

`FPR.mul` is a straight-line chain of `let`s, so — exactly as for `FPR.add` — it can be pinned to
the kernel term by `rfl`. `MulPipeline` names every intermediate of that chain as a structure
field, computed by the same `let`-chain as `FPR.mul`'s body
(`LatticeCrypto/Falcon/Concrete/FPR.lean`); `mul_eq_make` then identifies `FPR.mul` with the final
assembly call over three of those fields. Each field-projection equation below is also `rfl`. -/

/-- Every named intermediate of `FPR.mul`'s pipeline, in the order `FPR.mul` computes them. -/
private structure MulPipeline where
  /-- The extended significand of `x`, with the implicit leading bit folded in at position `52`. -/
  xu : UInt64
  /-- The extended significand of `y`, with the implicit leading bit folded in at position `52`. -/
  yu : UInt64
  /-- Low `25`-bit limb of `xu`. -/
  x0 : UInt32
  /-- High limb of `xu` (`28` bits). -/
  x1 : UInt32
  /-- Low `25`-bit limb of `yu`. -/
  y0 : UInt32
  /-- High limb of `yu` (`28` bits). -/
  y1 : UInt32
  w0 : UInt64
  /-- Low `25`-bit limb of the product. -/
  z0 : UInt32
  z1_ : UInt32
  w1 : UInt64
  z1 : UInt32
  z2_ : UInt32
  w2 : UInt64
  /-- Second `25`-bit limb of the product, before its carry is propagated. -/
  z1' : UInt32
  z2 : UInt32
  zu_ : UInt64
  z2' : UInt32
  /-- The product's high half: `xu * yu` shifted right by `50`. -/
  zu : UInt64
  /-- `zu` with the `50`-bit sticky bit folded into its low bit. -/
  zu' : UInt64
  /-- The renormalising right-shift count, `1` exactly when the product carried into bit `55`. -/
  es : UInt64
  /-- The renormalised significand handed to `make`. -/
  zu'' : UInt64
  /-- The biased exponent field of `x`. -/
  ex : UInt32
  /-- The biased exponent field of `y`. -/
  ey : UInt32
  e : UInt32
  /-- The sign of the product. -/
  s : UInt64
  /-- All-ones when either operand's exponent field is zero (the flush-to-zero guard). -/
  dzu : UInt32
  /-- The final exponent handed to `make`. -/
  e' : Int32
  /-- The final significand handed to `make`, after the flush guard. -/
  zu''' : UInt64

/-- The pipeline of `FPR.mul x y`, field by field, computed by the exact same `let`-chain as
`FPR.mul`'s body. -/
private def mulPipeline (x y : FPR) : MulPipeline :=
  let xu : UInt64 := (x &&& M52) ||| ((1 : UInt64) <<< 52)
  let yu : UInt64 := (y &&& M52) ||| ((1 : UInt64) <<< 52)
  let x0 := xu.toUInt32 &&& 0x01FFFFFF
  let x1 := (xu >>> 25).toUInt32
  let y0 := yu.toUInt32 &&& 0x01FFFFFF
  let y1 := (yu >>> 25).toUInt32
  let w0 := x0.toUInt64 * y0.toUInt64
  let z0 := w0.toUInt32 &&& 0x01FFFFFF
  let z1_ := (w0 >>> 25).toUInt32
  let w1 := x0.toUInt64 * y1.toUInt64
  let z1 := z1_ + (w1.toUInt32 &&& 0x01FFFFFF)
  let z2_ := (w1 >>> 25).toUInt32
  let w2 := x1.toUInt64 * y0.toUInt64
  let z1' := z1 + (w2.toUInt32 &&& 0x01FFFFFF)
  let z2 := z2_ + (w2 >>> 25).toUInt32
  let zu_ := x1.toUInt64 * y1.toUInt64
  let z2' := z2 + (z1' >>> 25)
  let zu := zu_ + z2'.toUInt64
  let zu' := zu ||| ((((z0 ||| (z1' &&& 0x01FFFFFF)) + 0x01FFFFFF) >>> 25).toUInt64)
  let es := zu' >>> 55
  let zu'' := (zu' >>> es) ||| (zu' &&& 1)
  let ex := (x >>> 52).toUInt32 &&& 0x7FF
  let ey := (y >>> 52).toUInt32 &&& 0x7FF
  let e := ex + ey - 2100 + es.toUInt32
  let s := (x ^^^ y) >>> 63
  let dzu := tbmask ((ex - 1) ||| (ey - 1))
  let e' : Int32 := (e ^^^ (dzu &&& (e ^^^ ((0 : UInt32) - 1076)))).toInt32
  let zu''' := zu'' &&& ((dzu &&& 1).toUInt64 - 1)
  { xu, yu, x0, x1, y0, y1, w0, z0, z1_, w1, z1, z2_, w2, z1', z2, zu_, z2', zu, zu', es, zu'',
    ex, ey, e, s, dzu, e', zu''' }

/-- `FPR.mul` is the final assembly call `make` applied to three fields of `mulPipeline`. -/
private theorem mul_eq_make (x y : FPR) :
    FPR.mul x y =
      make (mulPipeline x y).s (mulPipeline x y).e' (mulPipeline x y).zu''' :=
  rfl

private theorem mulPipeline_xu (x y : FPR) :
    (mulPipeline x y).xu = (x &&& M52) ||| ((1 : UInt64) <<< 52) := rfl

private theorem mulPipeline_yu (x y : FPR) :
    (mulPipeline x y).yu = (y &&& M52) ||| ((1 : UInt64) <<< 52) := rfl

private theorem mulPipeline_x0 (x y : FPR) :
    (mulPipeline x y).x0 = (mulPipeline x y).xu.toUInt32 &&& 0x01FFFFFF := rfl

private theorem mulPipeline_x1 (x y : FPR) :
    (mulPipeline x y).x1 = ((mulPipeline x y).xu >>> 25).toUInt32 := rfl

private theorem mulPipeline_y0 (x y : FPR) :
    (mulPipeline x y).y0 = (mulPipeline x y).yu.toUInt32 &&& 0x01FFFFFF := rfl

private theorem mulPipeline_y1 (x y : FPR) :
    (mulPipeline x y).y1 = ((mulPipeline x y).yu >>> 25).toUInt32 := rfl

private theorem mulPipeline_w0 (x y : FPR) :
    (mulPipeline x y).w0 = (mulPipeline x y).x0.toUInt64 * (mulPipeline x y).y0.toUInt64 := rfl

private theorem mulPipeline_z0 (x y : FPR) :
    (mulPipeline x y).z0 = (mulPipeline x y).w0.toUInt32 &&& 0x01FFFFFF := rfl

private theorem mulPipeline_z1_ (x y : FPR) :
    (mulPipeline x y).z1_ = ((mulPipeline x y).w0 >>> 25).toUInt32 := rfl

private theorem mulPipeline_w1 (x y : FPR) :
    (mulPipeline x y).w1 = (mulPipeline x y).x0.toUInt64 * (mulPipeline x y).y1.toUInt64 := rfl

private theorem mulPipeline_z1 (x y : FPR) :
    (mulPipeline x y).z1
      = (mulPipeline x y).z1_ + ((mulPipeline x y).w1.toUInt32 &&& 0x01FFFFFF) := rfl

private theorem mulPipeline_z2_ (x y : FPR) :
    (mulPipeline x y).z2_ = ((mulPipeline x y).w1 >>> 25).toUInt32 := rfl

private theorem mulPipeline_w2 (x y : FPR) :
    (mulPipeline x y).w2 = (mulPipeline x y).x1.toUInt64 * (mulPipeline x y).y0.toUInt64 := rfl

private theorem mulPipeline_z1' (x y : FPR) :
    (mulPipeline x y).z1'
      = (mulPipeline x y).z1 + ((mulPipeline x y).w2.toUInt32 &&& 0x01FFFFFF) := rfl

private theorem mulPipeline_z2 (x y : FPR) :
    (mulPipeline x y).z2
      = (mulPipeline x y).z2_ + ((mulPipeline x y).w2 >>> 25).toUInt32 := rfl

private theorem mulPipeline_zu_ (x y : FPR) :
    (mulPipeline x y).zu_ = (mulPipeline x y).x1.toUInt64 * (mulPipeline x y).y1.toUInt64 := rfl

private theorem mulPipeline_z2' (x y : FPR) :
    (mulPipeline x y).z2' = (mulPipeline x y).z2 + ((mulPipeline x y).z1' >>> 25) := rfl

private theorem mulPipeline_zu (x y : FPR) :
    (mulPipeline x y).zu = (mulPipeline x y).zu_ + (mulPipeline x y).z2'.toUInt64 := rfl

private theorem mulPipeline_zu' (x y : FPR) :
    (mulPipeline x y).zu'
      = (mulPipeline x y).zu |||
          (((((mulPipeline x y).z0 ||| ((mulPipeline x y).z1' &&& 0x01FFFFFF))
            + 0x01FFFFFF) >>> 25).toUInt64) := rfl

private theorem mulPipeline_es (x y : FPR) :
    (mulPipeline x y).es = (mulPipeline x y).zu' >>> 55 := rfl

private theorem mulPipeline_zu'' (x y : FPR) :
    (mulPipeline x y).zu''
      = ((mulPipeline x y).zu' >>> (mulPipeline x y).es) ||| ((mulPipeline x y).zu' &&& 1) := rfl

private theorem mulPipeline_ex (x y : FPR) :
    (mulPipeline x y).ex = (x >>> 52).toUInt32 &&& 0x7FF := rfl

private theorem mulPipeline_ey (x y : FPR) :
    (mulPipeline x y).ey = (y >>> 52).toUInt32 &&& 0x7FF := rfl

private theorem mulPipeline_e (x y : FPR) :
    (mulPipeline x y).e
      = (mulPipeline x y).ex + (mulPipeline x y).ey - 2100 + (mulPipeline x y).es.toUInt32 := rfl

private theorem mulPipeline_s (x y : FPR) : (mulPipeline x y).s = (x ^^^ y) >>> 63 := rfl

private theorem mulPipeline_dzu (x y : FPR) :
    (mulPipeline x y).dzu = tbmask (((mulPipeline x y).ex - 1) ||| ((mulPipeline x y).ey - 1)) :=
  rfl

private theorem mulPipeline_e' (x y : FPR) :
    (mulPipeline x y).e'
      = ((mulPipeline x y).e ^^^
          ((mulPipeline x y).dzu &&& ((mulPipeline x y).e ^^^ ((0 : UInt32) - 1076)))).toInt32 :=
  rfl

private theorem mulPipeline_zu''' (x y : FPR) :
    (mulPipeline x y).zu''' =
      (mulPipeline x y).zu'' &&& (((mulPipeline x y).dzu &&& 1).toUInt64 - 1) := rfl

/-! ### Generic word-level helpers for the 25-bit limb split -/

/-- Truncating to `UInt32` and masking to `25` bits reads the low `25` bits of the word. -/
private theorem toNat_low25 (v : UInt64) :
    (v.toUInt32 &&& 0x01FFFFFF).toNat = v.toNat % 2 ^ 25 := by
  have hM : (0x01FFFFFF : UInt32).toNat = 2 ^ 25 - 1 := by decide
  rw [UInt32.toNat_and, hM, Nat.and_two_pow_sub_one_eq_mod,
    show (v.toUInt32).toNat = v.toNat % 2 ^ 32 from rfl,
    Nat.mod_mod_of_dvd _ (by norm_num : (2:ℕ) ^ 25 ∣ 2 ^ 32)]

/-- For a word below `2 ^ 53`, shifting right by `25` lands inside `UInt32`. -/
private theorem toNat_high25 (v : UInt64) (hv : v.toNat < 2 ^ 53) :
    ((v >>> 25).toUInt32).toNat = v.toNat / 2 ^ 25 := by
  have hdiv : v.toNat / 2 ^ 25 < 2 ^ 28 := by
    apply Nat.div_lt_of_lt_mul; omega
  have hsr : (v >>> 25 : UInt64).toNat = v.toNat / 2 ^ 25 := by
    rw [UInt64.toNat_shiftRight, show (25 : UInt64).toNat % 64 = 25 from by decide,
      Nat.shiftRight_eq_div_pow]
  rw [show ((v >>> 25 : UInt64).toUInt32).toNat = (v >>> 25 : UInt64).toNat % 2 ^ 32 from rfl, hsr,
    Nat.mod_eq_of_lt (by omega)]

/-- A `UInt32 × UInt32` product taken in `UInt64` does not wrap. -/
private theorem toNat_mul32 (a b : UInt32) :
    (a.toUInt64 * b.toUInt64).toNat = a.toNat * b.toNat := by
  have ha : a.toNat < 2 ^ 32 := a.toNat_lt_size
  have hb : b.toNat < 2 ^ 32 := b.toNat_lt_size
  have hlt : a.toNat * b.toNat < 2 ^ 64 := by
    calc a.toNat * b.toNat < 2 ^ 32 * 2 ^ 32 := Nat.mul_lt_mul_of_lt_of_lt ha hb
      _ = 2 ^ 64 := by norm_num
  rw [UInt64.toNat_mul, UInt32.toNat_toUInt64, UInt32.toNat_toUInt64, Nat.mod_eq_of_lt hlt]

/-! ### The 25-bit limb identity, as pure arithmetic on `ℕ`

`FPR.mul` splits both `53`-bit significands into a `25`-bit low limb and a `28`-bit high limb,
forms the four partial products, and folds their carries into a single high word `zu` plus two
`25`-bit residues. This states exactly what that carry chain computes, with no machine words
involved; the pipeline lemmas below discharge its hypotheses. -/

private theorem limb_decomp (x0 x1 y0 y1 w0 w1 w2 zu_ z0 z1_ z1 z2_ z1' z2 z2' zu : ℕ)
    (hw0 : w0 = x0 * y0) (hw1 : w1 = x0 * y1) (hw2 : w2 = x1 * y0) (hzu_ : zu_ = x1 * y1)
    (hz0 : z0 = w0 % 2 ^ 25) (hz1_ : z1_ = w0 / 2 ^ 25)
    (hz1 : z1 = z1_ + w1 % 2 ^ 25) (hz2_ : z2_ = w1 / 2 ^ 25)
    (hz1' : z1' = z1 + w2 % 2 ^ 25) (hz2 : z2 = z2_ + w2 / 2 ^ 25)
    (hz2' : z2' = z2 + z1' / 2 ^ 25) (hzu : zu = zu_ + z2') :
    (x1 * 2 ^ 25 + x0) * (y1 * 2 ^ 25 + y0)
      = zu * 2 ^ 50 + (z1' % 2 ^ 25) * 2 ^ 25 + z0 := by
  have expand : (x1 * 2 ^ 25 + x0) * (y1 * 2 ^ 25 + y0)
      = zu_ * 2 ^ 50 + (w1 + w2) * 2 ^ 25 + w0 := by
    subst hw0 hw1 hw2 hzu_; ring
  rw [expand]
  subst hz0 hz1_ hz1 hz2_ hz1' hz2 hz2' hzu
  norm_num
  omega

/-! ### The pipeline's significands and limbs, read as naturals -/

private theorem mulPipeline_xu_toNat (x y : FPR) :
    (mulPipeline x y).xu.toNat = (FPR.decode x).mantissa + 2 ^ 52 := by
  rw [mulPipeline_xu, UInt64.toNat_or, toNat_and_M52_eq_mantissa,
    show ((1 : UInt64) <<< 52).toNat = 2 ^ 52 from by decide]
  exact or_two_pow_add_of_lt _ 52 (FPR.decode_mantissa_lt x)

private theorem mulPipeline_yu_toNat (x y : FPR) :
    (mulPipeline x y).yu.toNat = (FPR.decode y).mantissa + 2 ^ 52 := by
  rw [mulPipeline_yu, UInt64.toNat_or, toNat_and_M52_eq_mantissa,
    show ((1 : UInt64) <<< 52).toNat = 2 ^ 52 from by decide]
  exact or_two_pow_add_of_lt _ 52 (FPR.decode_mantissa_lt y)

private theorem mulPipeline_xu_lt (x y : FPR) : (mulPipeline x y).xu.toNat < 2 ^ 53 := by
  rw [mulPipeline_xu_toNat]; have := FPR.decode_mantissa_lt x; omega

private theorem mulPipeline_yu_lt (x y : FPR) : (mulPipeline x y).yu.toNat < 2 ^ 53 := by
  rw [mulPipeline_yu_toNat]; have := FPR.decode_mantissa_lt y; omega

private theorem mulPipeline_le_xu (x y : FPR) : 2 ^ 52 ≤ (mulPipeline x y).xu.toNat := by
  rw [mulPipeline_xu_toNat]; omega

private theorem mulPipeline_le_yu (x y : FPR) : 2 ^ 52 ≤ (mulPipeline x y).yu.toNat := by
  rw [mulPipeline_yu_toNat]; omega

private theorem mulPipeline_x0_toNat (x y : FPR) :
    (mulPipeline x y).x0.toNat = (mulPipeline x y).xu.toNat % 2 ^ 25 := by
  rw [mulPipeline_x0]; exact toNat_low25 _

private theorem mulPipeline_y0_toNat (x y : FPR) :
    (mulPipeline x y).y0.toNat = (mulPipeline x y).yu.toNat % 2 ^ 25 := by
  rw [mulPipeline_y0]; exact toNat_low25 _

private theorem mulPipeline_x1_toNat (x y : FPR) :
    (mulPipeline x y).x1.toNat = (mulPipeline x y).xu.toNat / 2 ^ 25 := by
  rw [mulPipeline_x1]; exact toNat_high25 _ (mulPipeline_xu_lt x y)

private theorem mulPipeline_y1_toNat (x y : FPR) :
    (mulPipeline x y).y1.toNat = (mulPipeline x y).yu.toNat / 2 ^ 25 := by
  rw [mulPipeline_y1]; exact toNat_high25 _ (mulPipeline_yu_lt x y)

private theorem mulPipeline_x0_lt (x y : FPR) : (mulPipeline x y).x0.toNat < 2 ^ 25 := by
  rw [mulPipeline_x0_toNat]; exact Nat.mod_lt _ (Nat.two_pow_pos _)

private theorem mulPipeline_y0_lt (x y : FPR) : (mulPipeline x y).y0.toNat < 2 ^ 25 := by
  rw [mulPipeline_y0_toNat]; exact Nat.mod_lt _ (Nat.two_pow_pos _)

private theorem mulPipeline_x1_lt (x y : FPR) : (mulPipeline x y).x1.toNat < 2 ^ 28 := by
  rw [mulPipeline_x1_toNat]
  exact Nat.div_lt_of_lt_mul (by have := mulPipeline_xu_lt x y; omega)

private theorem mulPipeline_y1_lt (x y : FPR) : (mulPipeline x y).y1.toNat < 2 ^ 28 := by
  rw [mulPipeline_y1_toNat]
  exact Nat.div_lt_of_lt_mul (by have := mulPipeline_yu_lt x y; omega)

/-! ### The four partial products -/

private theorem mulPipeline_w0_toNat (x y : FPR) :
    (mulPipeline x y).w0.toNat = (mulPipeline x y).x0.toNat * (mulPipeline x y).y0.toNat := by
  rw [mulPipeline_w0]; exact toNat_mul32 _ _

private theorem mulPipeline_w1_toNat (x y : FPR) :
    (mulPipeline x y).w1.toNat = (mulPipeline x y).x0.toNat * (mulPipeline x y).y1.toNat := by
  rw [mulPipeline_w1]; exact toNat_mul32 _ _

private theorem mulPipeline_w2_toNat (x y : FPR) :
    (mulPipeline x y).w2.toNat = (mulPipeline x y).x1.toNat * (mulPipeline x y).y0.toNat := by
  rw [mulPipeline_w2]; exact toNat_mul32 _ _

private theorem mulPipeline_zuTop_toNat (x y : FPR) :
    (mulPipeline x y).zu_.toNat = (mulPipeline x y).x1.toNat * (mulPipeline x y).y1.toNat := by
  rw [mulPipeline_zu_]; exact toNat_mul32 _ _

private theorem mulPipeline_w0_lt (x y : FPR) : (mulPipeline x y).w0.toNat < 2 ^ 50 := by
  rw [mulPipeline_w0_toNat]
  calc (mulPipeline x y).x0.toNat * (mulPipeline x y).y0.toNat < 2 ^ 25 * 2 ^ 25 :=
        Nat.mul_lt_mul_of_lt_of_lt (mulPipeline_x0_lt x y) (mulPipeline_y0_lt x y)
    _ = 2 ^ 50 := by norm_num

private theorem mulPipeline_w1_lt (x y : FPR) : (mulPipeline x y).w1.toNat < 2 ^ 53 := by
  rw [mulPipeline_w1_toNat]
  calc (mulPipeline x y).x0.toNat * (mulPipeline x y).y1.toNat < 2 ^ 25 * 2 ^ 28 :=
        Nat.mul_lt_mul_of_lt_of_lt (mulPipeline_x0_lt x y) (mulPipeline_y1_lt x y)
    _ = 2 ^ 53 := by norm_num

private theorem mulPipeline_w2_lt (x y : FPR) : (mulPipeline x y).w2.toNat < 2 ^ 53 := by
  rw [mulPipeline_w2_toNat]
  calc (mulPipeline x y).x1.toNat * (mulPipeline x y).y0.toNat < 2 ^ 28 * 2 ^ 25 :=
        Nat.mul_lt_mul_of_lt_of_lt (mulPipeline_x1_lt x y) (mulPipeline_y0_lt x y)
    _ = 2 ^ 53 := by norm_num

private theorem mulPipeline_zuTop_lt (x y : FPR) : (mulPipeline x y).zu_.toNat < 2 ^ 56 := by
  rw [mulPipeline_zuTop_toNat]
  calc (mulPipeline x y).x1.toNat * (mulPipeline x y).y1.toNat < 2 ^ 28 * 2 ^ 28 :=
        Nat.mul_lt_mul_of_lt_of_lt (mulPipeline_x1_lt x y) (mulPipeline_y1_lt x y)
    _ = 2 ^ 56 := by norm_num

/-! ### The carry chain

Every addition in `FPR.mul`'s carry chain stays inside its word, so each one denotes plain
addition on `ℕ`. The bounds are slack: the widest intermediate, `z2`, reaches only `2 ^ 29`. -/

private theorem toNat_add32_of_lt {a b : UInt32} (h : a.toNat + b.toNat < 2 ^ 32) :
    (a + b).toNat = a.toNat + b.toNat := by
  rw [UInt32.toNat_add, Nat.mod_eq_of_lt h]

private theorem toNat_shiftRight_25_uint32 (w : UInt32) : (w >>> 25).toNat = w.toNat / 2 ^ 25 := by
  rw [UInt32.toNat_shiftRight, show (25 : UInt32).toNat % 32 = 25 from by decide,
    Nat.shiftRight_eq_div_pow]

private theorem mulPipeline_z0_toNat (x y : FPR) :
    (mulPipeline x y).z0.toNat = (mulPipeline x y).w0.toNat % 2 ^ 25 := by
  rw [mulPipeline_z0]; exact toNat_low25 _

private theorem mulPipeline_z1c_toNat (x y : FPR) :
    (mulPipeline x y).z1_.toNat = (mulPipeline x y).w0.toNat / 2 ^ 25 := by
  rw [mulPipeline_z1_]
  exact toNat_high25 _ (by have := mulPipeline_w0_lt x y; omega)

private theorem mulPipeline_z2c_toNat (x y : FPR) :
    (mulPipeline x y).z2_.toNat = (mulPipeline x y).w1.toNat / 2 ^ 25 := by
  rw [mulPipeline_z2_]; exact toNat_high25 _ (mulPipeline_w1_lt x y)

private theorem mulPipeline_z1c_lt (x y : FPR) : (mulPipeline x y).z1_.toNat < 2 ^ 25 := by
  rw [mulPipeline_z1c_toNat]
  exact Nat.div_lt_of_lt_mul (by have := mulPipeline_w0_lt x y; omega)

private theorem mulPipeline_z2c_lt (x y : FPR) : (mulPipeline x y).z2_.toNat < 2 ^ 28 := by
  rw [mulPipeline_z2c_toNat]
  exact Nat.div_lt_of_lt_mul (by have := mulPipeline_w1_lt x y; omega)

private theorem mulPipeline_z1_toNat (x y : FPR) :
    (mulPipeline x y).z1.toNat
      = (mulPipeline x y).z1_.toNat + (mulPipeline x y).w1.toNat % 2 ^ 25 := by
  rw [mulPipeline_z1]
  have hlow : ((mulPipeline x y).w1.toUInt32 &&& 0x01FFFFFF).toNat
      = (mulPipeline x y).w1.toNat % 2 ^ 25 := toNat_low25 _
  have hb : (mulPipeline x y).w1.toNat % 2 ^ 25 < 2 ^ 25 := Nat.mod_lt _ (Nat.two_pow_pos _)
  rw [toNat_add32_of_lt (by have := mulPipeline_z1c_lt x y; rw [hlow]; omega), hlow]

private theorem mulPipeline_z1_lt (x y : FPR) : (mulPipeline x y).z1.toNat < 2 ^ 26 := by
  rw [mulPipeline_z1_toNat]
  have := mulPipeline_z1c_lt x y
  have : (mulPipeline x y).w1.toNat % 2 ^ 25 < 2 ^ 25 := Nat.mod_lt _ (Nat.two_pow_pos _)
  omega

private theorem mulPipeline_z1'_toNat (x y : FPR) :
    (mulPipeline x y).z1'.toNat
      = (mulPipeline x y).z1.toNat + (mulPipeline x y).w2.toNat % 2 ^ 25 := by
  rw [mulPipeline_z1']
  have hlow : ((mulPipeline x y).w2.toUInt32 &&& 0x01FFFFFF).toNat
      = (mulPipeline x y).w2.toNat % 2 ^ 25 := toNat_low25 _
  have hb : (mulPipeline x y).w2.toNat % 2 ^ 25 < 2 ^ 25 := Nat.mod_lt _ (Nat.two_pow_pos _)
  rw [toNat_add32_of_lt (by have := mulPipeline_z1_lt x y; rw [hlow]; omega), hlow]

private theorem mulPipeline_z1'_lt (x y : FPR) : (mulPipeline x y).z1'.toNat < 2 ^ 27 := by
  rw [mulPipeline_z1'_toNat]
  have := mulPipeline_z1_lt x y
  have : (mulPipeline x y).w2.toNat % 2 ^ 25 < 2 ^ 25 := Nat.mod_lt _ (Nat.two_pow_pos _)
  omega

private theorem mulPipeline_z2_toNat (x y : FPR) :
    (mulPipeline x y).z2.toNat
      = (mulPipeline x y).z2_.toNat + (mulPipeline x y).w2.toNat / 2 ^ 25 := by
  rw [mulPipeline_z2]
  have hhigh : (((mulPipeline x y).w2 >>> 25).toUInt32).toNat
      = (mulPipeline x y).w2.toNat / 2 ^ 25 := toNat_high25 _ (mulPipeline_w2_lt x y)
  have hb : (mulPipeline x y).w2.toNat / 2 ^ 25 < 2 ^ 28 :=
    Nat.div_lt_of_lt_mul (by have := mulPipeline_w2_lt x y; omega)
  rw [toNat_add32_of_lt (by have := mulPipeline_z2c_lt x y; rw [hhigh]; omega), hhigh]

private theorem mulPipeline_z2_lt (x y : FPR) : (mulPipeline x y).z2.toNat < 2 ^ 29 := by
  rw [mulPipeline_z2_toNat]
  have := mulPipeline_z2c_lt x y
  have : (mulPipeline x y).w2.toNat / 2 ^ 25 < 2 ^ 28 :=
    Nat.div_lt_of_lt_mul (by have := mulPipeline_w2_lt x y; omega)
  omega

private theorem mulPipeline_z2'_toNat (x y : FPR) :
    (mulPipeline x y).z2'.toNat
      = (mulPipeline x y).z2.toNat + (mulPipeline x y).z1'.toNat / 2 ^ 25 := by
  rw [mulPipeline_z2']
  have hsh : ((mulPipeline x y).z1' >>> 25).toNat = (mulPipeline x y).z1'.toNat / 2 ^ 25 :=
    toNat_shiftRight_25_uint32 _
  have hb : (mulPipeline x y).z1'.toNat / 2 ^ 25 < 2 ^ 2 :=
    Nat.div_lt_of_lt_mul (by have := mulPipeline_z1'_lt x y; omega)
  rw [toNat_add32_of_lt (by have := mulPipeline_z2_lt x y; rw [hsh]; omega), hsh]

private theorem mulPipeline_z2'_lt (x y : FPR) : (mulPipeline x y).z2'.toNat < 2 ^ 30 := by
  rw [mulPipeline_z2'_toNat]
  have := mulPipeline_z2_lt x y
  have : (mulPipeline x y).z1'.toNat / 2 ^ 25 < 2 ^ 2 :=
    Nat.div_lt_of_lt_mul (by have := mulPipeline_z1'_lt x y; omega)
  omega

private theorem mulPipeline_zu_toNat (x y : FPR) :
    (mulPipeline x y).zu.toNat
      = (mulPipeline x y).zu_.toNat + (mulPipeline x y).z2'.toNat := by
  rw [mulPipeline_zu, UInt64.toNat_add, UInt32.toNat_toUInt64]
  refine Nat.mod_eq_of_lt ?_
  have := mulPipeline_zuTop_lt x y
  have := mulPipeline_z2'_lt x y
  omega

/-! ### What the carry chain computes: the exact product, split at bit `50` -/

private theorem mulPipeline_product_eq (x y : FPR) :
    (mulPipeline x y).xu.toNat * (mulPipeline x y).yu.toNat
      = (mulPipeline x y).zu.toNat * 2 ^ 50
        + ((mulPipeline x y).z1'.toNat % 2 ^ 25) * 2 ^ 25 + (mulPipeline x y).z0.toNat := by
  have hx : (mulPipeline x y).xu.toNat
      = (mulPipeline x y).x1.toNat * 2 ^ 25 + (mulPipeline x y).x0.toNat := by
    rw [mulPipeline_x1_toNat, mulPipeline_x0_toNat]; omega
  have hy : (mulPipeline x y).yu.toNat
      = (mulPipeline x y).y1.toNat * 2 ^ 25 + (mulPipeline x y).y0.toNat := by
    rw [mulPipeline_y1_toNat, mulPipeline_y0_toNat]; omega
  rw [hx, hy]
  exact limb_decomp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (mulPipeline_w0_toNat x y) (mulPipeline_w1_toNat x y) (mulPipeline_w2_toNat x y)
    (mulPipeline_zuTop_toNat x y) (mulPipeline_z0_toNat x y) (mulPipeline_z1c_toNat x y)
    (mulPipeline_z1_toNat x y) (mulPipeline_z2c_toNat x y) (mulPipeline_z1'_toNat x y)
    (mulPipeline_z2_toNat x y) (mulPipeline_z2'_toNat x y) (mulPipeline_zu_toNat x y)

private theorem mulPipeline_residue_lt (x y : FPR) :
    ((mulPipeline x y).z1'.toNat % 2 ^ 25) * 2 ^ 25 + (mulPipeline x y).z0.toNat < 2 ^ 50 := by
  have h1 : (mulPipeline x y).z1'.toNat % 2 ^ 25 < 2 ^ 25 := Nat.mod_lt _ (Nat.two_pow_pos _)
  have h2 : (mulPipeline x y).z0.toNat < 2 ^ 25 := by
    rw [mulPipeline_z0_toNat]; exact Nat.mod_lt _ (Nat.two_pow_pos _)
  have h3 : ((mulPipeline x y).z1'.toNat % 2 ^ 25) * 2 ^ 25 ≤ (2 ^ 25 - 1) * 2 ^ 25 :=
    Nat.mul_le_mul_right _ (by omega)
  have h4 : (2 ^ 25 - 1) * 2 ^ 25 = 2 ^ 50 - 2 ^ 25 := by norm_num
  omega

/-- The high word `zu` is the exact product shifted right by `50`. -/
private theorem mulPipeline_zu_eq_div (x y : FPR) :
    (mulPipeline x y).zu.toNat
      = (mulPipeline x y).xu.toNat * (mulPipeline x y).yu.toNat / 2 ^ 50 := by
  have h := mulPipeline_product_eq x y
  have hlt := mulPipeline_residue_lt x y
  omega

/-- The two `25`-bit residues carry exactly the product's low `50` bits. -/
private theorem mulPipeline_residue_eq_mod (x y : FPR) :
    ((mulPipeline x y).z1'.toNat % 2 ^ 25) * 2 ^ 25 + (mulPipeline x y).z0.toNat
      = (mulPipeline x y).xu.toNat * (mulPipeline x y).yu.toNat % 2 ^ 50 := by
  have h := mulPipeline_product_eq x y
  have hlt := mulPipeline_residue_lt x y
  omega

/-! ### The 50-bit sticky fold -/

private theorem nat_or_eq_zero_iff (a b : ℕ) : a ||| b = 0 ↔ a = 0 ∧ b = 0 := by
  refine ⟨fun h => ⟨?_, ?_⟩, fun h => by rw [h.1, h.2]; rfl⟩ <;>
  · apply Nat.eq_of_testBit_eq
    intro i
    have hi := congrArg (fun n : ℕ => n.testBit i) h
    simp only [Nat.testBit_or, Nat.zero_testBit, Bool.or_eq_false_iff] at hi
    simp [Nat.zero_testBit, hi.1, hi.2]

private theorem toNat_and25_uint32 (v : UInt32) :
    (v &&& 0x01FFFFFF).toNat = v.toNat % 2 ^ 25 := by
  rw [UInt32.toNat_and, show (0x01FFFFFF : UInt32).toNat = 2 ^ 25 - 1 from by decide,
    Nat.and_two_pow_sub_one_eq_mod]

/-- The word `FPR.mul` tests for the sticky bit vanishes exactly when the product's low `50`
bits do. -/
private theorem mulPipeline_stickyWord_eq_zero_iff (x y : FPR) :
    ((mulPipeline x y).z0 ||| ((mulPipeline x y).z1' &&& 0x01FFFFFF)) = 0
      ↔ (mulPipeline x y).xu.toNat * (mulPipeline x y).yu.toNat % 2 ^ 50 = 0 := by
  rw [← mulPipeline_residue_eq_mod, ← UInt32.toNat_inj, UInt32.toNat_or, toNat_and25_uint32,
    show (0 : UInt32).toNat = 0 from rfl, nat_or_eq_zero_iff]
  have h2 : (mulPipeline x y).z0.toNat < 2 ^ 25 := by
    rw [mulPipeline_z0_toNat]; exact Nat.mod_lt _ (Nat.two_pow_pos _)
  constructor
  · rintro ⟨h0, h1⟩; rw [h0, h1]; ring
  · intro h
    have h1 : (mulPipeline x y).z1'.toNat % 2 ^ 25 < 2 ^ 25 := Nat.mod_lt _ (Nat.two_pow_pos _)
    omega

/-- `zu'` is the product's `50`-bit sticky shift: the high word with a single bit recording
whether anything was discarded. -/
private theorem mulPipeline_zu'_toNat (x y : FPR) :
    (mulPipeline x y).zu'.toNat
      = stickyShift ((mulPipeline x y).xu.toNat * (mulPipeline x y).yu.toNat) 50 := by
  have hmask := masked_or_add_shiftRight_25 (mulPipeline x y).w0.toUInt32 (mulPipeline x y).z1'
  rw [← mulPipeline_z0] at hmask
  rw [mulPipeline_zu', hmask]
  rw [stickyShift, UInt64.toNat_or, mulPipeline_zu_eq_div, Nat.shiftRight_eq_div_pow]
  congr 1
  by_cases h : ((mulPipeline x y).z0 ||| ((mulPipeline x y).z1' &&& 0x01FFFFFF)) = 0
  · rw [ite_eq_left h, ite_eq_left ((mulPipeline_stickyWord_eq_zero_iff x y).mp h)]; rfl
  · rw [ite_eq_right h,
      ite_eq_right fun hc => h ((mulPipeline_stickyWord_eq_zero_iff x y).mpr hc)]
    rfl

/-! ### The product's magnitude, and the renormalised significand -/

private theorem mulPipeline_product_le (x y : FPR) :
    2 ^ 104 ≤ (mulPipeline x y).xu.toNat * (mulPipeline x y).yu.toNat := by
  calc (2 : ℕ) ^ 104 = 2 ^ 52 * 2 ^ 52 := by norm_num
    _ ≤ (mulPipeline x y).xu.toNat * (mulPipeline x y).yu.toNat :=
        Nat.mul_le_mul (mulPipeline_le_xu x y) (mulPipeline_le_yu x y)

private theorem mulPipeline_product_lt (x y : FPR) :
    (mulPipeline x y).xu.toNat * (mulPipeline x y).yu.toNat < 2 ^ 106 := by
  calc (mulPipeline x y).xu.toNat * (mulPipeline x y).yu.toNat < 2 ^ 53 * 2 ^ 53 :=
        Nat.mul_lt_mul_of_lt_of_lt (mulPipeline_xu_lt x y) (mulPipeline_yu_lt x y)
    _ = 2 ^ 106 := by norm_num

private theorem mulPipeline_le_zu' (x y : FPR) : 2 ^ 54 ≤ (mulPipeline x y).zu'.toNat := by
  rw [mulPipeline_zu'_toNat]
  refine le_trans ?_ (le_stickyShift _ 50)
  exact Nat.le_div_iff_mul_le (Nat.two_pow_pos 50) |>.mpr
    (by have := mulPipeline_product_le x y; norm_num at this ⊢; omega)

private theorem mulPipeline_zu'_lt (x y : FPR) : (mulPipeline x y).zu'.toNat < 2 ^ 56 := by
  rw [mulPipeline_zu'_toNat]
  refine stickyShift_lt_two_pow (by norm_num) ?_
  exact Nat.div_lt_of_lt_mul (by have := mulPipeline_product_lt x y; norm_num at this ⊢; omega)

private theorem mulPipeline_es_le_one (x y : FPR) : (mulPipeline x y).es.toNat ≤ 1 := by
  rw [mulPipeline_es, UInt64.toNat_shiftRight,
    show (55 : UInt64).toNat % 64 = 55 from by decide, Nat.shiftRight_eq_div_pow]
  have := mulPipeline_zu'_lt x y
  omega

private theorem mulPipeline_zu''_toNat (x y : FPR) :
    (mulPipeline x y).zu''.toNat
      = stickyShift (mulPipeline x y).zu'.toNat (mulPipeline x y).es.toNat := by
  rw [mulPipeline_zu'']
  exact toNat_shiftRight_or_and_one _ _ (mulPipeline_es_le_one x y)

/-- The renormalised significand lands in the window `FPR.make`'s rounding analysis needs. -/
private theorem mulPipeline_zu''_mem (x y : FPR) :
    2 ^ 54 ≤ (mulPipeline x y).zu''.toNat ∧ (mulPipeline x y).zu''.toNat < 2 ^ 55 := by
  have hes := mulPipeline_es_le_one x y
  have hlo := mulPipeline_le_zu' x y
  have hhi := mulPipeline_zu'_lt x y
  have hdiv : (mulPipeline x y).zu'.toNat / 2 ^ (mulPipeline x y).es.toNat < 2 ^ 55 := by
    interval_cases h : (mulPipeline x y).es.toNat
    · -- `es = 0`: the product did not carry, so `zu'` is already below `2 ^ 55`
      have hz : (mulPipeline x y).zu'.toNat / 2 ^ 55 = 0 := by
        have := mulPipeline_es x y
        have hsr : (mulPipeline x y).es.toNat = (mulPipeline x y).zu'.toNat / 2 ^ 55 := by
          rw [mulPipeline_es, UInt64.toNat_shiftRight,
            show (55 : UInt64).toNat % 64 = 55 from by decide, Nat.shiftRight_eq_div_pow]
        omega
      simp only [pow_zero, Nat.div_one]
      omega
    · simp only [pow_one]; omega
  have hlo' : 2 ^ 54 ≤ (mulPipeline x y).zu'.toNat / 2 ^ (mulPipeline x y).es.toNat := by
    interval_cases h : (mulPipeline x y).es.toNat
    · simp only [pow_zero, Nat.div_one]; omega
    · simp only [pow_one]
      have hsr : (mulPipeline x y).es.toNat = (mulPipeline x y).zu'.toNat / 2 ^ 55 := by
        rw [mulPipeline_es, UInt64.toNat_shiftRight,
          show (55 : UInt64).toNat % 64 = 55 from by decide, Nat.shiftRight_eq_div_pow]
      omega
  rw [mulPipeline_zu''_toNat]
  exact ⟨le_trans hlo' (le_stickyShift _ _), stickyShift_lt_two_pow (by norm_num) hdiv⟩

/-! ### Composing the two sticky shifts

`FPR.mul` folds the discarded bits twice: once at bit `50`, when the `106`-bit product is cut
down to its high word, and again at bit `1` when a carry into bit `55` forces a renormalisation.
Sticky shifts compose, so the pair is a single sticky shift by `50 + es` and the truncation error
never exceeds one unit in the last place of the result. -/

private theorem stickyShift_fifty_succ (v : ℕ) :
    stickyShift (stickyShift v 50) 1 = stickyShift v 51 := by
  rw [stickyShift_eq (stickyShift v 50) 1, stickyShift_eq v 50, stickyShift_eq v 51]
  norm_num
  split_ifs <;> omega

private theorem mulPipeline_es_toNat (x y : FPR) :
    (mulPipeline x y).es.toNat = (mulPipeline x y).zu'.toNat / 2 ^ 55 := by
  rw [mulPipeline_es, UInt64.toNat_shiftRight,
    show (55 : UInt64).toNat % 64 = 55 from by decide, Nat.shiftRight_eq_div_pow]

/-- The significand handed to `FPR.make` is the exact product, sticky-shifted by `50 + es`. -/
private theorem mulPipeline_zu''_eq_stickyShift (x y : FPR) :
    (mulPipeline x y).zu''.toNat
      = stickyShift ((mulPipeline x y).xu.toNat * (mulPipeline x y).yu.toNat)
          (50 + (mulPipeline x y).es.toNat) := by
  have hes := mulPipeline_es_le_one x y
  rw [mulPipeline_zu''_toNat, mulPipeline_zu'_toNat]
  interval_cases h : (mulPipeline x y).es.toNat
  · rw [stickyShift_zero]
  · exact stickyShift_fifty_succ _

/-- The truncation error of the whole multiply is below one unit in the last place. -/
private theorem mulPipeline_zu''_bracket (x y : FPR) :
    (mulPipeline x y).zu''.toNat * 2 ^ (50 + (mulPipeline x y).es.toNat)
        < (mulPipeline x y).xu.toNat * (mulPipeline x y).yu.toNat
          + 2 ^ (50 + (mulPipeline x y).es.toNat)
      ∧ (mulPipeline x y).xu.toNat * (mulPipeline x y).yu.toNat
        < (mulPipeline x y).zu''.toNat * 2 ^ (50 + (mulPipeline x y).es.toNat)
          + 2 ^ (50 + (mulPipeline x y).es.toNat) := by
  rw [mulPipeline_zu''_eq_stickyShift]
  exact ⟨stickyShift_mul_lt _ _, lt_stickyShift_mul_add _ _⟩

/-! ### The flush-to-zero guard is inactive on normal operands

`FPR.mul` guards against a zero exponent field by building an all-ones mask from the top bit of
`(ex - 1) ||| (ey - 1)`. On two normal operands both fields are at least `1`, so both decrements
stay below `2 ^ 11`, the mask is zero, and neither the exponent nor the significand is rewritten. -/

private theorem mulPipeline_ex_toNat (x y : FPR) :
    (mulPipeline x y).ex.toNat = (FPR.decode x).exponent := by
  rw [mulPipeline_ex]; exact toNat_ex_field_of x

private theorem mulPipeline_ey_toNat (x y : FPR) :
    (mulPipeline x y).ey.toNat = (FPR.decode y).exponent := by
  rw [mulPipeline_ey]; exact toNat_ex_field_of y

private theorem mulPipeline_dzu_eq_zero (x y : FPR)
    (ha : FPR.IsNormal x) (hb : FPR.IsNormal y) : (mulPipeline x y).dzu = 0 := by
  have hx1 : 1 ≤ (mulPipeline x y).ex.toNat := by
    rw [mulPipeline_ex_toNat]; exact Nat.one_le_iff_ne_zero.mpr ha.1
  have hy1 : 1 ≤ (mulPipeline x y).ey.toNat := by
    rw [mulPipeline_ey_toNat]; exact Nat.one_le_iff_ne_zero.mpr hb.1
  have hxlt : (mulPipeline x y).ex.toNat < 2 ^ 11 := by
    rw [mulPipeline_ex_toNat]; exact FPR.decode_exponent_lt x
  have hylt : (mulPipeline x y).ey.toNat < 2 ^ 11 := by
    rw [mulPipeline_ey_toNat]; exact FPR.decode_exponent_lt y
  have hsx : ((mulPipeline x y).ex - 1).toNat = (mulPipeline x y).ex.toNat - 1 :=
    toNat_sub_of_le_uint32 (by simpa using hx1)
  have hsy : ((mulPipeline x y).ey - 1).toNat = (mulPipeline x y).ey.toNat - 1 :=
    toNat_sub_of_le_uint32 (by simpa using hy1)
  have hor : (((mulPipeline x y).ex - 1) ||| ((mulPipeline x y).ey - 1)).toNat < 2 ^ 31 := by
    rw [UInt32.toNat_or]
    have h := Nat.or_lt_two_pow (n := 11) (by omega : ((mulPipeline x y).ex - 1).toNat < 2 ^ 11)
      (by omega : ((mulPipeline x y).ey - 1).toNat < 2 ^ 11)
    omega
  have hsh : ((((mulPipeline x y).ex - 1) ||| ((mulPipeline x y).ey - 1)) >>> 31) = 0 := by
    rw [← UInt32.toNat_inj, toNat_shiftRight_31_uint32,
      show (0 : UInt32).toNat = 0 from rfl]
    omega
  rw [mulPipeline_dzu]
  unfold tbmask
  rw [hsh]
  decide

private theorem mulPipeline_zu'''_eq (x y : FPR)
    (ha : FPR.IsNormal x) (hb : FPR.IsNormal y) :
    (mulPipeline x y).zu''' = (mulPipeline x y).zu'' := by
  rw [mulPipeline_zu''', mulPipeline_dzu_eq_zero x y ha hb,
    show (((0 : UInt32) &&& 1).toUInt64 - 1) = 0xFFFFFFFFFFFFFFFF from by decide]
  exact and_allOnes_uint64 _

private theorem mulPipeline_e'_eq (x y : FPR)
    (ha : FPR.IsNormal x) (hb : FPR.IsNormal y) :
    (mulPipeline x y).e' = (mulPipeline x y).e.toInt32 := by
  rw [mulPipeline_e', mulPipeline_dzu_eq_zero x y ha hb, uint32_zero_and, uint32_xor_zero]

/-! ### The exponent chain

`e = ex + ey - 2100 + es` is computed in wrapping `UInt32` arithmetic and only then reinterpreted
as an `Int32`. For two normal operands the intended value lies in `[-2098, 1993]`, well inside
`Int32`, so the wraparound pattern the subtraction produces is exactly the two's-complement
encoding of the intended (often negative) exponent. -/

private theorem mulPipeline_e_toInt (x y : FPR)
    (hx1 : 1 ≤ (mulPipeline x y).ex.toNat) (hx2 : (mulPipeline x y).ex.toNat ≤ 2046)
    (hy1 : 1 ≤ (mulPipeline x y).ey.toNat) (hy2 : (mulPipeline x y).ey.toNat ≤ 2046) :
    (mulPipeline x y).e.toInt32.toInt
      = ((mulPipeline x y).ex.toNat : ℤ) + ((mulPipeline x y).ey.toNat : ℤ) - 2100
        + ((mulPipeline x y).es.toNat : ℤ) := by
  have hes := mulPipeline_es_le_one x y
  have hES : ((mulPipeline x y).es.toUInt32).toNat = (mulPipeline x y).es.toNat := by
    rw [UInt64.toNat_toUInt32]; omega
  rw [mulPipeline_e, UInt32.toInt32_add, Int32.toInt_add, UInt32.toInt32_sub, Int32.toInt_sub,
    UInt32.toInt32_add, Int32.toInt_add,
    toInt_toInt32_of_lt (show (mulPipeline x y).ex.toNat < 2 ^ 31 by omega),
    toInt_toInt32_of_lt (show (mulPipeline x y).ey.toNat < 2 ^ 31 by omega),
    toInt_toInt32_of_lt (show (2100 : UInt32).toNat < 2 ^ 31 by decide),
    toInt_toInt32_of_lt (show ((mulPipeline x y).es.toUInt32).toNat < 2 ^ 31 by omega),
    show (2100 : UInt32).toNat = 2100 from by decide, hES]
  push_cast
  rw [show (((mulPipeline x y).ex.toNat : ℤ) + ((mulPipeline x y).ey.toNat : ℤ)).bmod 4294967296
        = ((mulPipeline x y).ex.toNat : ℤ) + ((mulPipeline x y).ey.toNat : ℤ) from
      Int.bmod_eq_of_le_mul_two (by omega) (by omega)]
  rw [show (((mulPipeline x y).ex.toNat : ℤ) + ((mulPipeline x y).ey.toNat : ℤ)
          - 2100).bmod 4294967296
        = ((mulPipeline x y).ex.toNat : ℤ) + ((mulPipeline x y).ey.toNat : ℤ) - 2100 from
      Int.bmod_eq_of_le_mul_two (by omega) (by omega)]
  exact Int.bmod_eq_of_le_mul_two (by omega) (by omega)

/-! ### Magnitudes and sign -/

private theorem mulPipeline_abs_toReal_x (x y : FPR) (ha : FPR.IsNormal x) :
    |toReal x| = ((mulPipeline x y).xu.toNat : ℝ)
      * (2 : ℝ) ^ (((FPR.decode x).exponent : ℤ) - 1075) := by
  rw [mulPipeline_xu_toNat]
  change |(FPR.decode x).toReal| = _
  rw [abs_toReal_eq_significand_mul_two_zpow ha.1 ha.2]
  unfold FPR.Bits.significand
  rw [ite_eq_right ha.1]

private theorem mulPipeline_abs_toReal_y (x y : FPR) (hb : FPR.IsNormal y) :
    |toReal y| = ((mulPipeline x y).yu.toNat : ℝ)
      * (2 : ℝ) ^ (((FPR.decode y).exponent : ℤ) - 1075) := by
  rw [mulPipeline_yu_toNat]
  change |(FPR.decode y).toReal| = _
  rw [abs_toReal_eq_significand_mul_two_zpow hb.1 hb.2]
  unfold FPR.Bits.significand
  rw [ite_eq_right hb.1]

/-- The sign word is the exclusive-or of the two operands' sign bits. -/
private theorem mulPipeline_s_toNat (x y : FPR) :
    (mulPipeline x y).s.toNat
      = if xor (FPR.decode x).sign (FPR.decode y).sign then 1 else 0 := by
  rw [mulPipeline_s, signWord_toNat]

private theorem mulPipeline_s_le_one (x y : FPR) : (mulPipeline x y).s.toNat ≤ 1 := by
  rw [mulPipeline_s_toNat]; split <;> omega

/-- The product's sign factor, read off the sign word, is the product of the two operands'. -/
private theorem mulPipeline_sign_factor (x y : FPR) :
    (if (mulPipeline x y).s.toNat = 1 then (-1 : ℝ) else 1)
      = (if (FPR.decode x).sign then (-1 : ℝ) else 1)
        * (if (FPR.decode y).sign then (-1 : ℝ) else 1) := by
  rw [mulPipeline_s_toNat]
  cases hx : (FPR.decode x).sign <;> cases hy : (FPR.decode y).sign <;> norm_num

/-! ### The scale inequality that makes the error budget fit

The rounding step spends `2 ^ -53` of the `2 ^ -52` budget, so the truncation step must fit in
what is left. That holds because the exact product is large relative to the discarded low bits:
at least `2 ^ 104`, and at least `2 ^ 105 - 2 ^ 50` in the carrying case, against a discarded
weight of `2 ^ (50 + es)`. -/

private theorem mulPipeline_scale_le (x y : FPR) :
    2 ^ (53 : ℕ) * 2 ^ (50 + (mulPipeline x y).es.toNat)
        + 2 ^ (50 + (mulPipeline x y).es.toNat)
      ≤ (mulPipeline x y).xu.toNat * (mulPipeline x y).yu.toNat := by
  have hes := mulPipeline_es_le_one x y
  interval_cases h : (mulPipeline x y).es.toNat
  · have := mulPipeline_product_le x y; norm_num at this ⊢; omega
  · -- a carry into bit `55` forces the product past `2 ^ 105 - 2 ^ 50`
    have hzu' : 2 ^ 55 ≤ (mulPipeline x y).zu'.toNat := by
      have hsr := mulPipeline_es_toNat x y
      omega
    have hlt := stickyShift_mul_lt ((mulPipeline x y).xu.toNat * (mulPipeline x y).yu.toNat) 50
    rw [← mulPipeline_zu'_toNat] at hlt
    have : 2 ^ 55 * 2 ^ 50 ≤ (mulPipeline x y).zu'.toNat * 2 ^ 50 :=
      Nat.mul_le_mul_right _ hzu'
    norm_num at this hlt ⊢
    omega

/-! ### Real-valued form of the pipeline -/

private theorem mulPipeline_abs_product (x y : FPR) (ha : FPR.IsNormal x) (hb : FPR.IsNormal y) :
    |toReal x * toReal y|
      = (((mulPipeline x y).xu.toNat : ℝ) * ((mulPipeline x y).yu.toNat : ℝ))
        * (2 : ℝ) ^ ((((FPR.decode x).exponent : ℤ) + ((FPR.decode y).exponent : ℤ)) - 2150) := by
  rw [abs_mul, mulPipeline_abs_toReal_x x y ha, mulPipeline_abs_toReal_y x y hb,
    show ((((FPR.decode x).exponent : ℤ) + ((FPR.decode y).exponent : ℤ)) - 2150)
      = ((((FPR.decode x).exponent : ℤ)) - 1075) + ((((FPR.decode y).exponent : ℤ)) - 1075) by ring,
    zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
  ring

/-- The error bound and the closure property for `FPR.mul`, proved together.

Both conclusions rest on the same exponent-window analysis, and the window is most of the work,
so they are established in one pass and projected out below. -/
private theorem mul_error_aux (a b : FPR) (ha : FPR.IsNormal a) (hb : FPR.IsNormal b)
    (hr : FPR.InNormalMagnitudeRange (toReal a * toReal b)) :
    (|toReal (FPR.mul a b) - toReal a * toReal b| ≤
      (2 : ℝ) ^ (-(52 : ℤ)) * |toReal a * toReal b|)
    ∧ FPR.IsNormal (FPR.mul a b) := by
  have hne : toReal a * toReal b ≠ 0 :=
    mul_ne_zero (toReal_ne_zero_of_isNormal ha) (toReal_ne_zero_of_isNormal hb)
  rcases hr with h0 | ⟨hlo, hhi⟩
  · exact absurd h0 hne
  -- exponent-field bounds for the two normal operands
  have hx1 : 1 ≤ (mulPipeline a b).ex.toNat := by
    rw [mulPipeline_ex_toNat]; exact Nat.one_le_iff_ne_zero.mpr ha.1
  have hy1 : 1 ≤ (mulPipeline a b).ey.toNat := by
    rw [mulPipeline_ey_toNat]; exact Nat.one_le_iff_ne_zero.mpr hb.1
  have hx2 : (mulPipeline a b).ex.toNat ≤ 2046 := by
    rw [mulPipeline_ex_toNat]
    have := FPR.decode_exponent_lt a; have := ha.2; omega
  have hy2 : (mulPipeline a b).ey.toNat ≤ 2046 := by
    rw [mulPipeline_ey_toNat]
    have := FPR.decode_exponent_lt b; have := hb.2; omega
  have hmem := mulPipeline_zu''_mem a b
  have hes := mulPipeline_es_le_one a b
  -- the real-valued data
  set c : ℝ := (2 : ℝ) ^ ((((FPR.decode a).exponent : ℤ) + ((FPR.decode b).exponent : ℤ)) - 2150)
    with hcdef
  have hc : 0 < c := zpow_pos (by norm_num) _
  set K : ℝ := (2 : ℝ) ^ (50 + (mulPipeline a b).es.toNat) with hKdef
  have hK : 0 < K := by rw [hKdef]; positivity
  set W : ℝ := ((mulPipeline a b).zu''.toNat : ℝ) with hWdef
  set P : ℝ := (((mulPipeline a b).xu.toNat : ℝ) * ((mulPipeline a b).yu.toNat : ℝ)) with hPdef
  have habsQ : |toReal a * toReal b| = P * c := mulPipeline_abs_product a b ha hb
  -- the truncation bracket, in ℝ
  have hbrN := mulPipeline_zu''_bracket a b
  have hbr1 : (W - 1) * K < P := by
    have h := hbrN.1
    have : ((((mulPipeline a b).zu''.toNat * 2 ^ (50 + (mulPipeline a b).es.toNat) : ℕ)) : ℝ)
        < (((mulPipeline a b).xu.toNat * (mulPipeline a b).yu.toNat
            + 2 ^ (50 + (mulPipeline a b).es.toNat) : ℕ) : ℝ) := by exact_mod_cast h
    push_cast at this
    rw [hWdef, hKdef, hPdef]; nlinarith [this]
  have hbr2 : P < (W + 1) * K := by
    have h := hbrN.2
    have : ((((mulPipeline a b).xu.toNat * (mulPipeline a b).yu.toNat : ℕ)) : ℝ)
        < (((mulPipeline a b).zu''.toNat * 2 ^ (50 + (mulPipeline a b).es.toNat)
            + 2 ^ (50 + (mulPipeline a b).es.toNat) : ℕ) : ℝ) := by exact_mod_cast h
    push_cast at this
    rw [hWdef, hKdef, hPdef]; nlinarith [this]
  have hkey : (2 : ℝ) ^ (53 : ℕ) * K + K ≤ P := by
    have h := mulPipeline_scale_le a b
    have : ((2 ^ (53 : ℕ) * 2 ^ (50 + (mulPipeline a b).es.toNat)
        + 2 ^ (50 + (mulPipeline a b).es.toNat) : ℕ) : ℝ)
        ≤ (((mulPipeline a b).xu.toNat * (mulPipeline a b).yu.toNat : ℕ) : ℝ) := by
      exact_mod_cast h
    push_cast at this
    rw [hKdef, hPdef]; linarith
  have hW1 : (2 : ℝ) ^ (54 : ℕ) ≤ W := by rw [hWdef]; exact_mod_cast hmem.1
  have hW2 : W ≤ (2 : ℝ) ^ (55 : ℕ) - 1 := by
    rw [hWdef]
    have : ((mulPipeline a b).zu''.toNat : ℝ) < (2 : ℝ) ^ (55 : ℕ) := by exact_mod_cast hmem.2
    have hnat : (mulPipeline a b).zu''.toNat + 1 ≤ 2 ^ 55 := hmem.2
    have : (((mulPipeline a b).zu''.toNat + 1 : ℕ) : ℝ) ≤ ((2 ^ 55 : ℕ) : ℝ) := by
      exact_mod_cast hnat
    push_cast at this; linarith
  -- the exponent scale
  have heI := mulPipeline_e_toInt a b hx1 hx2 hy1 hy2
  rw [mulPipeline_ex_toNat, mulPipeline_ey_toNat] at heI
  have hScale : (2 : ℝ) ^ (mulPipeline a b).e.toInt32.toInt = K * c := by
    rw [heI, hKdef, hcdef, ← zpow_natCast (2 : ℝ) (50 + (mulPipeline a b).es.toNat),
      ← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
    congr 1
    push_cast
    omega
  have he'I : (mulPipeline a b).e'.toInt = (mulPipeline a b).e.toInt32.toInt := by
    rw [mulPipeline_e'_eq a b ha hb]
  -- the exponent window, forced by the result-range hypothesis
  have hSpos : (0 : ℝ) < (2 : ℝ) ^ (mulPipeline a b).e.toInt32.toInt := zpow_pos (by norm_num) _
  have hb1 : (W - 1) * ((2 : ℝ) ^ (mulPipeline a b).e.toInt32.toInt)
      < |toReal a * toReal b| := by
    rw [hScale, habsQ, show (W - 1) * (K * c) = ((W - 1) * K) * c from by ring]
    exact mul_lt_mul_of_pos_right hbr1 hc
  have hb2 : |toReal a * toReal b|
      < (W + 1) * ((2 : ℝ) ^ (mulPipeline a b).e.toInt32.toInt) := by
    rw [hScale, habsQ, show (W + 1) * (K * c) = ((W + 1) * K) * c from by ring]
    exact mul_lt_mul_of_pos_right hbr2 hc
  have hhi' : |toReal a * toReal b| ≤ (2 : ℝ) ^ (1024 : ℤ) - (2 : ℝ) ^ (971 : ℤ) := by
    rw [← maxFiniteReal_eq]; exact hhi
  have hlo' : (2 : ℝ) ^ (-(1022 : ℤ)) ≤ |toReal a * toReal b| := hlo
  have hle969 : (mulPipeline a b).e'.toInt ≤ 969 := by
    have h := (zpow_lt_zpow_iff_right₀ (by norm_num : (1 : ℝ) < 2)).mp
      (mul_scale_lt hW1 hb1 hhi')
    omega
  have hge : -1076 ≤ (mulPipeline a b).e'.toInt := by
    have h := (zpow_lt_zpow_iff_right₀ (by norm_num : (1 : ℝ) < 2)).mp
      (mul_scale_gt hW2 hb2 hSpos hlo')
    omega
  -- at the very top of the range the final rounding cannot carry out of the mantissa field
  have hnc : (mulPipeline a b).e'.toInt = 969 →
      roundQuarterTiesEven (mulPipeline a b).zu''.toNat < 2 ^ 53 := by
    intro h969
    by_contra hcc
    push Not at hcc
    have hround := (roundQuarterTiesEven_mem_of_normalized _ hmem.1 hmem.2).2
    have heq : roundQuarterTiesEven (mulPipeline a b).zu''.toNat = 2 ^ 53 := by omega
    have h4 := four_mul_roundQuarterTiesEven_le (mulPipeline a b).zu''.toNat
    rw [heq] at h4
    have hWbig : (2 : ℝ) ^ (55 : ℕ) - 2 ≤ W := by
      rw [hWdef]
      have hn : (2 : ℕ) ^ 55 ≤ (mulPipeline a b).zu''.toNat + 2 := by omega
      have hR : (((2 : ℕ) ^ 55 : ℕ) : ℝ) ≤ (((mulPipeline a b).zu''.toNat + 2 : ℕ) : ℝ) := by
        exact_mod_cast hn
      push_cast at hR; linarith
    rw [he'I] at h969
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
    rw [← abs_mul] at hhi'
    linarith
  -- the rounding step
  have hmul : FPR.mul a b
      = make (mulPipeline a b).s (mulPipeline a b).e' (mulPipeline a b).zu'' := by
    rw [mul_eq_make, mulPipeline_zu'''_eq a b ha hb]
  have hMV : |toReal (FPR.mul a b)
        - (if (mulPipeline a b).s.toNat = 1 then (-1 : ℝ) else 1)
          * ((mulPipeline a b).zu''.toNat : ℝ) * (2 : ℝ) ^ (mulPipeline a b).e'.toInt|
      ≤ (2 : ℝ) ^ (-(53 : ℤ))
        * |(if (mulPipeline a b).s.toNat = 1 then (-1 : ℝ) else 1)
            * ((mulPipeline a b).zu''.toNat : ℝ) * (2 : ℝ) ^ (mulPipeline a b).e'.toInt| := by
    rw [show toReal (FPR.mul a b) = toRealBits (FPR.mul a b) from rfl, hmul]
    by_cases h969 : (mulPipeline a b).e'.toInt = 969
    · exact abs_toRealBits_make_sub_le_of_no_carry _ _ _ (mulPipeline_s_le_one a b) hge hle969
        hmem.1 hmem.2 (hnc h969)
    · exact abs_toRealBits_make_sub_le _ _ _ (mulPipeline_s_le_one a b) hge (by omega)
        hmem.1 hmem.2
  -- the exact product, with its sign
  have hA := toReal_eq_sign_mul_abs a ha.1 ha.2
  have hB := toReal_eq_sign_mul_abs b hb.1 hb.2
  have hQsign : toReal a * toReal b
      = (if (mulPipeline a b).s.toNat = 1 then (-1 : ℝ) else 1) * (P * c) := by
    calc toReal a * toReal b
        = ((if (FPR.decode a).sign then (-1 : ℝ) else 1) * |toReal a|)
          * ((if (FPR.decode b).sign then (-1 : ℝ) else 1) * |toReal b|) := by rw [← hA, ← hB]
      _ = ((if (FPR.decode a).sign then (-1 : ℝ) else 1)
            * (if (FPR.decode b).sign then (-1 : ℝ) else 1)) * (|toReal a| * |toReal b|) := by ring
      _ = (if (mulPipeline a b).s.toNat = 1 then (-1 : ℝ) else 1) * |toReal a * toReal b| := by
          rw [mulPipeline_sign_factor, abs_mul]
      _ = (if (mulPipeline a b).s.toNat = 1 then (-1 : ℝ) else 1) * (P * c) := by rw [habsQ]
  refine ⟨?_, ?_⟩
  · rw [hQsign]
    refine mul_error_combine (by split_ifs <;> simp) hc (by rw [hWdef]; positivity) hK ?_
      hbr1 hbr2 hkey
    rw [show (if (mulPipeline a b).s.toNat = 1 then (-1 : ℝ) else 1) * (W * K * c)
        = (if (mulPipeline a b).s.toNat = 1 then (-1 : ℝ) else 1) * W
          * (2 : ℝ) ^ (mulPipeline a b).e'.toInt from by rw [he'I, hScale]; ring]
    exact hMV
  · rw [hmul]
    exact FPR.isNormal_make _ _ _ (mulPipeline_s_le_one a b) hge hle969 hmem.1 hmem.2 hnc

/-- Relative error bound for `FPR.mul`, on normal operands whose exact product stays in the
correctly-rounded binary64 magnitude window (`FPR.InNormalMagnitudeRange`); see `add_error` for
why both the operand- and result-side restrictions are necessary. -/
private theorem mul_error_of_isNormal (a b : FPR) (ha : FPR.IsNormal a) (hb : FPR.IsNormal b)
    (hr : FPR.InNormalMagnitudeRange (toReal a * toReal b)) :
    |toReal (FPR.mul a b) - toReal a * toReal b| ≤
    (2 : ℝ) ^ (-(52 : ℤ)) * |toReal a * toReal b| :=
  (mul_error_aux a b ha hb hr).1

/-- Closure for `FPR.mul` on the domain `mul_error` covers. Unlike addition, multiplication
cannot cancel: a product of nonzero normals is nonzero, so the result is always normal and the
zero disjunct of `FPR.IsNormalOrZero` is never needed here. -/
private theorem mul_isNormalOrZero_of_isNormal (a b : FPR) (ha : FPR.IsNormal a)
    (hb : FPR.IsNormal b)
    (hr : FPR.InNormalMagnitudeRange (toReal a * toReal b)) :
    FPR.IsNormalOrZero (FPR.mul a b) :=
  Or.inl (mul_error_aux a b ha hb hr).2

/-- `FPR.mul`'s flush guard fires when either operand's exponent field is `0`. -/
private theorem mulPipeline_dzu_eq_allOnes (x y : FPR)
    (h : (FPR.decode x).exponent = 0 ∨ (FPR.decode y).exponent = 0) :
    (mulPipeline x y).dzu = 0xFFFFFFFF := by
  have hor : (((mulPipeline x y).ex - 1) ||| ((mulPipeline x y).ey - 1)).toNat = 2 ^ 32 - 1 := by
    have hsize : (UInt32.size : Nat) = 2 ^ 32 := by decide
    have hbnd := (((mulPipeline x y).ex - 1) ||| ((mulPipeline x y).ey - 1)).toNat_lt_size
    rcases h with h | h
    · have hz : ((mulPipeline x y).ex - 1).toNat = 2 ^ 32 - 1 := by
        rw [show (mulPipeline x y).ex = 0 from by
          rw [← UInt32.toNat_inj, mulPipeline_ex_toNat, h]; rfl]
        exact uint32_zero_sub_one_toNat
      have hle : ((mulPipeline x y).ex - 1).toNat
          ≤ (((mulPipeline x y).ex - 1) ||| ((mulPipeline x y).ey - 1)).toNat :=
        UInt32.le_iff_toNat_le.mp UInt32.left_le_or
      omega
    · have hz : ((mulPipeline x y).ey - 1).toNat = 2 ^ 32 - 1 := by
        rw [show (mulPipeline x y).ey = 0 from by
          rw [← UInt32.toNat_inj, mulPipeline_ey_toNat, h]; rfl]
        exact uint32_zero_sub_one_toNat
      have hle : ((mulPipeline x y).ey - 1).toNat
          ≤ (((mulPipeline x y).ex - 1) ||| ((mulPipeline x y).ey - 1)).toNat :=
        UInt32.le_iff_toNat_le.mp UInt32.right_le_or
      omega
  have hsh : ((((mulPipeline x y).ex - 1) ||| ((mulPipeline x y).ey - 1)) >>> 31) = 1 := by
    rw [← UInt32.toNat_inj, toNat_shiftRight_31_uint32, show (1 : UInt32).toNat = 1 from rfl, hor]
    norm_num
  rw [mulPipeline_dzu]
  unfold tbmask
  rw [hsh]
  decide

/-- **`FPR.mul` flushes to a signed zero when either operand is a zero encoding.** The guard
`dzu` fires on a zero exponent field, which both empties the significand and substitutes the
flushed exponent, so the product is the bare sign bit. -/
private theorem mul_eq_signBit_of_exponent_eq_zero (a b : FPR)
    (h : (FPR.decode a).exponent = 0 ∨ (FPR.decode b).exponent = 0) :
    FPR.mul a b = (mulPipeline a b).s <<< 63 := by
  have hdzu := mulPipeline_dzu_eq_allOnes a b h
  have hzu : (mulPipeline a b).zu''' = 0 := by
    rw [mulPipeline_zu''', hdzu,
      show (((0xFFFFFFFF : UInt32) &&& 1).toUInt64 - 1) = 0 from by decide]
    simp
  have he : (mulPipeline a b).e' = ((0 : UInt32) - 1076).toInt32 := by
    rw [mulPipeline_e', hdzu, uint32_allOnes_and, ← UInt32.xor_assoc, UInt32.xor_self,
      UInt32.zero_xor]
  rw [mul_eq_make, hzu, he, make_flushed]

/-- `FPR.mul` lands on a zero encoding when either operand is a zero encoding. -/
private theorem mul_isZero_of_isZero (a b : FPR) (h : FPR.IsZero a ∨ FPR.IsZero b) :
    FPR.IsZero (FPR.mul a b) := by
  have hexp : (FPR.decode a).exponent = 0 ∨ (FPR.decode b).exponent = 0 := by
    rcases h with h | h
    · exact Or.inl h.1
    · exact Or.inr h.1
  unfold FPR.IsZero FPR.Bits.IsZero
  rw [mul_eq_signBit_of_exponent_eq_zero a b hexp, decode_shiftLeft_63 _ (mulPipeline_s_le_one a b)]
  exact ⟨rfl, rfl⟩

theorem mul_error (a b : FPR) (ha : FPR.IsNormalOrZero a) (hb : FPR.IsNormalOrZero b)
    (hr : FPR.InNormalMagnitudeRange (toReal a * toReal b)) :
    |toReal (FPR.mul a b) - toReal a * toReal b| ≤
    (2 : ℝ) ^ (-(52 : ℤ)) * |toReal a * toReal b| := by
  rcases ha with ha | ha
  · rcases hb with hb | hb
    · exact mul_error_of_isNormal a b ha hb hr
    · rw [toReal_eq_zero_of_isZero (mul_isZero_of_isZero a b (Or.inr hb)),
        toReal_eq_zero_of_isZero hb, mul_zero, sub_zero, abs_zero]
      positivity
  · rw [toReal_eq_zero_of_isZero (mul_isZero_of_isZero a b (Or.inl ha)),
      toReal_eq_zero_of_isZero ha, zero_mul, sub_zero, abs_zero]
    positivity

theorem mul_isNormalOrZero (a b : FPR) (ha : FPR.IsNormalOrZero a) (hb : FPR.IsNormalOrZero b)
    (hr : FPR.InNormalMagnitudeRange (toReal a * toReal b)) :
    FPR.IsNormalOrZero (FPR.mul a b) := by
  rcases ha with ha | ha
  · rcases hb with hb | hb
    · exact mul_isNormalOrZero_of_isNormal a b ha hb hr
    · exact Or.inr (mul_isZero_of_isZero a b (Or.inr hb))
  · exact Or.inr (mul_isZero_of_isZero a b (Or.inl ha))

end

end Falcon.Concrete.FPRBridge
