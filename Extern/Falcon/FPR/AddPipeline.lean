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
# The `FPR.add` pipeline, field by field

Names every intermediate word of `FPR.add` — the compare-and-swap on the magnitude key, the
alignment shift with its sticky bit, the signed combination, and the renormalisation — and
proves the normality and field bounds each stage preserves. The error analysis built on these
names is in `Extern.Falcon.FPR.Add`.
-/

public section

namespace Falcon.Concrete.FPRBridge

open Falcon.Concrete.FPR

noncomputable section

/-! ## The `FPR.add` pipeline, named field by field

`FPR.add` is one straight-line chain of `let`s (no branch on data values), so it can be pinned to
the kernel term by `rfl`. `AddPipeline` names every intermediate of that chain as a structure
field, computed by the exact same `let`-chain as `FPR.add`'s body
(`LatticeCrypto/Falcon/Concrete/FPR.lean`) so the sharing between fields is preserved;
`add_eq_make_z` then identifies `FPR.add` with the final assembly call over two of those fields,
by `rfl`. Each field-projection equation below (`addPipeline_za`, `addPipeline_za'`, …) is *also*
`rfl`, and is proved independently of the others, so no proof in this file ever has to re-unfold
the whole pipeline more than once or twice at a time. -/

/-- Every named intermediate of `FPR.add`'s pipeline, in the order `FPR.add` computes them. -/
private structure AddPipeline where
  /-- The raw (possibly-wrapping) magnitude comparison `FPR.add` opens with. -/
  za : UInt64
  /-- The tie-broken magnitude comparator: bit `63` decides whether `x` or `y` leads. -/
  za' : UInt64
  /-- The conditional-swap mask: all-ones when `y` has the larger (or tied, sign-broken)
  magnitude, zero otherwise. -/
  sw : UInt64
  /-- The larger-or-equal-magnitude operand after the conditional swap. -/
  x' : FPR
  /-- The smaller-or-equal-magnitude operand after the conditional swap. -/
  y' : FPR
  ex_ : UInt32
  /-- The sign bit of `x'`. -/
  sx : UInt32
  /-- The biased exponent field of `x'`. -/
  ex : UInt32
  /-- The extended significand of `x'`, scaled by `8` with the implicit leading bit folded in at
  position `55`. -/
  xu : UInt64
  /-- The working exponent paired with `xu`: `ex - 1078`. -/
  ex' : Int32
  ey_ : UInt32
  /-- The sign bit of `y'`. -/
  sy : UInt32
  /-- The biased exponent field of `y'`. -/
  ey : UInt32
  /-- The extended significand of `y'`, scaled by `8` with the implicit leading bit folded in at
  position `55`, before alignment to `x'`'s scale. -/
  yu_ : UInt64
  /-- The exponent gap between `x'` and `y'`. -/
  n : UInt32
  /-- `yu_`, flushed to zero once the exponent gap reaches `60`. -/
  yu' : UInt64
  /-- The alignment shift amount, reduced mod `64`. -/
  n' : UInt32
  m : UInt64
  /-- `y'`'s significand, aligned to `x'`'s scale via a sticky right shift. -/
  yu : UInt64
  /-- All-ones when the two (post-swap) operands' signs differ (subtract), zero when they agree
  (add). -/
  dm : UInt64
  /-- The combined, aligned significand: `xu + yu` on matching signs, `xu - yu` on differing
  signs. -/
  zu : UInt64
  /-- The renormalising left-shift count. -/
  c : UInt32
  /-- The renormalised (top-bit-set) combined significand. -/
  zu' : UInt64
  ex'' : Int32
  /-- The final rounded (9-bit sticky-folded) significand handed to `make_z`. -/
  zu'' : UInt64
  /-- The final exponent handed to `make_z`, after both the renormalising shift and the nine-bit
  rounding fold. -/
  ex''' : Int32

/-- The pipeline of `FPR.add x y`, field by field, computed by the exact same `let`-chain as
`FPR.add`'s body. -/
private def addPipeline (x y : FPR) : AddPipeline :=
  let za := (x &&& M63) - (y &&& M63)
  let za' := za ||| ((za - 1) &&& x)
  let sw := (x ^^^ y) &&& ((0 : UInt64) - (za' >>> 63))
  let x' := x ^^^ sw
  let y' := y ^^^ sw
  let ex_ := (x' >>> 52).toUInt32
  let sx := ex_ >>> 11
  let ex := ex_ &&& 0x7FF
  let xu := ((x' &&& M52) <<< 3) ||| (((ex + 0x7FF) >>> 11).toUInt64 <<< 55)
  let ex' : Int32 := (ex - 1078).toInt32
  let ey_ := (y' >>> 52).toUInt32
  let sy := ey_ >>> 11
  let ey := ey_ &&& 0x7FF
  let yu_ := ((y' &&& M52) <<< 3) ||| (((ey + 0x7FF) >>> 11).toUInt64 <<< 55)
  let n := ex - ey
  let yu' := yu_ &&& ((0 : UInt64) - ((n - 60) >>> 31).toUInt64)
  let n' := n &&& 63
  let m := fpr_ulsh 1 n' - 1
  let yu := fpr_ursh (yu' ||| ((yu' &&& m) + m)) n'
  let dm := (0 - (sx ^^^ sy).toUInt64)
  let zu := xu + yu - (dm &&& (yu <<< 1))
  let c := lzcnt64_nonzero (zu ||| 1)
  let zu' := fpr_ulsh zu c
  let ex'' := ex' - c.toInt32
  let zu'' := (zu' ||| ((zu' &&& 0x1FF) + 0x1FF)) >>> 9
  let ex''' := ex'' + 9
  { za, za', sw, x', y', ex_, sx, ex, xu, ex', ey_, sy, ey, yu_, n, yu', n', m, yu, dm, zu, c, zu',
    ex'', zu'', ex''' }

/-- `FPR.add` is the final assembly call `make_z` applied to two fields of `addPipeline`, pinning
the model to the kernel term exactly as `FPR.add` computes it. -/
private theorem add_eq_make_z (x y : FPR) :
    FPR.add x y =
      make_z (addPipeline x y).sx.toUInt64 (addPipeline x y).ex''' (addPipeline x y).zu'' :=
  rfl

private theorem addPipeline_za (x y : FPR) : (addPipeline x y).za = (x &&& M63) - (y &&& M63) :=
  rfl

private theorem addPipeline_za' (x y : FPR) :
    (addPipeline x y).za' = (addPipeline x y).za ||| (((addPipeline x y).za - 1) &&& x) := rfl

private theorem addPipeline_sw (x y : FPR) :
    (addPipeline x y).sw = (x ^^^ y) &&& ((0 : UInt64) - ((addPipeline x y).za' >>> 63)) := rfl

private theorem addPipeline_x' (x y : FPR) : (addPipeline x y).x' = x ^^^ (addPipeline x y).sw :=
  rfl

private theorem addPipeline_y' (x y : FPR) : (addPipeline x y).y' = y ^^^ (addPipeline x y).sw :=
  rfl

private theorem addPipeline_ex_ (x y : FPR) :
    (addPipeline x y).ex_ = ((addPipeline x y).x' >>> 52).toUInt32 := rfl

private theorem addPipeline_sx (x y : FPR) : (addPipeline x y).sx = (addPipeline x y).ex_ >>> 11 :=
  rfl

private theorem addPipeline_ex (x y : FPR) :
    (addPipeline x y).ex = (addPipeline x y).ex_ &&& 0x7FF := rfl

private theorem addPipeline_xu (x y : FPR) :
    (addPipeline x y).xu =
      ((addPipeline x y).x' &&& M52) <<< 3
        ||| (((addPipeline x y).ex + 0x7FF) >>> 11).toUInt64 <<< 55 := rfl

private theorem addPipeline_ex' (x y : FPR) :
    (addPipeline x y).ex' = ((addPipeline x y).ex - 1078).toInt32 := rfl

private theorem addPipeline_ey_ (x y : FPR) :
    (addPipeline x y).ey_ = ((addPipeline x y).y' >>> 52).toUInt32 := rfl

private theorem addPipeline_sy (x y : FPR) : (addPipeline x y).sy = (addPipeline x y).ey_ >>> 11 :=
  rfl

private theorem addPipeline_ey (x y : FPR) :
    (addPipeline x y).ey = (addPipeline x y).ey_ &&& 0x7FF := rfl

private theorem addPipeline_yu_ (x y : FPR) :
    (addPipeline x y).yu_ =
      ((addPipeline x y).y' &&& M52) <<< 3
        ||| (((addPipeline x y).ey + 0x7FF) >>> 11).toUInt64 <<< 55 := rfl

private theorem addPipeline_n (x y : FPR) :
    (addPipeline x y).n = (addPipeline x y).ex - (addPipeline x y).ey := rfl

private theorem addPipeline_yu' (x y : FPR) :
    (addPipeline x y).yu' =
      (addPipeline x y).yu_ &&& ((0 : UInt64) - (((addPipeline x y).n - 60) >>> 31).toUInt64) :=
  rfl

private theorem addPipeline_dm (x y : FPR) :
    (addPipeline x y).dm =
      (0 : UInt64) - ((addPipeline x y).sx ^^^ (addPipeline x y).sy).toUInt64 := rfl

private theorem addPipeline_zu (x y : FPR) :
    (addPipeline x y).zu =
      (addPipeline x y).xu + (addPipeline x y).yu
        - ((addPipeline x y).dm &&& ((addPipeline x y).yu <<< 1)) := rfl

private theorem addPipeline_c (x y : FPR) :
    (addPipeline x y).c = lzcnt64_nonzero ((addPipeline x y).zu ||| 1) := rfl

private theorem addPipeline_zu' (x y : FPR) :
    (addPipeline x y).zu' = fpr_ulsh (addPipeline x y).zu (addPipeline x y).c := rfl

private theorem addPipeline_ex'' (x y : FPR) :
    (addPipeline x y).ex'' = (addPipeline x y).ex' - ((addPipeline x y).c).toInt32 := rfl

private theorem addPipeline_zu'' (x y : FPR) :
    (addPipeline x y).zu'' =
      ((addPipeline x y).zu' ||| (((addPipeline x y).zu' &&& 0x1FF) + 0x1FF)) >>> 9 := rfl

private theorem addPipeline_ex''' (x y : FPR) :
    (addPipeline x y).ex''' = (addPipeline x y).ex'' + 9 := rfl

/-! ### Step 2: the assembly mantissa-range hypotheses

Whenever the combined significand `zu` is nonzero, the renormalised `zu'` has its top bit set
(`fpr_ulsh_lzcnt64_top_bit`), and the nine-bit rounding fold transfers that bracket through
`stickyShift` to land `zu''` exactly inside the `[2 ^ 54, 2 ^ 55)` window
`abs_toRealBits_make_z_sub_le` needs. -/

/-- The `stickyShift`-by-`9` image of a value already known to occupy the top bit of a 64-bit
word lands in `[2 ^ 54, 2 ^ 55)`, the significand window `FPR.make_z` expects. -/
private theorem stickyShift_nine_mem {v : ℕ} (h1 : 2 ^ 63 ≤ v) (h2 : v < 2 ^ 64) :
    2 ^ 54 ≤ stickyShift v 9 ∧ stickyShift v 9 < 2 ^ 55 := by
  rw [stickyShift_eq]
  have hd1 : 2 ^ 53 ≤ v / 2 ^ 10 := by
    have := Nat.div_le_div_right (c := 2 ^ 10) h1
    norm_num at this
    omega
  have hd2 : v / 2 ^ 10 < 2 ^ 54 := by
    have := Nat.div_le_div_right (c := 2 ^ 10) h2.le
    norm_num at this
    omega
  split_ifs <;> omega

/-- Whenever the combined significand `zu` is nonzero, the final rounded significand `zu''`
handed to `make_z` lands in `[2 ^ 54, 2 ^ 55)`. -/
private theorem addPipeline_zu''_mem (a b : FPR) (h : (addPipeline a b).zu ≠ 0) :
    2 ^ 54 ≤ (addPipeline a b).zu''.toNat ∧ (addPipeline a b).zu''.toNat < 2 ^ 55 := by
  have hge : 2 ^ 63 ≤ (addPipeline a b).zu'.toNat := by
    rw [addPipeline_zu', addPipeline_c]
    exact fpr_ulsh_lzcnt64_top_bit _ h
  have hlt : (addPipeline a b).zu'.toNat < 2 ^ 64 := (addPipeline a b).zu'.toNat_lt_size
  rw [addPipeline_zu'', toNat_or_fold_shiftRight_nine]
  exact stickyShift_nine_mem hge hlt

/-! ### Step 3a: the conditional swap

`za'`'s top bit decides whether `FPR.add` swaps its operands, per `za'_shiftRight_63_eq_one_iff`.
The lemmas below identify that condition with the two operands' packed magnitude comparison, and
conclude that the pipeline's `x'` always carries the larger-or-equal magnitude. -/

/-- The top bit of a right shift by `63` is always `0` or `1`. -/
private theorem shiftRight63_eq_zero_or_one (w : UInt64) : w >>> 63 = 0 ∨ w >>> 63 = 1 := by
  have hmod := toNat_shiftRight_sixtyThree w
  have hb : w.toNat < 2 ^ 64 := w.toNat_lt_size
  have h2 : w.toNat / 2 ^ 63 = 0 ∨ w.toNat / 2 ^ 63 = 1 := by omega
  rcases h2 with h2 | h2
  · exact Or.inl (by rw [← UInt64.toNat_inj, hmod, h2]; rfl)
  · exact Or.inr (by rw [← UInt64.toNat_inj, hmod, h2]; rfl)

/-- Masking an `FPR` word with `M63` computes exactly its decoded `magKey`, restated with `M63`
in place of the literal mask so it can be `rw`-ed directly against `addPipeline`'s fields. -/
private theorem toNat_and_M63_eq_magKey (x : FPR) : (x &&& M63).toNat = (FPR.decode x).magKey :=
  toNat_and_low63Mask_eq_magKey x

/-- Masking an `FPR` word with `M63` always stays below `2 ^ 63`, restated with `M63` in place of
the literal mask. -/
private theorem and_M63_lt (x : FPR) : x &&& M63 < (1 : UInt64) <<< 63 := by
  rw [UInt64.lt_iff_toNat_lt, show (x &&& M63).toNat = x.toNat % 2 ^ 63 from toNat_and_low63Mask x,
    show ((1 : UInt64) <<< 63).toNat = 2 ^ 63 from by decide]
  exact Nat.mod_lt _ (by norm_num)

/-- `FPR.add`'s tie-broken swap test, restated as a comparison of the two operands' decoded
`magKey`s. -/
private theorem addPipeline_za'_shiftRight (a b : FPR) :
    (addPipeline a b).za' >>> 63 = 1 ↔
      (FPR.decode a).magKey < (FPR.decode b).magKey ∨
        ((FPR.decode a).magKey = (FPR.decode b).magKey ∧ a >>> 63 = 1) := by
  rw [addPipeline_za', addPipeline_za,
    za'_shiftRight_63_eq_one_iff (a &&& M63) (b &&& M63) a (and_M63_lt a) (and_M63_lt b),
    UInt64.lt_iff_toNat_lt, toNat_and_M63_eq_magKey, toNat_and_M63_eq_magKey, ← UInt64.toNat_inj,
    toNat_and_M63_eq_magKey, toNat_and_M63_eq_magKey]

/-- `FPR.add`'s pipeline always orders `x'` above `y'` in decoded magnitude, and `(x', y')` is
always `a, b` in one of the two possible orders. -/
private theorem addPipeline_swap_cases (a b : FPR) :
    ((addPipeline a b).x' = a ∧ (addPipeline a b).y' = b ∨
        (addPipeline a b).x' = b ∧ (addPipeline a b).y' = a) ∧
      (FPR.decode (addPipeline a b).y').magKey ≤ (FPR.decode (addPipeline a b).x').magKey := by
  by_cases hswap : (addPipeline a b).za' >>> 63 = 1
  · have hsw : (addPipeline a b).sw = a ^^^ b := by
      rw [addPipeline_sw, hswap]
      change (a ^^^ b) &&& ((0 : UInt64) - 1) = a ^^^ b
      rw [UInt64.and_comm, allOnes_and]
    have hx' : (addPipeline a b).x' = b := by
      rw [addPipeline_x', hsw, ← UInt64.xor_assoc, UInt64.xor_self, UInt64.zero_xor]
    have hy' : (addPipeline a b).y' = a := by
      rw [addPipeline_y', hsw, UInt64.xor_comm a b, ← UInt64.xor_assoc, UInt64.xor_self,
        UInt64.zero_xor]
    refine ⟨Or.inr ⟨hx', hy'⟩, ?_⟩
    rw [hx', hy']
    rcases (addPipeline_za'_shiftRight a b).mp hswap with h | ⟨h, -⟩
    · exact h.le
    · exact h.le
  · have hbit : (addPipeline a b).za' >>> 63 = 0 :=
      (shiftRight63_eq_zero_or_one _).resolve_right hswap
    have hsw : (addPipeline a b).sw = 0 := by
      rw [addPipeline_sw, hbit]
      change (a ^^^ b) &&& ((0 : UInt64) - 0) = 0
      norm_num
    have hx' : (addPipeline a b).x' = a := by rw [addPipeline_x', hsw, UInt64.xor_zero]
    have hy' : (addPipeline a b).y' = b := by rw [addPipeline_y', hsw, UInt64.xor_zero]
    refine ⟨Or.inl ⟨hx', hy'⟩, ?_⟩
    rw [hx', hy']
    by_contra hcontra
    push Not at hcontra
    exact hswap ((addPipeline_za'_shiftRight a b).mpr (Or.inl hcontra))

/-! ### Step 3b: field extraction

`xu` (resp. `yu_`) packs the decoded mantissa of `x'` (resp. `y'`), left-shifted by `3`, together
with an implicit leading bit set exactly when the operand is normal, at bit position `55`. This
section identifies that packed value with `8 *` the operand's `FPR.Bits.significand`. -/

/-- The `bit ≤ 1` generalisation of `or_two_pow_add_of_lt`, matching the shape of the implicit-bit
fold `xu`/`yu_` use. -/
private theorem or_mul_two_pow_add_of_lt (a k bit : ℕ) (hbit : bit ≤ 1) (ha : a < 2 ^ k) :
    a ||| bit * 2 ^ k = a + bit * 2 ^ k := by
  interval_cases bit
  · simp
  · simpa using or_two_pow_add_of_lt a k ha

/-- The implicit-bit fold `((e + 0x7FF) >>> 11).toUInt64`, for an exponent field `e` below
`2 ^ 11`, is `1` exactly when `e` is nonzero and `0` when `e` is zero. -/
private theorem toNat_implicitBit_of_lt {e : UInt32} (he : e.toNat < 2 ^ 11) :
    (((e + 0x7FF) >>> 11).toUInt64).toNat = if e.toNat = 0 then 0 else 1 := by
  rw [UInt32.toNat_toUInt64, UInt32.toNat_shiftRight]
  have hadd : (e + 0x7FF).toNat = e.toNat + 2047 := by
    rw [UInt32.toNat_add, show (0x7FF : UInt32).toNat = 2047 from by decide]
    omega
  rw [hadd, show (11 : UInt32).toNat % 32 = 11 from by decide, Nat.shiftRight_eq_div_pow]
  split_ifs with h0 <;> omega

/-- The significand-packing formula `xu`/`yu_` both use, parametrised by the operand `w` and its
already-extracted exponent field `ex`: it computes exactly `8 *` the operand's decoded
significand. -/
private theorem toNat_significand_pack (w : FPR) (ex : UInt32)
    (hex : ex.toNat = (FPR.decode w).exponent) :
    (((w &&& M52) <<< 3) ||| (((ex + 0x7FF) >>> 11).toUInt64 <<< 55)).toNat =
      8 * (FPR.decode w).significand := by
  have hmlt : (w &&& M52).toNat < 2 ^ 52 := by
    rw [toNat_and_M52_eq_mantissa]; exact FPR.decode_mantissa_lt w
  have hA : ((w &&& M52) <<< 3).toNat = (w &&& M52).toNat * 8 := by
    rw [UInt64.toNat_shiftLeft, show (3 : UInt64).toNat % 64 = 3 from by decide,
      Nat.shiftLeft_eq, Nat.mod_eq_of_lt (show (w &&& M52).toNat * 2 ^ 3 < 2 ^ 64 from by omega)]
    norm_num
  have hexlt : ex.toNat < 2 ^ 11 := hex ▸ FPR.decode_exponent_lt w
  have hbit := toNat_implicitBit_of_lt hexlt
  have hB : (((ex + 0x7FF) >>> 11).toUInt64 <<< 55).toNat =
      (if ex.toNat = 0 then 0 else 1) * 2 ^ 55 := by
    rw [UInt64.toNat_shiftLeft, show (55 : UInt64).toNat % 64 = 55 from by decide,
      Nat.shiftLeft_eq, hbit]
    exact Nat.mod_eq_of_lt (by split_ifs <;> norm_num)
  rw [UInt64.toNat_or, hA, hB,
    or_mul_two_pow_add_of_lt ((w &&& M52).toNat * 8) 55 (if ex.toNat = 0 then 0 else 1)
      (by split_ifs <;> omega) (by omega),
    toNat_and_M52_eq_mantissa]
  unfold FPR.Bits.significand
  rw [hex]
  split_ifs <;> ring

/-- The sign-bit extraction `((w >>> 52).toUInt32) >>> 11` recovers the top bit of `w`. -/
private theorem toNat_sx_of (w : FPR) :
    (((w >>> 52).toUInt32) >>> 11).toNat = w.toNat / 2 ^ 63 := by
  rw [UInt32.toNat_shiftRight, toNat_ex_of,
    show (11 : UInt32).toNat % 32 = 11 from by decide, Nat.shiftRight_eq_div_pow,
    Nat.div_div_eq_div_mul, show (2 : ℕ) ^ 52 * 2 ^ 11 = 2 ^ 63 from by norm_num]

/-- The pipeline's `ex` field is exactly `x'`'s decoded exponent field. -/
private theorem addPipeline_ex_eq_exponent (a b : FPR) :
    (addPipeline a b).ex.toNat = (FPR.decode (addPipeline a b).x').exponent := by
  rw [addPipeline_ex, addPipeline_ex_, UInt32.toNat_and, toNat_ex_of,
    show (0x7FF : UInt32).toNat = 2 ^ 11 - 1 from by decide, Nat.and_two_pow_sub_one_eq_mod]
  unfold FPR.decode
  rw [Nat.shiftRight_eq_div_pow]

/-- The pipeline's `ey` field is exactly `y'`'s decoded exponent field. -/
private theorem addPipeline_ey_eq_exponent (a b : FPR) :
    (addPipeline a b).ey.toNat = (FPR.decode (addPipeline a b).y').exponent := by
  rw [addPipeline_ey, addPipeline_ey_, UInt32.toNat_and, toNat_ex_of,
    show (0x7FF : UInt32).toNat = 2 ^ 11 - 1 from by decide, Nat.and_two_pow_sub_one_eq_mod]
  unfold FPR.decode
  rw [Nat.shiftRight_eq_div_pow]

/-- The pipeline's `xu` field packs `8 *` `x'`'s decoded significand. -/
private theorem addPipeline_xu_toNat (a b : FPR) :
    (addPipeline a b).xu.toNat = 8 * (FPR.decode (addPipeline a b).x').significand := by
  rw [addPipeline_xu]
  exact toNat_significand_pack _ _ (addPipeline_ex_eq_exponent a b)

/-- The pipeline's `yu_` field packs `8 *` `y'`'s decoded significand. -/
private theorem addPipeline_yuRaw_toNat (a b : FPR) :
    (addPipeline a b).yu_.toNat = 8 * (FPR.decode (addPipeline a b).y').significand := by
  rw [addPipeline_yu_]
  exact toNat_significand_pack _ _ (addPipeline_ey_eq_exponent a b)

/-- The sign-bit extraction `((w >>> 52).toUInt32) >>> 11` recovers exactly `FPR.decode`'s sign
field, as a `0`/`1` natural number. -/
private theorem toNat_sign_field_of (w : FPR) :
    (((w >>> 52).toUInt32) >>> 11).toNat = if (FPR.decode w).sign then 1 else 0 := by
  rw [toNat_sx_of]
  have hb : w.toNat < 2 ^ 64 := w.toNat_lt_size
  have hb2 : w.toNat / 2 ^ 63 < 2 := by omega
  unfold FPR.decode
  rw [Nat.testBit_eq_decide_div_mod_eq]
  interval_cases h : (w.toNat / 2 ^ 63) <;> simp_all

/-- The pipeline's `sx` field is exactly `x'`'s decoded sign bit. -/
private theorem addPipeline_sx_toNat (a b : FPR) :
    (addPipeline a b).sx.toNat = if (FPR.decode (addPipeline a b).x').sign then 1 else 0 := by
  rw [addPipeline_sx, addPipeline_ex_, toNat_sign_field_of]

/-- The pipeline's `sy` field is exactly `y'`'s decoded sign bit. -/
private theorem addPipeline_sy_toNat (a b : FPR) :
    (addPipeline a b).sy.toNat = if (FPR.decode (addPipeline a b).y').sign then 1 else 0 := by
  rw [addPipeline_sy, addPipeline_ey_, toNat_sign_field_of]

/-! ### Step 4: word-level helpers for the remaining pipeline steps

Small `UInt32` / `UInt64` / `ℝ` facts used by the alignment, sign-combination and
renormalisation steps below. Each isolates one wraparound- or masking-freedom obligation so the
later steps read as plain arithmetic. -/

/-- Reducing a shift amount below `64` mod `64` is the identity. -/
theorem toNat_and_63_of_lt {n : UInt32} (h : n.toNat < 64) :
    (n &&& 63).toNat = n.toNat := by
  rw [UInt32.toNat_and, show (63 : UInt32).toNat = 2 ^ 6 - 1 from by decide,
    Nat.and_two_pow_sub_one_eq_mod]
  exact Nat.mod_eq_of_lt (by omega)

/-- Divide a two-sided integer ulp bracket through by the (positive) scale. -/
private theorem real_bracket_div {A V c : ℝ} (hc : 0 < c) (h1 : A * c < V + c)
    (h2 : V < A * c + c) : A < V / c + 1 ∧ V / c < A + 1 := by
  constructor
  · rw [← sub_lt_iff_lt_add, lt_div_iff₀ hc]
    have hr : (A - 1) * c = A * c - c := by ring
    rw [hr]
    linarith
  · rw [div_lt_iff₀ hc]
    have hr : (A + 1) * c = A * c + c := by ring
    rw [hr]
    linarith

/-! ### Step 4a: the exponent chain

The pipeline's exponents travel through `ex → ex' → ex'' → ex'''` as `UInt32` and `Int32` words.
Each step below shows the corresponding machine operation computes the plain integer arithmetic
it is meant to denote, with no wraparound artefact surviving. -/

/-- `UInt32` subtraction by the literal `1078`, reinterpreted as a signed `Int32`, computes the
plain integer difference whenever the minuend stays comfortably below `2 ^ 31` (in particular for
any valid IEEE-754 biased exponent field, which never reaches `2 ^ 11`; see `addPipeline_ex_lt`
below). -/
private theorem toInt_sub_1078_toInt32_of_lt {ex : UInt32} (h : ex.toNat < 2 ^ 31) :
    (ex - 1078).toInt32.toInt = (ex.toNat : ℤ) - 1078 := by
  rw [UInt32.toInt32_sub, Int32.toInt_sub,
    toInt_toInt32_of_lt h,
    toInt_toInt32_of_lt (show (1078 : UInt32).toNat < 2 ^ 31 by decide),
    show (1078 : UInt32).toNat = 1078 from by decide]
  apply Int.bmod_eq_of_le_mul_two <;> omega

/-- A `FPR.Bits.magKey` ordering forces an exponent ordering: a strictly larger exponent always
dominates any mantissa difference below `2 ^ 52`. -/
private theorem exponent_le_of_magKey_le {b1 b2 : FPR.Bits} (hm1 : b1.mantissa < 2 ^ 52)
    (hm2 : b2.mantissa < 2 ^ 52) (h : b1.magKey ≤ b2.magKey) : b1.exponent ≤ b2.exponent := by
  unfold FPR.Bits.magKey at h
  by_contra hc
  push Not at hc
  have hge : (b2.exponent + 1) * 2 ^ 52 ≤ b1.exponent * 2 ^ 52 := Nat.mul_le_mul_right _ hc
  omega

/-- The pipeline's aligned exponent fields obey `ey ≤ ex`: `x'` always carries the
larger-or-equal magnitude (`addPipeline_swap_cases`), so its exponent field dominates `y'`'s. -/
private theorem addPipeline_ey_le_ex (a b : FPR) :
    (addPipeline a b).ey.toNat ≤ (addPipeline a b).ex.toNat := by
  have hmag := (addPipeline_swap_cases a b).2
  rw [addPipeline_ex_eq_exponent, addPipeline_ey_eq_exponent]
  exact exponent_le_of_magKey_le (FPR.decode_mantissa_lt _) (FPR.decode_mantissa_lt _) hmag

/-- The pipeline's exponent-gap field `n` is exactly the non-negative gap `ex - ey`: `x'`
always carries the larger-or-equal magnitude, so the subtraction never wraps. -/
private theorem addPipeline_n_toNat (a b : FPR) :
    (addPipeline a b).n.toNat = (addPipeline a b).ex.toNat - (addPipeline a b).ey.toNat := by
  rw [addPipeline_n]
  exact toNat_sub_of_le_uint32 (addPipeline_ey_le_ex a b)

/-- The pipeline's `ex` field is always a valid biased exponent, unconditionally (no normality
needed): it is `x'`'s decoded exponent field, and every decoded exponent field is below `2 ^ 11`
(`FPR.decode_exponent_lt`). -/
private theorem addPipeline_ex_lt (a b : FPR) : (addPipeline a b).ex.toNat < 2 ^ 11 := by
  rw [addPipeline_ex_eq_exponent]
  exact FPR.decode_exponent_lt _

/-- The pipeline's exponent gap is always a genuine small gap, below `2 ^ 11`: it is a difference
of two `11`-bit exponent fields taken in the non-wrapping order. -/
private theorem addPipeline_n_lt (a b : FPR) : (addPipeline a b).n.toNat < 2 ^ 11 := by
  have := addPipeline_n_toNat a b
  have := addPipeline_ex_lt a b
  omega

/-- The pipeline's `ex'` field, as a plain integer: `x'`'s exponent field minus `1078`,
unconditionally (no normality of the operands needed — this only uses the generic exponent-field
bound `addPipeline_ex_lt`). -/
private theorem addPipeline_ex'_toInt (a b : FPR) :
    (addPipeline a b).ex'.toInt = ((addPipeline a b).ex.toNat : ℤ) - 1078 := by
  rw [addPipeline_ex']
  have hlt := addPipeline_ex_lt a b
  exact toInt_sub_1078_toInt32_of_lt (by omega)

/-- The pipeline's `ex''` field, as a plain integer: `ex'` decremented by the renormalising
shift count `c` (the exponent-decrement fact `toInt_sub_lzcnt64_nonzero_or_one_toInt32`,
specialised to `m := zu`, `e := ex'`). -/
private theorem addPipeline_ex''_toInt (a b : FPR) :
    (addPipeline a b).ex''.toInt =
      (addPipeline a b).ex'.toInt - ((addPipeline a b).c.toNat : ℤ) := by
  rw [addPipeline_ex'', addPipeline_c]
  apply toInt_sub_lzcnt64_nonzero_or_one_toInt32
  have hb := addPipeline_ex'_toInt a b
  have hc := lzcnt64_nonzero_toNat_le ((addPipeline a b).zu ||| 1)
  omega

/-- The pipeline's final exponent `ex'''`, as a plain integer, in terms of `ex'` and the
renormalising shift count `c`. -/
private theorem addPipeline_ex'''_toInt (a b : FPR) :
    (addPipeline a b).ex'''.toInt =
      (addPipeline a b).ex'.toInt - ((addPipeline a b).c.toNat : ℤ) + 9 := by
  have hex := addPipeline_ex_lt a b
  have hex' := addPipeline_ex'_toInt a b
  have hc := lzcnt64_nonzero_toNat_le ((addPipeline a b).zu ||| 1)
  rw [← addPipeline_c] at hc
  rw [addPipeline_ex''', Int32.toInt_add, addPipeline_ex''_toInt,
    show ((9 : Int32).toInt) = 9 from by decide]
  apply Int.bmod_eq_of_le_mul_two <;> omega

/-- The pipeline's `xu` field, on the same `2 ^ ex'.toInt` scale as its exponent field `ex'`,
denotes *exactly* `x'`'s real magnitude — no rounding error at all, unlike the aligned `yu`
side. -/
private theorem addPipeline_abs_toReal_x'_eq (a b : FPR)
    (hx0 : (FPR.decode (addPipeline a b).x').exponent ≠ 0)
    (hx2047 : (FPR.decode (addPipeline a b).x').exponent ≠ 2047) :
    |toReal (addPipeline a b).x'| =
      ((addPipeline a b).xu.toNat : ℝ) * (2 : ℝ) ^ (addPipeline a b).ex'.toInt := by
  rw [addPipeline_xu_toNat, addPipeline_ex'_toInt, addPipeline_ex_eq_exponent]
  change |(FPR.decode (addPipeline a b).x').toReal| = _
  rw [abs_toReal_eq_significand_mul_two_zpow hx0 hx2047]
  push_cast
  rw [show (((FPR.decode (addPipeline a b).x').exponent : ℤ) - 1078)
      = (((FPR.decode (addPipeline a b).x').exponent : ℤ) - 1075) + (-3 : ℤ) by ring,
    zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
  ring

/-! ### Step 4b: the alignment shift

`FPR.add` aligns the smaller operand by a sticky right shift, after first flushing it to zero once
the exponent gap reaches `60`. This section identifies the kernel's masked fold with `stickyShift`,
gives the flush condition in closed form, and brackets the aligned significand within one unit in
the last place of the exactly-scaled one. -/

/-- The alignment shift of `FPR.add` denotes `stickyShift`. -/
private theorem addPipeline_yu_toNat (a b : FPR) :
    (addPipeline a b).yu.toNat
      = stickyShift (addPipeline a b).yu'.toNat ((addPipeline a b).n &&& 63).toNat :=
  toNat_fpr_ursh_or_fold (addPipeline a b).yu' (addPipeline a b).n

/-- Bit `31` of the wrapping `UInt32` difference `n - 60`: it is clear exactly on the window
`60 ≤ n < 2 ^ 31 + 60`, and set everywhere else (both for `n < 60`, where the subtraction wraps,
and for the top half `n ≥ 2 ^ 31 + 60`). -/
private theorem toNat_flushSelector (n : UInt32) :
    ((n - 60) >>> 31 : UInt32).toNat = if 60 ≤ n.toNat ∧ n.toNat < 2 ^ 31 + 60 then 0 else 1 := by
  have hn : n.toNat < 2 ^ 32 := n.toNat_lt_size
  have h31 : (2 : ℕ) ^ 31 = 2147483648 := by norm_num
  have h32 : (2 : ℕ) ^ 32 = 4294967296 := by norm_num
  rw [toNat_shiftRight_31_uint32, UInt32.toNat_sub,
    show (60 : UInt32).toNat = 60 from by decide]
  split_ifs <;> omega

/-- The alignment flush mask of `FPR.add`, in closed form. -/
private theorem flushMask_eq (n : UInt32) :
    (0 : UInt64) - ((n - 60) >>> 31).toUInt64
      = if 60 ≤ n.toNat ∧ n.toNat < 2 ^ 31 + 60 then 0 else 0xFFFFFFFFFFFFFFFF := by
  have h := toNat_flushSelector n
  by_cases hc : 60 ≤ n.toNat ∧ n.toNat < 2 ^ 31 + 60
  · rw [ite_eq_left hc] at h
    have hsel : ((n - 60) >>> 31 : UInt32) = 0 := by rw [← UInt32.toNat_inj, h]; rfl
    rw [ite_eq_left hc, hsel]
    decide
  · rw [ite_eq_right hc] at h
    have hsel : ((n - 60) >>> 31 : UInt32) = 1 := by rw [← UInt32.toNat_inj, h]; rfl
    rw [ite_eq_right hc, hsel]
    decide

/-- Full characterisation of the flushed operand `yu'`. -/
private theorem addPipeline_yu'_eq (a b : FPR) :
    (addPipeline a b).yu'
      = if 60 ≤ (addPipeline a b).n.toNat ∧ (addPipeline a b).n.toNat < 2 ^ 31 + 60
        then 0 else (addPipeline a b).yu_ := by
  rw [addPipeline_yu', flushMask_eq]
  split_ifs
  · exact and_zero_uint64 _
  · exact and_allOnes_uint64 _

/-- No flush below an exponent gap of `60`. -/
private theorem addPipeline_yu'_eq_yuRaw (a b : FPR) (h : (addPipeline a b).n.toNat < 60) :
    (addPipeline a b).yu' = (addPipeline a b).yu_ := by
  rw [addPipeline_yu'_eq, ite_eq_right (by omega)]

/-- Flush to zero from an exponent gap of `60` on. -/
private theorem addPipeline_yu'_eq_zero (a b : FPR) (h60 : 60 ≤ (addPipeline a b).n.toNat) :
    (addPipeline a b).yu' = 0 := by
  have hb := addPipeline_n_lt a b
  rw [addPipeline_yu'_eq, ite_eq_left ⟨h60, by omega⟩]

/-- The flushed operand contributes nothing to the sum. -/
private theorem addPipeline_yu_eq_zero (a b : FPR) (h60 : 60 ≤ (addPipeline a b).n.toNat) :
    (addPipeline a b).yu = 0 := by
  have h0 : (addPipeline a b).yu.toNat = 0 := by
    rw [addPipeline_yu_toNat, addPipeline_yu'_eq_zero a b h60]
    exact (stickyShift_eq_zero_iff _ _).mpr rfl
  rw [← UInt64.toNat_inj, h0]
  rfl

/-- The two-sided integer ulp bracket relating the aligned significand to the exactly-scaled
one. -/
private theorem addPipeline_yu_nat_bracket (a b : FPR) :
    (addPipeline a b).yu.toNat * 2 ^ ((addPipeline a b).n &&& 63).toNat
        < (addPipeline a b).yu'.toNat + 2 ^ ((addPipeline a b).n &&& 63).toNat
      ∧ (addPipeline a b).yu'.toNat
        < (addPipeline a b).yu.toNat * 2 ^ ((addPipeline a b).n &&& 63).toNat
          + 2 ^ ((addPipeline a b).n &&& 63).toNat := by
  rw [addPipeline_yu_toNat]
  exact ⟨stickyShift_mul_lt _ _, lt_stickyShift_mul_add _ _⟩

/-- The bracket of `addPipeline_yu_nat_bracket`, divided through by the alignment scale. -/
private theorem addPipeline_yu_real_bracket (a b : FPR) :
    ((addPipeline a b).yu.toNat : ℝ)
        < ((addPipeline a b).yu'.toNat : ℝ) / 2 ^ ((addPipeline a b).n &&& 63).toNat + 1
      ∧ ((addPipeline a b).yu'.toNat : ℝ) / 2 ^ ((addPipeline a b).n &&& 63).toNat
        < ((addPipeline a b).yu.toNat : ℝ) + 1 := by
  obtain ⟨h1, h2⟩ := addPipeline_yu_nat_bracket a b
  have hp : (0 : ℝ) < 2 ^ ((addPipeline a b).n &&& 63).toNat := by positivity
  have h1' : ((addPipeline a b).yu.toNat : ℝ) * 2 ^ ((addPipeline a b).n &&& 63).toNat
      < ((addPipeline a b).yu'.toNat : ℝ) + 2 ^ ((addPipeline a b).n &&& 63).toNat := by
    exact_mod_cast h1
  have h2' : ((addPipeline a b).yu'.toNat : ℝ)
      < ((addPipeline a b).yu.toNat : ℝ) * 2 ^ ((addPipeline a b).n &&& 63).toNat
        + 2 ^ ((addPipeline a b).n &&& 63).toNat := by
    exact_mod_cast h2
  exact real_bracket_div hp h1' h2'

/-- The ulp bracket, keyed on the *pre-flush* significand word `yu_` and the raw exponent gap
`n`, in the shape the later rounding step consumes. -/
private theorem addPipeline_yu_real_bracket_yuRaw (a b : FPR)
    (h : (addPipeline a b).n.toNat < 60) :
    ((addPipeline a b).yu.toNat : ℝ)
        < ((addPipeline a b).yu_.toNat : ℝ) / 2 ^ (addPipeline a b).n.toNat + 1
      ∧ ((addPipeline a b).yu_.toNat : ℝ) / 2 ^ (addPipeline a b).n.toNat
        < ((addPipeline a b).yu.toNat : ℝ) + 1 := by
  have hk : ((addPipeline a b).n &&& 63).toNat = (addPipeline a b).n.toNat :=
    toNat_and_63_of_lt (by omega)
  have hv : (addPipeline a b).yu'.toNat = (addPipeline a b).yu_.toNat := by
    rw [addPipeline_yu'_eq_yuRaw a b h]
  have := addPipeline_yu_real_bracket a b
  rwa [hk, hv] at this

/-! ### Step 4c: the sign combination

`FPR.add` combines the two aligned significands with a single masked expression: the mask `dm` is
all-ones on differing signs (subtract) and zero on matching signs (add). -/

private theorem dm_eq_zero_of_sx_eq_sy (sx sy : UInt32) (hsx : sx = 0 ∨ sx = 1)
    (h : sx = sy) : (0 : UInt64) - (sx ^^^ sy).toUInt64 = 0 := by
  subst h
  rcases hsx with hsx | hsx <;> subst hsx <;> decide

private theorem dm_eq_allOnes_of_sx_ne_sy (sx sy : UInt32) (hsx : sx = 0 ∨ sx = 1)
    (hsy : sy = 0 ∨ sy = 1) (h : sx ≠ sy) :
    (0 : UInt64) - (sx ^^^ sy).toUInt64 = (0 : UInt64) - 1 := by
  rcases hsx with hsx | hsx <;> rcases hsy with hsy | hsy <;> subst hsx <;> subst hsy <;>
    first
    | decide
    | exact absurd rfl h

private theorem zu_eq_add_of_dm_zero (xu yu dm : UInt64) (h : dm = 0) :
    xu + yu - (dm &&& (yu <<< 1)) = xu + yu := by
  subst h; simp

private theorem zu_eq_sub_of_dm_allOnes (xu yu dm : UInt64) (h : dm = (0 : UInt64) - 1) :
    xu + yu - (dm &&& (yu <<< 1)) = xu - yu := by
  subst h
  rw [allOnes_and]
  apply UInt64.toNat_inj.mp
  rw [UInt64.toNat_sub, UInt64.toNat_add, UInt64.toNat_sub, toNat_shiftLeft_one]
  have hxu : xu.toNat < 2 ^ 64 := xu.toNat_lt_size
  have hyu : yu.toNat < 2 ^ 64 := yu.toNat_lt_size
  omega

/-- The pipeline's `sx` field is a packed sign bit, hence `0` or `1`. -/
private theorem addPipeline_sx_eq_zero_or_one (a b : FPR) :
    (addPipeline a b).sx = 0 ∨ (addPipeline a b).sx = 1 := by
  have h := addPipeline_sx_toNat a b
  rcases Classical.em (FPR.decode (addPipeline a b).x').sign with hc | hc
  · rw [ite_eq_left hc] at h; right; apply UInt32.toNat_inj.mp; rw [h]; decide
  · rw [ite_eq_right hc] at h; left; apply UInt32.toNat_inj.mp; rw [h]; decide

/-- The pipeline's `sy` field is a packed sign bit, hence `0` or `1`. -/
private theorem addPipeline_sy_eq_zero_or_one (a b : FPR) :
    (addPipeline a b).sy = 0 ∨ (addPipeline a b).sy = 1 := by
  have h := addPipeline_sy_toNat a b
  rcases Classical.em (FPR.decode (addPipeline a b).y').sign with hc | hc
  · rw [ite_eq_left hc] at h; right; apply UInt32.toNat_inj.mp; rw [h]; decide
  · rw [ite_eq_right hc] at h; left; apply UInt32.toNat_inj.mp; rw [h]; decide

/-- On matching (post-swap) signs, `FPR.add`'s combined significand is the plain sum. -/
private theorem addPipeline_zu_eq_add_of_sx_eq_sy (a b : FPR)
    (h : (addPipeline a b).sx = (addPipeline a b).sy) :
    (addPipeline a b).zu = (addPipeline a b).xu + (addPipeline a b).yu := by
  rw [addPipeline_zu, addPipeline_dm]
  exact zu_eq_add_of_dm_zero _ _ _
    (dm_eq_zero_of_sx_eq_sy _ _ (addPipeline_sx_eq_zero_or_one a b) h)

/-- On differing (post-swap) signs, `FPR.add`'s combined significand is the (wrapping)
difference. -/
private theorem addPipeline_zu_eq_sub_of_sx_ne_sy (a b : FPR)
    (h : (addPipeline a b).sx ≠ (addPipeline a b).sy) :
    (addPipeline a b).zu = (addPipeline a b).xu - (addPipeline a b).yu := by
  rw [addPipeline_zu, addPipeline_dm]
  exact zu_eq_sub_of_dm_allOnes _ _ _
    (dm_eq_allOnes_of_sx_ne_sy _ _ (addPipeline_sx_eq_zero_or_one a b)
      (addPipeline_sy_eq_zero_or_one a b) h)

/-- The no-underflow case of `FPR.add`'s subtraction step, in the real pipeline's own fields:
whenever the smaller-magnitude aligned significand `yu` does not exceed `xu`, the differing-signs
combined significand `zu` denotes the true natural-number difference `xu.toNat - yu.toNat`, with
no wraparound. -/
private theorem addPipeline_zu_toNat_eq_of_sx_ne_sy (a b : FPR)
    (h : (addPipeline a b).sx ≠ (addPipeline a b).sy)
    (hle : (addPipeline a b).yu.toNat ≤ (addPipeline a b).xu.toNat) :
    (addPipeline a b).zu.toNat = (addPipeline a b).xu.toNat - (addPipeline a b).yu.toNat := by
  rw [addPipeline_zu_eq_sub_of_sx_ne_sy a b h]
  exact toNat_sub_of_le_uint64 _ _ hle

/-! ### Step 4d: renormalisation, and the exact-cancellation branch -/

private theorem zu'_toNat_eq (zu : UInt64) (c_add : UInt32) (hzu : zu ≠ 0)
    (hc : c_add = lzcnt64_nonzero (zu ||| 1)) :
    (fpr_ulsh zu c_add).toNat = zu.toNat * 2 ^ c_add.toNat := by
  subst hc
  exact fpr_ulsh_lzcnt64_toNat zu hzu

private theorem ex''_toInt_eq (ex' ex'' : Int32) (c_add : UInt32) (zu : UInt64)
    (hc : c_add = lzcnt64_nonzero (zu ||| 1)) (hex' : ex'' = ex' - c_add.toInt32)
    (hbound : -(2 ^ 31 : ℤ) + 63 ≤ ex'.toInt) :
    ex''.toInt = ex'.toInt - (c_add.toNat : ℤ) := by
  subst hc; subst hex'
  apply toInt_sub_lzcnt64_nonzero_or_one_toInt32
  have := lzcnt64_nonzero_toNat_le (zu ||| 1)
  push_cast
  omega

/-- Renormalisation is value-preserving: the pair `(zu', ex'')` denotes the same real value as
the pre-renormalisation pair `(zu, ex')`, for any nonzero `zu`. -/
private theorem renorm_value_preserving (zu : UInt64) (ex' ex'' : Int32) (c_add : UInt32)
    (hzu : zu ≠ 0) (hc : c_add = lzcnt64_nonzero (zu ||| 1)) (hex' : ex'' = ex' - c_add.toInt32)
    (hbound : -(2 ^ 31 : ℤ) + 63 ≤ ex'.toInt) :
    ((fpr_ulsh zu c_add).toNat : ℝ) * (2 : ℝ) ^ ex''.toInt
      = (zu.toNat : ℝ) * (2 : ℝ) ^ ex'.toInt := by
  have h1 := zu'_toNat_eq zu c_add hzu hc
  have h2 := ex''_toInt_eq ex' ex'' c_add zu hc hex' hbound
  rw [h1, h2]
  push_cast
  rw [mul_assoc, ← zpow_natCast (2 : ℝ) c_add.toNat, ← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
  congr 2
  ring

/-- Renormalisation is value-preserving, in the real pipeline's own fields: the pair
`(zu', ex'')` from `FPR.add`'s renormalising step denotes the same real value as the
pre-renormalisation pair `(zu, ex')`, given a bound on `ex'` (its actual magnitude, near `±1100`,
is far inside this range) ruling out `Int32` underflow in the exponent decrement. -/
private theorem addPipeline_renorm_value_preserving (a b : FPR)
    (hzu : (addPipeline a b).zu ≠ 0)
    (hbound : -(2 ^ 31 : ℤ) + 63 ≤ (addPipeline a b).ex'.toInt) :
    ((addPipeline a b).zu'.toNat : ℝ) * (2 : ℝ) ^ (addPipeline a b).ex''.toInt
      = ((addPipeline a b).zu.toNat : ℝ) * (2 : ℝ) ^ (addPipeline a b).ex'.toInt := by
  have h := renorm_value_preserving (addPipeline a b).zu (addPipeline a b).ex'
    (addPipeline a b).ex'' (addPipeline a b).c hzu (addPipeline_c a b) (addPipeline_ex'' a b)
    hbound
  rwa [← addPipeline_zu'] at h

private theorem addPipeline_zu'_eq_zero_of_zu_eq_zero (a b : FPR)
    (h : (addPipeline a b).zu = 0) : (addPipeline a b).zu' = 0 := by
  rw [addPipeline_zu', h]
  unfold fpr_ulsh
  simp

private theorem addPipeline_zu''_eq_zero_of_zu_eq_zero (a b : FPR)
    (h : (addPipeline a b).zu = 0) : (addPipeline a b).zu'' = 0 := by
  have hzu' := addPipeline_zu'_eq_zero_of_zu_eq_zero a b h
  rw [addPipeline_zu'']
  have hmask : (0x1FF : UInt64) = (1 : UInt64) <<< (9 : UInt64) - 1 := by decide
  rw [hmask]
  exact (or_fold_shiftRight_eq_zero_iff (addPipeline a b).zu' (9 : UInt64) (by decide)).mpr hzu'

/-- When `FPR.add`'s combined significand `zu` is exactly zero (the exact-cancellation case),
`FPR.add x y` denotes the real number `0`. This is the branch left uncovered by the main
normalized-significand argument, which assumes `2 ^ 54 ≤ zu''`. -/
private theorem add_toReal_eq_zero_of_zu_eq_zero (x y : FPR) (h : (addPipeline x y).zu = 0)
    (hs : (addPipeline x y).sx.toUInt64.toNat ≤ 1) : toReal (FPR.add x y) = 0 := by
  unfold toReal
  rw [add_eq_make_z, addPipeline_zu''_eq_zero_of_zu_eq_zero x y h]
  exact toRealBits_make_z_of_zero _ _ hs

/-- The exact-cancellation branch, hypothesis-free: the sign-field bound of
`add_toReal_eq_zero_of_zu_eq_zero` always holds structurally (`sx` is a packed sign bit, hence `0`
or `1`), so no side condition beyond `zu = 0` is needed. -/
private theorem add_toReal_eq_zero_of_zu_eq_zero' (x y : FPR) (h : (addPipeline x y).zu = 0) :
    toReal (FPR.add x y) = 0 := by
  apply add_toReal_eq_zero_of_zu_eq_zero x y h
  rcases addPipeline_sx_eq_zero_or_one x y with hc | hc <;> rw [hc] <;> decide

/-! ## (I) The assembly bound at the top exponent -/

private theorem abs_toRealBits_make_z_sub_le_of_no_carry (s : UInt64) (e : Int32) (m : UInt64)
    (hs : s.toNat ≤ 1) (he1 : -1076 ≤ e.toInt) (he2 : e.toInt ≤ 969)
    (hm1 : 2 ^ 54 ≤ m.toNat) (hm2 : m.toNat < 2 ^ 55)
    (hnc : roundQuarterTiesEven m.toNat < 2 ^ 53) :
    |toRealBits (make_z s e m) -
        (if s.toNat = 1 then (-1 : ℝ) else 1) * (m.toNat : ℝ) * (2 : ℝ) ^ e.toInt| ≤
      (2 : ℝ) ^ (-(53 : ℤ)) *
        |(if s.toNat = 1 then (-1 : ℝ) else 1) * (m.toNat : ℝ) * (2 : ℝ) ^ e.toInt| := by
  rw [FPR.make_z_eq_make s e m hm1 hm2]
  exact abs_toRealBits_make_sub_le_of_no_carry s e m hs he1 he2 hm1 hm2 hnc

/-! ## (III) Normality and field bounds along the pipeline -/

private theorem addPipeline_x'_isNormal (a b : FPR) (ha : FPR.IsNormal a) (hb : FPR.IsNormal b) :
    FPR.IsNormal (addPipeline a b).x' := by
  rcases (addPipeline_swap_cases a b).1 with ⟨hx, -⟩ | ⟨hx, -⟩ <;> rw [hx] <;> assumption

private theorem addPipeline_y'_isNormal (a b : FPR) (ha : FPR.IsNormal a) (hb : FPR.IsNormal b) :
    FPR.IsNormal (addPipeline a b).y' := by
  rcases (addPipeline_swap_cases a b).1 with ⟨-, hy⟩ | ⟨-, hy⟩ <;> rw [hy] <;> assumption

private theorem addPipeline_sum_eq (a b : FPR) :
    toReal (addPipeline a b).x' + toReal (addPipeline a b).y' = toReal a + toReal b := by
  rcases (addPipeline_swap_cases a b).1 with ⟨hx, hy⟩ | ⟨hx, hy⟩
  · rw [hx, hy]
  · rw [hx, hy]
    exact add_comm _ _

/-- A nonzero exponent field puts the significand in `[2 ^ 52, 2 ^ 53)`. -/
theorem significand_mem_of_isNormal {b : FPR.Bits} (h0 : b.exponent ≠ 0)
    (hm : b.mantissa < 2 ^ 52) : 2 ^ 52 ≤ b.significand ∧ b.significand < 2 ^ 53 := by
  unfold FPR.Bits.significand
  rw [ite_eq_right h0]
  omega

private theorem addPipeline_xu_mem (a b : FPR) (ha : FPR.IsNormal a) (hb : FPR.IsNormal b) :
    2 ^ 55 ≤ (addPipeline a b).xu.toNat ∧ (addPipeline a b).xu.toNat < 2 ^ 56 := by
  have h := significand_mem_of_isNormal (addPipeline_x'_isNormal a b ha hb).1
    (FPR.decode_mantissa_lt (addPipeline a b).x')
  rw [addPipeline_xu_toNat]
  omega

private theorem addPipeline_yuRaw_mem (a b : FPR) (ha : FPR.IsNormal a) (hb : FPR.IsNormal b) :
    2 ^ 55 ≤ (addPipeline a b).yu_.toNat ∧ (addPipeline a b).yu_.toNat < 2 ^ 56 := by
  have h := significand_mem_of_isNormal (addPipeline_y'_isNormal a b ha hb).1
    (FPR.decode_mantissa_lt (addPipeline a b).y')
  rw [addPipeline_yuRaw_toNat]
  omega

end

end Falcon.Concrete.FPRBridge
