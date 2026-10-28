/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import LatticeCrypto.Falcon.Concrete.FPR

/-!
# FloatLike: Typeclass for IEEE-754-like Floating-Point Operations

Abstracts over floating-point arithmetic so that Falcon algorithms can be
written generically and instantiated with either:
- `FPR` (UInt64 integer emulation, bit-exact with c-fn-dsa's plain path)
- `Float` (Lean's native hardware double, fast but opaque to proofs)

The typeclass captures exactly the operations used by the Falcon signing
pipeline: FFT, LDL decomposition, discrete Gaussian sampling, and the
FACCT exponential approximation.
-/

public section


/-- Floating-point-like operations needed by the executable Falcon implementation. -/
class FloatLike (F : Type) where
  /-- The value `0` (`FPR_ZERO` in c-fn-dsa). -/
  zero : F
  /-- The value `1` (`FPR_ONE` in c-fn-dsa). -/
  one : F
  /-- Negation (`fpr_neg` in c-fn-dsa). -/
  neg : F → F
  /-- Rounded addition (`fpr_add` in c-fn-dsa). -/
  add : F → F → F
  /-- Rounded subtraction (`fpr_sub` in c-fn-dsa). -/
  sub : F → F → F
  /-- Rounded multiplication (`fpr_mul` in c-fn-dsa). -/
  mul : F → F → F
  /-- Rounded division (`fpr_div` in c-fn-dsa). -/
  div : F → F → F
  /-- Rounded square root of a nonnegative value (`fpr_sqrt` in c-fn-dsa). -/
  sqrt : F → F
  /-- Conversion of a 64-bit signed integer (`fpr_of` in c-fn-dsa). -/
  ofInt : Int64 → F
  /-- Conversion of a 32-bit signed integer (`fpr_of32` in c-fn-dsa). -/
  ofInt32 : Int32 → F
  /-- `scaled i sc` is the value `i · 2^sc` (`fpr_scaled` in c-fn-dsa). -/
  scaled : Int64 → Int32 → F
  /-- Rounding to the nearest integer, ties to even (`fpr_rint` in c-fn-dsa). -/
  rint : F → Int64
  /-- Rounding toward negative infinity (`fpr_floor` in c-fn-dsa). -/
  floor_ : F → Int64
  /-- Returns ⌊2^63 · ccs · exp(-x)⌋ as a UInt64.
  For FPR this is the FACCT polynomial; for Float this uses hardware exp. -/
  expm_p63 : F → F → UInt64
  /-- Convert a raw IEEE-754 double bit pattern (stored as UInt64) to `F`.
  For FPR (= UInt64), this is the identity. For Float, this decodes the bits. -/
  ofRawFPR : UInt64 → F

namespace FloatLike

variable {F : Type} [FloatLike F]

/-- The constant `1 / 2` in a `FloatLike` type. -/
@[inline] def half : F := div one (add one one)
/-- The constant `2` in a `FloatLike` type. -/
@[inline] def two : F := add one one
/-- Square a `FloatLike` value. -/
@[inline] def sqr (x : F) : F := mul x x
/-- Multiplicative inverse in a `FloatLike` type. -/
@[inline] def inv (x : F) : F := div one x

end FloatLike

/-! ## FPR instance -/

open Falcon.Concrete.FPR in
/-- The bit-exact Falcon floating-point backend based on `FPR`. -/
instance : FloatLike FPR where
  zero := zero
  one := one
  neg := neg
  add := add
  sub := sub
  mul := mul
  div := div
  sqrt := sqrt
  ofInt := ofInt
  ofInt32 x := ofInt x.toInt64
  scaled := scaled
  rint := rint
  floor_ := floor_
  expm_p63 := expm_p63
  ofRawFPR := id

/-! ## Float instance -/

private def floatOfInt64 (i : Int64) : Float :=
  if i.toInt >= 0 then Float.ofNat i.toInt.toNat
  else Float.neg (Float.ofNat (-i.toInt).toNat)

private def floatOfInt32 (i : Int32) : Float := floatOfInt64 i.toInt64

private def floatScaled (i : Int64) (sc : Int32) : Float :=
  (floatOfInt64 i).scaleB sc.toInt

private def floatExpmP63 (x ccs : Float) : UInt64 :=
  let v := ccs * Float.exp (-x)
  let twoTo63 : Float := 9223372036854775808.0
  let result := v * twoTo63
  if result <= 0.0 then 0
  else result.toUInt64

private def floatFloorInt64 (x : Float) : Int64 :=
  let r := Float.floor x
  if r >= 0.0 then r.toUInt64.toInt64
  else (0 : Int64) - ((-r).toUInt64).toInt64

private def floatRint (x : Float) : Int64 :=
  let floorInt := floatFloorInt64 x
  let frac := x - Float.floor x
  if frac < 0.5 then
    floorInt
  else if frac > 0.5 then
    floorInt + 1
  else if (floorInt.toUInt64 &&& 1) == 0 then
    floorInt
  else
    floorInt + 1

/-- The fast native-`Float` Falcon floating-point backend. -/
@[no_expose] instance : FloatLike Float where
  zero := 0.0
  one := 1.0
  neg := Float.neg
  add := (· + ·)
  sub := (· - ·)
  mul := (· * ·)
  div := (· / ·)
  sqrt x := if x > 0.0 then Float.sqrt x else 0.0
  ofInt := floatOfInt64
  ofInt32 := floatOfInt32
  scaled := floatScaled
  rint := floatRint
  floor_ := floatFloorInt64
  expm_p63 := floatExpmP63
  ofRawFPR := Float.ofBits
