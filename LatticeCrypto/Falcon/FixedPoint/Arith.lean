/-
Copyright (c) 2026 XC0R. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XC0R
-/

module
public import LatticeCrypto.Falcon.FFTStages

/-!
# Fixed-point arithmetic with 64 fractional bits

A fixed-point register with 64 fractional bits holds a real on the grid `2⁻⁶⁴ · ℤ`. `Arith64` is
the arithmetic of an implementation in that format: one deterministic function per operation,
each with its error bound.

- `rnd` reads a real onto the grid, within `2⁻⁶⁵` (round to nearest, any tie rule);
- `mul` is the complex product of two registers, within `√2 · 2⁻⁶⁴` (four real products, each
  rounded within `2⁻⁶⁵` and combined exactly, or one rounding per component);
- `tw` is the twiddle table, within `0.7072 · 2⁻⁶⁴` of `Falcon.FFTStages.twiddle` (each
  component rounded to nearest, `√2 · 2⁻⁶⁵ ≤ 0.7072 · 2⁻⁶⁴`).

Additions, subtractions and negations are exact, and integers are held exactly. The fields need to
agree with an implementation only on the values it computes.

Register overflow is not represented: `Arith64` places no bound on the magnitude of a value, so an
implementation in a format with 64 integer bits agrees with this model only while every value it
computes stays below `2^63` in magnitude, and nothing in this model checks that.

`Arith64.nearest` rounds to nearest at every operation, so `Arith64` is inhabited.
-/

public section

open Complex

namespace Falcon.FixedPoint

/-- Fixed-point arithmetic with 64 fractional bits: the reading of a real onto the grid within
`2⁻⁶⁵`, the complex product within `√2 · 2⁻⁶⁴`, and a twiddle table within `0.7072 · 2⁻⁶⁴` of
`FFTStages.twiddle`. -/
structure Arith64 where
  /-- The reading of a real onto the grid `2⁻⁶⁴ · ℤ`. -/
  rnd : ℝ → ℝ
  rnd_err : ∀ x, |rnd x - x| ≤ 1 / 2 ^ 65
  /-- The complex product of two registers. -/
  mul : ℂ → ℂ → ℂ
  mul_err : ∀ z w, ‖mul z w - z * w‖ ≤ √2 / 2 ^ 64
  /-- The twiddle of block `c` at stage `s`. -/
  tw : ℕ → ℕ → ℂ
  tw_err : ∀ s c, ‖tw s c - FFTStages.twiddle s c‖ ≤ 7072 / 10000 / 2 ^ 64

/-- `√2 ≤ 1.4143`. -/
theorem sqrt_two_le : √2 ≤ 14143 / 10000 := by
  calc √2 ≤ √((14143 / 10000) ^ 2) := Real.sqrt_le_sqrt (by norm_num)
    _ = 14143 / 10000 := Real.sqrt_sq (by norm_num)

namespace Arith64

/-- Round to nearest on the grid `2⁻⁶⁴ · ℤ`. -/
@[expose] noncomputable def roundGrid (x : ℝ) : ℝ := (round (x * 2 ^ 64) : ℝ) / 2 ^ 64

/-- Round to nearest on the grid is within `2⁻⁶⁵`. -/
theorem abs_roundGrid_sub_le (x : ℝ) : |roundGrid x - x| ≤ 1 / 2 ^ 65 := by
  have hp : (0 : ℝ) < 2 ^ 64 := by positivity
  have h := abs_sub_round (x * 2 ^ 64)
  have e : roundGrid x - x = ((round (x * 2 ^ 64) : ℝ) - x * 2 ^ 64) / 2 ^ 64 := by
    unfold roundGrid
    rw [sub_div, mul_div_assoc, div_self hp.ne', mul_one]
  rw [e, abs_div, abs_of_pos hp, abs_sub_comm, div_le_iff₀ hp]
  calc _ ≤ 1 / 2 := h
    _ = 1 / 2 ^ 65 * 2 ^ 64 := by norm_num

/-- A complex number rounded to the grid, part by part. -/
@[expose] noncomputable def roundGridC (z : ℂ) : ℂ := ⟨roundGrid z.re, roundGrid z.im⟩

/-- A complex number rounded to the grid part by part is within `√2 · 2⁻⁶⁵`. -/
theorem norm_roundGridC_sub_le (z : ℂ) : ‖roundGridC z - z‖ ≤ √2 / 2 ^ 65 := by
  have h1 := abs_roundGrid_sub_le z.re
  have h2 := abs_roundGrid_sub_le z.im
  calc ‖roundGridC z - z‖ ≤ √2 * max |(roundGridC z - z).re| |(roundGridC z - z).im| :=
        Complex.norm_le_sqrt_two_mul_max _
    _ ≤ √2 * (1 / 2 ^ 65) := by
        refine mul_le_mul_of_nonneg_left (max_le ?_ ?_) (Real.sqrt_nonneg _)
        · simpa [roundGridC] using h1
        · simpa [roundGridC] using h2
    _ = √2 / 2 ^ 65 := by ring

/-- The complex product from four real products, each rounded to nearest on the grid. -/
@[expose] noncomputable def mulNearest (z w : ℂ) : ℂ :=
  ⟨roundGrid (z.re * w.re) - roundGrid (z.im * w.im),
    roundGrid (z.re * w.im) + roundGrid (z.im * w.re)⟩

/-- The product from four rounded real products is within `√2 · 2⁻⁶⁴`. -/
theorem norm_mulNearest_sub_le (z w : ℂ) : ‖mulNearest z w - z * w‖ ≤ √2 / 2 ^ 64 := by
  have h1 := abs_roundGrid_sub_le (z.re * w.re)
  have h2 := abs_roundGrid_sub_le (z.im * w.im)
  have h3 := abs_roundGrid_sub_le (z.re * w.im)
  have h4 := abs_roundGrid_sub_le (z.im * w.re)
  have hre : |(mulNearest z w - z * w).re| ≤ 1 / 2 ^ 64 := by
    have e : (mulNearest z w - z * w).re =
        (roundGrid (z.re * w.re) - z.re * w.re) - (roundGrid (z.im * w.im) - z.im * w.im) := by
      simp [mulNearest]; ring
    rw [e]
    calc _ ≤ |roundGrid (z.re * w.re) - z.re * w.re| + |roundGrid (z.im * w.im) - z.im * w.im| :=
          abs_sub _ _
      _ ≤ 1 / 2 ^ 65 + 1 / 2 ^ 65 := add_le_add h1 h2
      _ = 1 / 2 ^ 64 := by norm_num
  have him : |(mulNearest z w - z * w).im| ≤ 1 / 2 ^ 64 := by
    have e : (mulNearest z w - z * w).im =
        (roundGrid (z.re * w.im) - z.re * w.im) + (roundGrid (z.im * w.re) - z.im * w.re) := by
      simp [mulNearest]; ring
    rw [e]
    calc _ ≤ |roundGrid (z.re * w.im) - z.re * w.im| + |roundGrid (z.im * w.re) - z.im * w.re| :=
          abs_add_le _ _
      _ ≤ 1 / 2 ^ 65 + 1 / 2 ^ 65 := add_le_add h3 h4
      _ = 1 / 2 ^ 64 := by norm_num
  calc _ ≤ √2 * max |(mulNearest z w - z * w).re| |(mulNearest z w - z * w).im| :=
        Complex.norm_le_sqrt_two_mul_max _
    _ ≤ √2 * (1 / 2 ^ 64) := mul_le_mul_of_nonneg_left (max_le hre him) (Real.sqrt_nonneg _)
    _ = √2 / 2 ^ 64 := by ring

/-- The twiddle table rounded to nearest is within `0.7072 · 2⁻⁶⁴`. -/
theorem norm_roundGridC_twiddle_sub_le (s c : ℕ) :
    ‖roundGridC (FFTStages.twiddle s c) - FFTStages.twiddle s c‖ ≤ 7072 / 10000 / 2 ^ 64 := by
  refine (norm_roundGridC_sub_le _).trans ?_
  have := sqrt_two_le
  calc √2 / 2 ^ 65 ≤ 14143 / 10000 / 2 ^ 65 := by gcongr
    _ ≤ 7072 / 10000 / 2 ^ 64 := by norm_num

/-- Round to nearest at every operation. -/
noncomputable def nearest : Arith64 where
  rnd := roundGrid
  rnd_err := abs_roundGrid_sub_le
  mul := mulNearest
  mul_err := norm_mulNearest_sub_le
  tw s c := roundGridC (FFTStages.twiddle s c)
  tw_err := norm_roundGridC_twiddle_sub_le

end Arith64

end Falcon.FixedPoint

end
