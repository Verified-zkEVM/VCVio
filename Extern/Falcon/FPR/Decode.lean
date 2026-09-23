/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

import all LatticeCrypto.Falcon.Concrete.FPR
public import LatticeCrypto.Falcon.Concrete.FPR
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# FPR decoding and denotation

The bit-level decoding `FPR.decode` of a binary64 word into sign, exponent and mantissa fields,
its denotation `toReal` into `ℝ`, and the structural facts every arithmetic proof starts from:
negation, field bounds, the uniform significand reconstruction, the operand and result domains
(`FPR.IsNormal`, `FPR.IsNormalOrZero`, `FPR.InNormalMagnitudeRange`), and the magnitude key
that `FPR.add`'s compare-and-swap step reads.

This is the root of the FPR bridge: nothing here mentions an arithmetic kernel.

It also carries the generic word-arithmetic facts (non-wrapping `UInt32` / `UInt64` add and
subtract, exponent-field extraction, fixed shifts) that the operation proofs and the fixed-point
`expm_p63` proof in `Extern/Falcon/Expm/` share, so that neither has to reach into the other.
-/

public section

namespace Falcon.Concrete.FPRBridge

open Falcon.Concrete.FPR

noncomputable section

/-! ## Interpretation: FPR → ℝ -/

/-! ### Layer 1: bit-level decomposition (pure `Nat`/`Bool`, no `ℝ`) -/

/-- The three IEEE-754 binary64 bit fields of an `FPR` word: sign bit, 11-bit biased
exponent, and 52-bit mantissa (implicit leading `1` for normal values), matching the
layout documented in `FPR.lean`'s module docstring (bit 63 / bits 62-52 / bits 51-0).

This is an **unchecked** triple: the field widths describe the intended layout but are not
enforced by the types, so out-of-range triples such as `⟨false, 2048, 0⟩` inhabit it and even
satisfy `FPR.Bits.IsNormal`. Nothing produced by `FPR.decode` is out of range —
`FPR.decode_wellFormed` — so the predicates and denotations below are only ever applied to
in-range triples in this development. A theorem stated on a raw `FPR.Bits` rather than on
`FPR.decode x` should say which bounds it needs; see `FPR.Bits.abs_toReal_sub_of_succ_mantissa`
for one that does not carry them. -/
structure FPR.Bits where
  /-- The sign bit: `true` means negative. -/
  sign : Bool
  /-- The 11-bit biased exponent (bias `1023`). -/
  exponent : Nat
  /-- The 52-bit mantissa (implicit leading `1` for normal values). -/
  mantissa : Nat
deriving DecidableEq, Repr

/-- Split an `FPR` bit pattern into its sign, exponent, and mantissa fields. -/
def FPR.decode (x : FPR) : FPR.Bits where
  sign := x.toNat.testBit 63
  exponent := (x.toNat >>> 52) % 2 ^ 11
  mantissa := x.toNat % 2 ^ 52

/-! ### Layer 2: interpretation into `ℝ` -/

/-- Interpret decoded IEEE-754 fields as a real number. Non-finite patterns (biased
exponent all-ones, i.e. Inf/NaN) denote `0`, matching the existing `toRat0`-based
convention. Subnormals (exponent = 0) have no implicit leading bit; normals do. -/
noncomputable def FPR.Bits.toReal (b : FPR.Bits) : ℝ :=
  if b.exponent = 0 then
    (if b.sign then -1 else 1) * (b.mantissa : ℝ) * (2 : ℝ) ^ (-(1074 : ℤ))
  else if b.exponent = 2047 then
    0
  else
    (if b.sign then -1 else 1) * (1 + (b.mantissa : ℝ) / 2 ^ 52) *
      (2 : ℝ) ^ ((b.exponent : ℤ) - 1023)

/-- An `FPR` bit pattern interpreted as a real number, by splitting it into its IEEE-754
binary64 fields with `FPR.decode` and denoting those fields with `FPR.Bits.toReal`. The
whole chain is elementary arithmetic on `Nat`, `Bool` and `ℝ`, so it reduces in the
kernel. -/
noncomputable def toRealBits (x : FPR) : ℝ := (FPR.decode x).toReal

/-- Interpret an `FPR` word as the corresponding IEEE-754 value in `ℝ`,
mapping non-finite bit patterns to `0`. -/
def toReal (x : FPR) : ℝ := toRealBits x

/-! ## Structural theorems: zero, one, negation -/

private theorem neg_toNat (x : FPR) : (FPR.neg x).toNat = x.toNat ^^^ 2 ^ 63 := by
  simp [FPR.neg, UInt64.toNat_xor]

private theorem decode_neg_sign (x : FPR) :
    (FPR.decode (FPR.neg x)).sign = !(FPR.decode x).sign := by
  unfold FPR.decode; simp only; rw [neg_toNat, Nat.testBit_xor, Nat.testBit_two_pow]; simp

private theorem decode_neg_exponent (x : FPR) :
    (FPR.decode (FPR.neg x)).exponent = (FPR.decode x).exponent := by
  unfold FPR.decode
  simp only
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_mod_two_pow, Nat.testBit_mod_two_pow]
  by_cases hi : i < 11
  · simp only [hi, decide_true, Bool.true_and, Nat.testBit_shiftRight]
    rw [neg_toNat, Nat.testBit_xor, Nat.testBit_two_pow_of_ne (by omega : (63 : Nat) ≠ 52 + i)]
    simp
  · simp [hi]

private theorem decode_neg_mantissa (x : FPR) :
    (FPR.decode (FPR.neg x)).mantissa = (FPR.decode x).mantissa := by
  unfold FPR.decode
  simp only
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_mod_two_pow, Nat.testBit_mod_two_pow]
  by_cases hi : i < 52
  · simp only [hi, decide_true, Bool.true_and]
    rw [neg_toNat, Nat.testBit_xor, Nat.testBit_two_pow_of_ne (by omega : (63 : Nat) ≠ i)]
    simp
  · simp [hi]

private theorem decode_zero : FPR.decode FPR.zero = ⟨false, 0, 0⟩ := by
  unfold FPR.decode FPR.zero; decide

private theorem decode_one : FPR.decode FPR.one = ⟨false, 1023, 0⟩ := by
  unfold FPR.decode FPR.one; decide

/-- `toReal` of the `FPR` zero bit pattern is `0`. -/
theorem toReal_zero : toReal FPR.zero = 0 := by
  unfold toReal toRealBits
  rw [decode_zero]
  unfold FPR.Bits.toReal
  norm_num

/-- `toReal` of the `FPR` one bit pattern is `1`. -/
theorem toReal_one : toReal FPR.one = 1 := by
  unfold toReal toRealBits
  rw [decode_one]
  simp [FPR.Bits.toReal]

-- Binary64's own exponent range reaches `2 ^ (-1074)` at the subnormal scale, well past
-- the default evaluation threshold of `256`. Raised here so the numeric tactics evaluate
-- the format's constants instead of declining to; it is not a suppressed diagnostic.

set_option exponentiation.threshold 1100 in
/-- Negating an `FPR` value (flipping its sign bit) negates its real interpretation. -/
theorem toReal_neg (a : FPR) : toReal (FPR.neg a) = -toReal a := by
  unfold toReal toRealBits FPR.Bits.toReal
  rw [decode_neg_exponent, decode_neg_mantissa, decode_neg_sign]
  cases (FPR.decode a).sign <;> simp <;> split_ifs <;> ring

/-! ## Structural facts: field bounds, uniform reconstruction, representability, and ulp

Reusable structural infrastructure over `FPR.decode` / `toRealBits`, needed by (but proven
independently of) the per-operation rounding bounds. None of this depends on the internals
of `FPR.add` / `FPR.mul` / `FPR.div` / `FPR.sqrt`; it is pure algebra on the IEEE-754 field
decomposition itself. -/

/-- The biased exponent field extracted by `FPR.decode` is always below `2^11`: it is
literally reduced modulo `2^11` in the definition of `FPR.decode`. -/
theorem FPR.decode_exponent_lt (x : FPR) : (FPR.decode x).exponent < 2 ^ 11 := by
  unfold FPR.decode
  exact Nat.mod_lt _ (by norm_num)

/-- A field triple whose exponent and mantissa fit the widths the layout documents. -/
def FPR.Bits.WellFormed (b : FPR.Bits) : Prop := b.exponent < 2 ^ 11 ∧ b.mantissa < 2 ^ 52

/-- The mantissa field extracted by `FPR.decode` is always below `2^52`: it is literally
reduced modulo `2^52` in the definition of `FPR.decode`. -/
theorem FPR.decode_mantissa_lt (x : FPR) : (FPR.decode x).mantissa < 2 ^ 52 := by
  unfold FPR.decode
  exact Nat.mod_lt _ (by norm_num)

/-- Everything `FPR.decode` produces respects the documented field widths. -/
theorem FPR.decode_wellFormed (x : FPR) : (FPR.decode x).WellFormed :=
  ⟨FPR.decode_exponent_lt x, FPR.decode_mantissa_lt x⟩

/-- The integer significand of a decoded field triple: the mantissa with the implicit
leading bit folded in when the exponent field is nonzero (normal), or bare when it is zero
(subnormal or zero). Together with `FPR.Bits.workExp`, this gives every finite `FPR.Bits`
value a single uniform `significand * 2^(workExp - 1023 - 52)` shape, erasing the
subnormal/normal case split that `FPR.Bits.toReal` itself makes; see
`FPR.Bits.toReal_eq_of_exponent_ne_2047`. -/
def FPR.Bits.significand (b : FPR.Bits) : ℕ :=
  b.mantissa + (if b.exponent = 0 then 0 else 2 ^ 52)

/-- The working exponent of a decoded field triple: the biased exponent field itself when
normal, or `1` when the exponent field is `0` (subnormal/zero), matching the convention
that subnormals scale by `2^(1 - 1023 - 52) = 2^(-1074)`. Paired with
`FPR.Bits.significand` in `FPR.Bits.toReal_eq_of_exponent_ne_2047`. -/
def FPR.Bits.workExp (b : FPR.Bits) : ℕ := max b.exponent 1

/-- Every finite (non-Inf/NaN) decoded field triple denotes `± significand * 2^(workExp -
1023 - 52)`, a single algebraic form unifying the subnormal and normal branches of
`FPR.Bits.toReal`. This is the form the ulp/spacing facts below are built from. -/
theorem FPR.Bits.toReal_eq_of_exponent_ne_2047 (b : FPR.Bits) (h : b.exponent ≠ 2047) :
    b.toReal = (if b.sign then -1 else 1) * (b.significand : ℝ) *
      (2 : ℝ) ^ ((b.workExp : ℤ) - 1023 - 52) := by
  unfold FPR.Bits.toReal FPR.Bits.significand FPR.Bits.workExp
  by_cases he : b.exponent = 0
  · simp only [he]
    norm_num
  · rw [ite_eq_right he, ite_eq_right h, ite_eq_right he, max_eq_left (by omega : 1 ≤ b.exponent)]
    have key : (2 : ℝ) ^ ((b.exponent : ℤ) - 1023 - 52) =
        (2 : ℝ) ^ ((b.exponent : ℤ) - 1023) / 2 ^ (52 : ℕ) := by
      rw [show (b.exponent : ℤ) - 1023 - 52 = ((b.exponent : ℤ) - 1023) - (52 : ℤ) by ring,
        zpow_sub₀ (by norm_num : (2 : ℝ) ≠ 0)]
      norm_num
    rw [key]
    push_cast
    field_simp
    ring

/-- The magnitude of a decoded field triple's real value, stripped of the sign factor:
`|b.toReal|` reduces to the same case split as `FPR.Bits.toReal` itself, minus the `±1`. -/
theorem FPR.Bits.abs_toReal_eq (b : FPR.Bits) :
    |b.toReal| = if b.exponent = 0 then (b.mantissa : ℝ) * (2 : ℝ) ^ (-(1074 : ℤ))
      else if b.exponent = 2047 then 0
      else (1 + (b.mantissa : ℝ) / 2 ^ 52) * (2 : ℝ) ^ ((b.exponent : ℤ) - 1023) := by
  have hsign1 : |(if b.sign then (-1 : ℝ) else 1)| = 1 := by cases b.sign <;> simp
  unfold FPR.Bits.toReal
  by_cases h1 : b.exponent = 0
  · rw [ite_eq_left h1, ite_eq_left h1, abs_mul, abs_mul, hsign1,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ (b.mantissa : ℝ)),
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ (-(1074 : ℤ)))]
    ring
  · rw [ite_eq_right h1, ite_eq_right h1]
    by_cases h2 : b.exponent = 2047
    · rw [ite_eq_left h2, ite_eq_left h2, abs_zero]
    · rw [ite_eq_right h2, ite_eq_right h2, abs_mul, abs_mul, hsign1,
        abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 + (b.mantissa : ℝ) / 2 ^ 52),
        abs_of_nonneg (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ ((b.exponent : ℤ) - 1023))]
      ring

/-- A real number is exactly representable as a finite (non-Inf/NaN) IEEE-754 binary64
value when it arises as `FPR.Bits.toReal` of some field triple with a valid (in-range)
exponent and mantissa. -/
def IsFPRRepresentable (r : ℝ) : Prop :=
  ∃ b : FPR.Bits, b.exponent < 2047 ∧ b.mantissa < 2 ^ 52 ∧ r = b.toReal

/-- Non-finite bit patterns (biased exponent field `2047`, i.e. Inf/NaN) decode to `0`
under `toRealBits`, matching the "non-finite denotes `0`" convention documented at
`FPR.Bits.toReal`. -/
theorem toRealBits_eq_zero_of_exponent_eq_2047 (x : FPR)
    (h : (FPR.decode x).exponent = 2047) : toRealBits x = 0 := by
  unfold toRealBits FPR.Bits.toReal
  simp [h]

/-- Every `FPR` bit pattern denotes an exactly representable real: the finite ones via
their own decoded field triple, and the non-finite ones via the all-zero triple, since
`toRealBits` maps them both to `0`. -/
theorem toRealBits_isFPRRepresentable (x : FPR) : IsFPRRepresentable (toRealBits x) := by
  have hexp := FPR.decode_exponent_lt x
  by_cases h : (FPR.decode x).exponent = 2047
  · refine ⟨⟨false, 0, 0⟩, by norm_num, by norm_num, ?_⟩
    rw [toRealBits_eq_zero_of_exponent_eq_2047 x h]
    simp [FPR.Bits.toReal]
  · exact ⟨FPR.decode x, by omega, FPR.decode_mantissa_lt x, rfl⟩

/-- The spacing ("unit in the last place") between adjacent representable binary64 values
sharing biased exponent field `e`: `2^(-1074)` at the subnormal/zero exponent (`e = 0`,
via the working-exponent convention `FPR.Bits.workExp` maps it to `1`), and
`2^(e - 1023 - 52)` for normal `e`. -/
def FPR.ulpOfExponent (e : ℕ) : ℝ := (2 : ℝ) ^ ((max e 1 : ℤ) - 1023 - 52)

/-- The key ulp/magnitude relation for normal (nonzero, finite) exponent fields: the
spacing to the next representable value is at most `2^(-52)` of the value's own
magnitude. This is the fact that ultimately controls the relative rounding error of any
correctly-rounded binary64 operation, since a correctly-rounded result is within half a
ulp of the exact value. -/
theorem FPR.ulpOfExponent_le_two_pow_neg52_mul_abs (b : FPR.Bits)
    (he0 : b.exponent ≠ 0) (he : b.exponent ≠ 2047) :
    FPR.ulpOfExponent b.exponent ≤ (2 : ℝ) ^ (-(52 : ℤ)) * |b.toReal| := by
  rw [FPR.Bits.abs_toReal_eq, ite_eq_right he0, ite_eq_right he]
  unfold FPR.ulpOfExponent
  rw [max_eq_left (show (1 : ℤ) ≤ (b.exponent : ℤ) by omega)]
  have hcomb : (2 : ℝ) ^ (-(52 : ℤ)) * (2 : ℝ) ^ ((b.exponent : ℤ) - 1023) =
      (2 : ℝ) ^ ((b.exponent : ℤ) - 1023 - 52) := by
    rw [← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
    ring_nf
  rw [show (2 : ℝ) ^ (-(52 : ℤ)) *
        ((1 + (b.mantissa : ℝ) / 2 ^ 52) * (2 : ℝ) ^ ((b.exponent : ℤ) - 1023)) =
      (1 + (b.mantissa : ℝ) / 2 ^ 52) *
        ((2 : ℝ) ^ (-(52 : ℤ)) * (2 : ℝ) ^ ((b.exponent : ℤ) - 1023)) by ring,
    hcomb]
  have h1le : (1 : ℝ) ≤ 1 + (b.mantissa : ℝ) / 2 ^ 52 := le_add_of_nonneg_right (by positivity)
  nlinarith [zpow_pos (by norm_num : (0 : ℝ) < 2) ((b.exponent : ℤ) - 1023 - 52)]

/-- The gap between two decoded values that agree on sign and exponent and whose mantissas
differ by exactly `1` is exactly `FPR.ulpOfExponent` at that exponent — the ulp/spacing
fact stated directly as a distance between adjacent representable values, rather than as
a bound relative to one endpoint's magnitude (`FPR.ulpOfExponent_le_two_pow_neg52_mul_abs`).
Holds uniformly across the subnormal/normal boundary via the significand/workExp
reconstruction, `FPR.Bits.toReal_eq_of_exponent_ne_2047`.

Stated on a raw triple, so it does **not** bound `b.mantissa`: at `b.mantissa = 2 ^ 52 - 1` the
successor leaves the 52-bit field, and the statement then describes a triple that no `FPR` word
decodes to. Applied to `FPR.decode x` the bound comes from `FPR.decode_mantissa_lt`, and the
carry case is the business of the packing lemmas rather than this one. -/
theorem FPR.Bits.abs_toReal_sub_of_succ_mantissa (b : FPR.Bits) (he : b.exponent ≠ 2047) :
    |({ b with mantissa := b.mantissa + 1 } : FPR.Bits).toReal - b.toReal| =
      FPR.ulpOfExponent b.exponent := by
  have he' : ({ b with mantissa := b.mantissa + 1 } : FPR.Bits).exponent ≠ 2047 := he
  rw [FPR.Bits.toReal_eq_of_exponent_ne_2047 _ he', FPR.Bits.toReal_eq_of_exponent_ne_2047 b he]
  have hsig : ({ b with mantissa := b.mantissa + 1 } : FPR.Bits).significand =
      b.significand + 1 := by
    unfold FPR.Bits.significand
    dsimp only
    split_ifs <;> omega
  have hwork : ({ b with mantissa := b.mantissa + 1 } : FPR.Bits).workExp = b.workExp := rfl
  have hsign : ({ b with mantissa := b.mantissa + 1 } : FPR.Bits).sign = b.sign := rfl
  rw [hsig, hwork, hsign]
  unfold FPR.ulpOfExponent FPR.Bits.workExp
  have hsign1 : |(if b.sign then (-1 : ℝ) else 1)| = 1 := by cases b.sign <;> simp
  push_cast
  rw [show (if b.sign then (-1 : ℝ) else 1) * ((b.significand : ℝ) + 1) *
        (2 : ℝ) ^ ((max b.exponent 1 : ℤ) - 1023 - 52) -
      (if b.sign then (-1 : ℝ) else 1) * (b.significand : ℝ) *
        (2 : ℝ) ^ ((max b.exponent 1 : ℤ) - 1023 - 52) =
      (if b.sign then (-1 : ℝ) else 1) * (2 : ℝ) ^ ((max b.exponent 1 : ℤ) - 1023 - 52) by ring,
    abs_mul, hsign1, one_mul, abs_of_nonneg (by positivity)]

/-! ## Domain restriction: normal, in-range operands and results -/

/-- A decoded field triple denotes a normal (non-subnormal), finite (non-Inf/NaN) value:
its biased exponent field avoids both the subnormal/zero marker `0` and the non-finite
marker `2047`. -/
def FPR.Bits.IsNormal (b : FPR.Bits) : Prop := b.exponent ≠ 0 ∧ b.exponent ≠ 2047

/-- An `FPR` bit pattern decodes to a normal, finite IEEE-754 binary64 value. -/
def FPR.IsNormal (x : FPR) : Prop := (FPR.decode x).IsNormal

/-- A decoded field triple denotes exactly `±0`: the zero/subnormal exponent marker with an
empty significand. Distinct from `toReal b = 0`, which also holds on the non-finite encodings,
since `FPR.Bits.toReal` sends those to `0` as well. -/
def FPR.Bits.IsZero (b : FPR.Bits) : Prop := b.exponent = 0 ∧ b.mantissa = 0

/-- An `FPR` bit pattern is one of the two zero encodings. -/
def FPR.IsZero (x : FPR) : Prop := (FPR.decode x).IsZero

/-- The operand domain binary64 arithmetic is actually closed under: normal and finite, or
exactly `±0`.

`FPR.IsNormal` alone is not closed, because exact cancellation leaves the normal range: at
`1 + (-1)` both operands are normal, the exact sum `0` satisfies `FPR.InNormalMagnitudeRange`
through its `r = 0` disjunct, and `FPR.add` returns `+0`, whose exponent field is `0`. Admitting
the zero encodings repairs that without admitting subnormals (exponent `0` with a nonzero
significand) or the non-finite encodings (exponent `2047`), both of which would break the
relative-error bounds. -/
def FPR.IsNormalOrZero (x : FPR) : Prop := FPR.IsNormal x ∨ FPR.IsZero x

/-- The smallest positive magnitude of a normal binary64 value, `2^(-1022)`. -/
def FPR.minNormalReal : ℝ := (2 : ℝ) ^ (-(1022 : ℤ))

/-- The largest finite representable binary64 magnitude, `(2 - 2^(-52)) * 2^1023`. -/
def FPR.maxFiniteReal : ℝ := (2 - (2 : ℝ) ^ (-(52 : ℤ))) * (2 : ℝ) ^ (1023 : ℤ)

/-- `r` is either exactly `0`, or has magnitude bracketed in `[FPR.minNormalReal,
FPR.maxFiniteReal]`: the magnitude window a correctly-rounded binary64 operation can land in
with the standard `2^(-52)` relative-error guarantee, excluding both overflow (magnitude above
`maxFiniteReal`) and underflow into the subnormal range (nonzero magnitude strictly below
`minNormalReal`). This is a pure magnitude bracket: it carries no claim that `r` itself is
exactly representable in binary64 (`IsFPRRepresentable`), only that *if* `r` is the exact
mathematical result of an operation, no correctly-rounded binary64 encoding of it can overflow
or underflow. -/
def FPR.InNormalMagnitudeRange (r : ℝ) : Prop :=
  r = 0 ∨ (FPR.minNormalReal ≤ |r| ∧ |r| ≤ FPR.maxFiniteReal)

/-! ## Bit-pattern magnitude compare (toward `FPR.add`'s compare-and-swap step)

`FPR.add` opens by comparing its two operands' magnitudes as unsigned 63-bit integers
(`za := (x &&& M63) - (y &&& M63)`) and conditionally swapping, via the tie-broken comparator
`za' := za ||| ((za - 1) &&& x)`, so the larger-magnitude operand leads (with ties broken by `x`'s
own sign bit). The lemmas below give the ingredients of that step's correctness:
`FPR.Bits.abs_toReal_lt_iff_magKey_lt` shows the packed exponent/mantissa integer orders
identically to real magnitude, `toNat_and_low63Mask_eq_magKey` shows the concrete `x &&& M63`
computation produces exactly that packed integer, and `za'_shiftRight_63_eq_one_iff` decides the
swap test `za' >>> 63` — tie-break included — in terms of the two packed integers and `x`'s sign
bit. `addPipeline` below carries the swap and every later stage — alignment/sticky-bit shift,
sign combination, leading-zero renormalization, final round-to-nearest — through to `add_error`
and `add_isNormalOrZero`, and these three are the magnitude-comparison layer it rests on. -/

/-- The unsigned integer packing of a decoded field triple's exponent and mantissa fields into
a single natural number, `exponent * 2^52 + mantissa`. Orders identically to real magnitude via
`FPR.Bits.abs_toReal_lt_iff_magKey_lt`, and is exactly what masking an `FPR` word's sign bit off
computes via `toNat_and_low63Mask_eq_magKey`. -/
private def FPR.Bits.magKey (b : FPR.Bits) : ℕ := b.exponent * 2 ^ 52 + b.mantissa

/-- Two finite (non-Inf/NaN) decoded field triples are ordered by real magnitude exactly as
their `FPR.Bits.magKey` values are ordered: a strictly larger exponent always dominates any
mantissa difference (the significand fraction is always below `2`), and for equal exponents the
comparison reduces to the mantissa alone. Holds uniformly across the subnormal/normal boundary
(no `FPR.Bits.IsNormal` hypothesis is needed). -/
private theorem FPR.Bits.abs_toReal_lt_iff_magKey_lt (b1 b2 : FPR.Bits)
    (hm1 : b1.mantissa < 2 ^ 52) (hm2 : b2.mantissa < 2 ^ 52)
    (h1 : b1.exponent ≠ 2047) (h2 : b2.exponent ≠ 2047) :
    |b1.toReal| < |b2.toReal| ↔ b1.magKey < b2.magKey := by
  unfold FPR.Bits.magKey
  rw [FPR.Bits.abs_toReal_eq, FPR.Bits.abs_toReal_eq]
  rw [ite_eq_right h1, ite_eq_right h2]
  split_ifs with he1 he2 he2
  · have hpos : (0 : ℝ) < (2 : ℝ) ^ (-(1074 : ℤ)) := by positivity
    rw [he1, he2]
    simp only [Nat.zero_mul, Nat.zero_add]
    rw [mul_lt_mul_iff_of_pos_right hpos]
    exact_mod_cast Iff.rfl
  · have he2' : 1 ≤ b2.exponent := by omega
    refine iff_of_true ?_ (by omega)
    have hm1' : (b1.mantissa : ℝ) < 2 ^ 52 := by exact_mod_cast hm1
    have hstep1 : (b1.mantissa : ℝ) * (2 : ℝ) ^ (-(1074 : ℤ)) <
        (2 : ℝ) ^ (52 : ℕ) * (2 : ℝ) ^ (-(1074 : ℤ)) := by
      apply mul_lt_mul_of_pos_right hm1' (by positivity)
    have hcomb : (2 : ℝ) ^ (52 : ℕ) * (2 : ℝ) ^ (-(1074 : ℤ)) = (2 : ℝ) ^ (-(1022 : ℤ)) := by
      rw [← zpow_natCast (2 : ℝ) 52, ← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
      norm_num
    have hstep2 : (2 : ℝ) ^ (-(1022 : ℤ)) ≤ (2 : ℝ) ^ ((b2.exponent : ℤ) - 1023) := by
      apply zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2)
      omega
    have hstep3 : (2 : ℝ) ^ ((b2.exponent : ℤ) - 1023) ≤
        (1 + (b2.mantissa : ℝ) / 2 ^ 52) * (2 : ℝ) ^ ((b2.exponent : ℤ) - 1023) := by
      apply le_mul_of_one_le_left (by positivity)
      have : (0 : ℝ) ≤ (b2.mantissa : ℝ) / 2 ^ 52 := by positivity
      linarith
    rw [hcomb] at hstep1
    linarith
  · have he1' : 1 ≤ b1.exponent := by omega
    refine iff_of_false ?_ (by omega)
    have hm2' : (b2.mantissa : ℝ) < 2 ^ 52 := by exact_mod_cast hm2
    have hstep1 : (b2.mantissa : ℝ) * (2 : ℝ) ^ (-(1074 : ℤ)) <
        (2 : ℝ) ^ (52 : ℕ) * (2 : ℝ) ^ (-(1074 : ℤ)) := by
      apply mul_lt_mul_of_pos_right hm2' (by positivity)
    have hcomb : (2 : ℝ) ^ (52 : ℕ) * (2 : ℝ) ^ (-(1074 : ℤ)) = (2 : ℝ) ^ (-(1022 : ℤ)) := by
      rw [← zpow_natCast (2 : ℝ) 52, ← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
      norm_num
    have hstep2 : (2 : ℝ) ^ (-(1022 : ℤ)) ≤ (2 : ℝ) ^ ((b1.exponent : ℤ) - 1023) := by
      apply zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2)
      omega
    have hstep3 : (2 : ℝ) ^ ((b1.exponent : ℤ) - 1023) ≤
        (1 + (b1.mantissa : ℝ) / 2 ^ 52) * (2 : ℝ) ^ ((b1.exponent : ℤ) - 1023) := by
      apply le_mul_of_one_le_left (by positivity)
      have : (0 : ℝ) ≤ (b1.mantissa : ℝ) / 2 ^ 52 := by positivity
      linarith
    rw [hcomb] at hstep1
    linarith
  · have hm1' : (b1.mantissa : ℝ) < 2 ^ 52 := by exact_mod_cast hm1
    have hm2' : (b2.mantissa : ℝ) < 2 ^ 52 := by exact_mod_cast hm2
    rcases lt_trichotomy b1.exponent b2.exponent with hlt | heq | hgt
    · refine iff_of_true ?_ (by omega)
      have hstep1 : (1 + (b1.mantissa : ℝ) / 2 ^ 52) * (2 : ℝ) ^ ((b1.exponent : ℤ) - 1023) <
          2 * (2 : ℝ) ^ ((b1.exponent : ℤ) - 1023) := by
        apply mul_lt_mul_of_pos_right (by linarith) (by positivity)
      have hcomb : (2 : ℝ) * (2 : ℝ) ^ ((b1.exponent : ℤ) - 1023) =
          (2 : ℝ) ^ ((b1.exponent : ℤ) + 1 - 1023) := by
        rw [show (b1.exponent : ℤ) + 1 - 1023 = ((b1.exponent : ℤ) - 1023) + 1 by ring,
          zpow_add_one₀ (by norm_num : (2 : ℝ) ≠ 0)]
        ring
      have hstep2 : (2 : ℝ) ^ ((b1.exponent : ℤ) + 1 - 1023) ≤
          (2 : ℝ) ^ ((b2.exponent : ℤ) - 1023) := by
        apply zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2)
        omega
      have hstep3 : (2 : ℝ) ^ ((b2.exponent : ℤ) - 1023) ≤
          (1 + (b2.mantissa : ℝ) / 2 ^ 52) * (2 : ℝ) ^ ((b2.exponent : ℤ) - 1023) := by
        apply le_mul_of_one_le_left (by positivity)
        have : (0 : ℝ) ≤ (b2.mantissa : ℝ) / 2 ^ 52 := by positivity
        linarith
      rw [hcomb] at hstep1
      linarith
    · rw [heq]
      have hp : (0 : ℝ) < (2 : ℝ) ^ ((b2.exponent : ℤ) - 1023) := by positivity
      rw [mul_lt_mul_iff_of_pos_right hp]
      constructor
      · intro h
        have hnat : b1.mantissa < b2.mantissa := by
          have : (b1.mantissa : ℝ) < (b2.mantissa : ℝ) := by linarith
          exact_mod_cast this
        omega
      · intro h
        have hnat : b1.mantissa < b2.mantissa := by omega
        have : (b1.mantissa : ℝ) < (b2.mantissa : ℝ) := by exact_mod_cast hnat
        linarith
    · refine iff_of_false ?_ (by omega)
      have hstep1 : (1 + (b2.mantissa : ℝ) / 2 ^ 52) * (2 : ℝ) ^ ((b2.exponent : ℤ) - 1023) <
          2 * (2 : ℝ) ^ ((b2.exponent : ℤ) - 1023) := by
        apply mul_lt_mul_of_pos_right (by linarith) (by positivity)
      have hcomb : (2 : ℝ) * (2 : ℝ) ^ ((b2.exponent : ℤ) - 1023) =
          (2 : ℝ) ^ ((b2.exponent : ℤ) + 1 - 1023) := by
        rw [show (b2.exponent : ℤ) + 1 - 1023 = ((b2.exponent : ℤ) - 1023) + 1 by ring,
          zpow_add_one₀ (by norm_num : (2 : ℝ) ≠ 0)]
        ring
      have hstep2 : (2 : ℝ) ^ ((b2.exponent : ℤ) + 1 - 1023) ≤
          (2 : ℝ) ^ ((b1.exponent : ℤ) - 1023) := by
        apply zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2)
        omega
      have hstep3 : (2 : ℝ) ^ ((b1.exponent : ℤ) - 1023) ≤
          (1 + (b1.mantissa : ℝ) / 2 ^ 52) * (2 : ℝ) ^ ((b1.exponent : ℤ) - 1023) := by
        apply le_mul_of_one_le_left (by positivity)
        have : (0 : ℝ) ≤ (b1.mantissa : ℝ) / 2 ^ 52 := by positivity
        linarith
      rw [hcomb] at hstep1
      intro hcontra
      linarith

/-- Masking a `UInt64` with the low-63-bit all-ones pattern strips its top (sign) bit: the
result's underlying `Nat` is the original reduced modulo `2^63`. -/
private theorem toNat_and_low63Mask (x : UInt64) :
    (x &&& (((1 : UInt64) <<< 63) - 1)).toNat = x.toNat % 2 ^ 63 := by
  rw [UInt64.toNat_and]
  have h1 : (((1 : UInt64) <<< 63) - 1).toNat = 2 ^ 63 - 1 := by decide
  rw [h1]
  exact Nat.and_two_pow_sub_one_eq_mod x.toNat 63

/-- Masking an `FPR` word with the low-63-bit all-ones pattern (the sign-stripping mask `M63`
used inside `FPR.add`'s compare-and-swap step) computes exactly `FPR.Bits.magKey` of its
decoded fields. -/
private theorem toNat_and_low63Mask_eq_magKey (x : FPR) :
    (x &&& (((1 : UInt64) <<< 63) - 1)).toNat = (FPR.decode x).magKey := by
  rw [toNat_and_low63Mask]
  unfold FPR.decode FPR.Bits.magKey
  simp only [Nat.shiftRight_eq_div_pow]
  omega

/-- The classic "subtract and test the top bit" unsigned-comparison trick, valid on 63-bit
`UInt64` patterns (the sign-stripped operand shape `FPR.add`'s `za := (x &&& M63) - (y &&& M63)`
step produces): the top bit of `p - q` is set exactly when `p < q`. Proved by unfolding to the
underlying `Nat` subtraction modulo `2^64` and case-splitting on whether it wraps. -/
private theorem sub_shiftRight_63_eq_one_iff_lt (p q : UInt64)
    (hp : p < ((1 : UInt64) <<< 63)) (hq : q < ((1 : UInt64) <<< 63)) :
    (p - q) >>> 63 = 1 ↔ p < q := by
  rw [UInt64.lt_iff_toNat_lt, ← UInt64.toNat_inj]
  rw [UInt64.lt_iff_toNat_lt] at hp hq
  have h63 : ((1 : UInt64) <<< 63).toNat = 2 ^ 63 := by decide
  rw [h63] at hp hq
  rw [UInt64.toNat_shiftRight, UInt64.toNat_sub]
  have hshift : (63 : UInt64).toNat = 63 := by decide
  rw [hshift]
  have h1 : (1 : UInt64).toNat = 1 := by decide
  rw [h1, Nat.shiftRight_eq_div_pow]
  by_cases hle : q.toNat ≤ p.toNat
  · have heq : (2 ^ 64 - q.toNat + p.toNat) % 2 ^ 64 = p.toNat - q.toNat := by omega
    rw [heq]
    have hdiv : (p.toNat - q.toNat) / 2 ^ 63 = 0 := by omega
    rw [hdiv]
    omega
  · have heq : (2 ^ 64 - q.toNat + p.toNat) % 2 ^ 64 = 2 ^ 64 - q.toNat + p.toNat := by omega
    rw [heq]
    have hdiv : (2 ^ 64 - q.toNat + p.toNat) / 2 ^ 63 = 1 := by omega
    rw [hdiv]
    omega

/-- Shifting a `UInt64` right by the literal `63` denotes plain `Nat` division by `2 ^ 63`: the
shift-count truncation `63 % 64` folds away since `63` is already below the word size. -/
private theorem toNat_shiftRight_sixtyThree (w : UInt64) :
    (w >>> 63).toNat = w.toNat / 2 ^ 63 := by
  rw [UInt64.toNat_shiftRight, show (63 : UInt64).toNat % 64 = 63 from by decide,
    Nat.shiftRight_eq_div_pow]

/-- Whenever the plain subtraction `p - q` is nonzero, folding in `(p - q - 1) &&& x` leaves its
top bit unchanged: the fold can only move bit `63` on an exact tie `p - q = 0`, the case
`za'_shiftRight_63_eq_one_iff` handles separately. Consumed by that lemma, this is what lets
`sub_shiftRight_63_eq_one_iff_lt`'s plain "subtract and test the top bit" trick decide the
non-tied cases of `FPR.add`'s tie-broken comparator `za'`. -/
private theorem or_and_sub_one_shiftRight_63_eq_of_ne_zero (p q x : UInt64) (h : p ≠ q)
    (hp : p < ((1 : UInt64) <<< 63)) (hq : q < ((1 : UInt64) <<< 63)) :
    ((p - q) ||| ((p - q - 1) &&& x)) >>> 63 = (p - q) >>> 63 := by
  have h63 : ((1 : UInt64) <<< 63).toNat = 2 ^ 63 := by decide
  rw [UInt64.lt_iff_toNat_lt, h63] at hp hq
  have hne : p.toNat ≠ q.toNat := fun hc => h (UInt64.toNat_inj.mp hc)
  have hzaN : (p - q).toNat = (2 ^ 64 - q.toNat + p.toNat) % 2 ^ 64 := UInt64.toNat_sub p q
  rw [← UInt64.toNat_inj, toNat_shiftRight_sixtyThree, toNat_shiftRight_sixtyThree]
  rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
  · -- p < q: `p - q` already wraps into the upper half, and or-ing in more bits cannot clear it.
    have hle : (p - q) ≤ (p - q) ||| ((p - q - 1) &&& x) := UInt64.left_le_or
    have hle' : (p - q).toNat ≤ ((p - q) ||| ((p - q - 1) &&& x)).toNat :=
      UInt64.le_iff_toNat_le.mp hle
    have hup : ((p - q) ||| ((p - q - 1) &&& x)).toNat < 2 ^ 64 := UInt64.toNat_lt _
    omega
  · -- p > q: `p - q` stays below the half, and so does the `&&&`-bounded fold or-ed into it.
    have hsub1N : (p - q - 1).toNat = (2 ^ 64 - 1 + (p - q).toNat) % 2 ^ 64 :=
      UInt64.toNat_sub (p - q) 1
    have hzalt : (p - q).toNat < 2 ^ 63 := by omega
    have hsub1lt : (p - q - 1).toNat < 2 ^ 63 := by omega
    have hand : ((p - q - 1) &&& x).toNat ≤ (p - q - 1).toNat :=
      UInt64.le_iff_toNat_le.mp UInt64.and_le_left
    have handlt : ((p - q - 1) &&& x).toNat < 2 ^ 63 := by omega
    have hor : ((p - q) ||| ((p - q - 1) &&& x)).toNat < 2 ^ 63 :=
      Nat.or_lt_two_pow hzalt handlt
    omega

/-- All-ones (`(0 : UInt64) - 1`) is neutral for `&&&`: this is what a tied magnitude comparison
`p - q = 0` collapses `FPR.add`'s tie-broken comparator `za' := (p - q) ||| ((p - q - 1) &&& x)`
down to (`(p - q - 1)` wraps to all-ones), leaving `za' = x` and its top bit exactly `x`'s sign
bit. -/
private theorem allOnes_and (x : UInt64) : ((0 : UInt64) - 1) &&& x = x := by
  have h0 : ((0 : UInt64) - 1).toNat = 2 ^ 64 - 1 := by decide
  rw [← UInt64.toNat_inj, UInt64.toNat_and, h0, Nat.and_comm,
    Nat.and_two_pow_sub_one_eq_mod]
  exact Nat.mod_eq_of_lt x.toNat_lt_size

/-- Bit `63` of `FPR.add`'s tie-broken magnitude comparator `za' := (p - q) ||| ((p - q - 1) &&&
x)`: it is set exactly when the packed magnitude `p` is strictly below `q`, or the two are equal
and `x`'s own sign bit is set. This is the correctness of `FPR.add`'s conditional-swap test
`(x ^^^ y) &&& (0 - (za' >>> 63))`, including the tie-break the plain "subtract and test the top
bit" trick (`sub_shiftRight_63_eq_one_iff_lt`) does not cover on its own: on an exact tie
`p - q = 0`, `p - q - 1` wraps to all-ones, so `za'` collapses to `x` itself
(`allOnes_and`), and the swap keys on `x`'s sign bit. -/
private theorem za'_shiftRight_63_eq_one_iff (p q x : UInt64)
    (hp : p < ((1 : UInt64) <<< 63)) (hq : q < ((1 : UInt64) <<< 63)) :
    ((p - q) ||| ((p - q - 1) &&& x)) >>> 63 = 1 ↔ p < q ∨ (p = q ∧ x >>> 63 = 1) := by
  by_cases heq : p = q
  · subst heq
    rw [UInt64.sub_self, allOnes_and]
    simp
  · rw [or_and_sub_one_shiftRight_63_eq_of_ne_zero p q x heq hp hq,
      sub_shiftRight_63_eq_one_iff_lt p q hp hq]
    constructor
    · exact Or.inl
    · rintro (h | ⟨h, -⟩)
      · exact h
      · exact absurd h heq

/-- `0` is neutral for bitwise or. -/
theorem or_zero (v : UInt64) : v ||| 0 = v := by
  rw [← UInt64.toNat_inj, UInt64.toNat_or]
  exact Nat.or_zero _

/-- A value known to fit below `2 ^ k`, or-ed with a bit-`k` flag scaled by `2 ^ k`, is exactly
their sum: the two contributions occupy disjoint bit ranges. -/
private theorem or_two_pow_add_of_lt (a k : ℕ) (ha : a < 2 ^ k) : a ||| 2 ^ k = a + 2 ^ k := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_or, Nat.testBit_two_pow]
  rcases Nat.lt_trichotomy j k with hjk | hjk | hjk
  · rw [show decide (k = j) = false from by simp; omega, Bool.or_false]
    have hpow : (2 : ℕ) ^ k = 2 ^ j * 2 ^ (k - j) := by rw [← pow_add]; congr 1; omega
    have hdiv : (a + 2 ^ k) / 2 ^ j = a / 2 ^ j + 2 ^ (k - j) := by
      rw [hpow, Nat.add_mul_div_left a _ (Nat.two_pow_pos j)]
    have heven : (2 : ℕ) ^ (k - j) % 2 = 0 := by
      have : (2 : ℕ) ^ (k - j) = 2 * 2 ^ (k - j - 1) := by rw [← pow_succ']; congr 1; omega
      omega
    rw [Nat.testBit_eq_decide_div_mod_eq, Nat.testBit_eq_decide_div_mod_eq, hdiv,
      show (a / 2 ^ j + 2 ^ (k - j)) % 2 = a / 2 ^ j % 2 from by omega]
  · subst hjk
    rw [show decide (j = j) = true from by simp, Bool.or_true]
    have hdiv : (a + 2 ^ j) / 2 ^ j = 1 := by
      have hd0 : a / 2 ^ j = 0 := Nat.div_eq_of_lt ha
      have := Nat.add_div_right a (Nat.two_pow_pos j)
      omega
    rw [Nat.testBit_eq_decide_div_mod_eq, hdiv]
    rfl
  · rw [show decide (k = j) = false from by simp; omega, Bool.or_false]
    have hpow : (2 : ℕ) ^ (k + 1) = 2 ^ k + 2 ^ k := by rw [pow_succ]; ring
    have hle : (2 : ℕ) ^ (k + 1) ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) (by omega)
    have hja : a + 2 ^ k < 2 ^ j := by omega
    have hja0 : a < 2 ^ j := lt_of_lt_of_le ha (Nat.pow_le_pow_right (by norm_num) (by omega))
    rw [Nat.testBit_lt_two_pow hja0]
    exact (Nat.testBit_lt_two_pow hja).symm

/-- The combined sign+exponent word `(w >>> 52).toUInt32` computed from any `FPR` word `w` is
exactly `w.toNat / 2 ^ 52`, with no truncation from the `UInt64 → UInt32` narrowing (the value
never exceeds `2 ^ 12`). -/
private theorem toNat_ex_of (w : FPR) : ((w >>> 52).toUInt32).toNat = w.toNat / 2 ^ 52 := by
  rw [UInt64.toNat_toUInt32, UInt64.toNat_shiftRight,
    show (52 : UInt64).toNat % 64 = 52 from by decide, Nat.shiftRight_eq_div_pow]
  have hb : w.toNat < 2 ^ 64 := w.toNat_lt_size
  exact Nat.mod_eq_of_lt (by omega)

/-- The exponent-field extraction `((w >>> 52).toUInt32) &&& 0x7FF` recovers exactly
`FPR.decode`'s exponent field. -/
private theorem toNat_ex_field_of (w : FPR) :
    (((w >>> 52).toUInt32) &&& 0x7FF).toNat = (FPR.decode w).exponent := by
  rw [UInt32.toNat_and, toNat_ex_of, show (0x7FF : UInt32).toNat = 2 ^ 11 - 1 from by decide,
    Nat.and_two_pow_sub_one_eq_mod]
  unfold FPR.decode
  rw [Nat.shiftRight_eq_div_pow]

/-- A `UInt64` left shift by one, as a wrapping doubling. -/
private theorem toNat_shiftLeft_one (v : UInt64) :
    (v <<< (1 : UInt64)).toNat = v.toNat * 2 % 2 ^ 64 := by
  rw [UInt64.toNat_shiftLeft, show (UInt64.toNat 1 % 64) = 1 from by decide, Nat.shiftLeft_eq]

/-- Unsigned `UInt32` subtraction computes the true gap whenever the subtrahend does not
exceed the minuend: no wraparound occurs. -/
private theorem toNat_sub_of_le_uint32 {ex ey : UInt32} (h : ey.toNat ≤ ex.toNat) :
    (ex - ey).toNat = ex.toNat - ey.toNat := by
  rw [UInt32.toNat_sub]
  have hex : ex.toNat < 2 ^ 32 := ex.toNat_lt_size
  have hey : ey.toNat < 2 ^ 32 := ey.toNat_lt_size
  omega

/-- The no-underflow condition for `FPR.add`'s subtraction step: whenever the smaller-magnitude
aligned significand `yu` does not exceed `xu`, the wrapping `UInt64` subtraction `xu - yu`
computes the true (non-wrapping) natural-number difference. -/
private theorem toNat_sub_of_le_uint64 (xu yu : UInt64) (h : yu.toNat ≤ xu.toNat) :
    (xu - yu).toNat = xu.toNat - yu.toNat :=
  UInt64.toNat_sub_of_le xu yu (UInt64.le_iff_toNat_le.mpr h)

private theorem toReal_eq_significand_mul_two_zpow {bx : FPR.Bits} (h0 : bx.exponent ≠ 0)
    (h2047 : bx.exponent ≠ 2047) :
    bx.toReal = (if bx.sign then (-1 : ℝ) else 1) * (bx.significand : ℝ) *
      (2 : ℝ) ^ ((bx.exponent : ℤ) - 1075) := by
  unfold FPR.Bits.toReal
  rw [ite_eq_right h0, ite_eq_right h2047]
  unfold FPR.Bits.significand
  rw [ite_eq_right h0]
  push_cast
  rw [show ((bx.exponent : ℤ) - 1075) = ((bx.exponent : ℤ) - 1023) + (-52 : ℤ) by ring,
    zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
  ring

private theorem toNat_add_of_lt_uint64 {a b : UInt64} (h : a.toNat + b.toNat < 2 ^ 64) :
    (a + b).toNat = a.toNat + b.toNat := by
  rw [UInt64.toNat_add, Nat.mod_eq_of_lt h]

end

end Falcon.Concrete.FPRBridge
