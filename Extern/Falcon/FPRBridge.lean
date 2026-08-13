/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
import all Extern.Falcon.Instance
import all LatticeCrypto.Falcon.Concrete.FPR
public import LatticeCrypto.Falcon.Scheme
public import LatticeCrypto.Falcon.Concrete.FPR
public import Extern.Falcon.Instance
public import LatticeCrypto.Falcon.Concrete.Encoding
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# FPR ↔ ℝ Bridge Theorems

Error bounds connecting the integer-only FPR emulation layer to the
exact `ℝ` arithmetic used in the abstract Falcon specification.

The analytic error bounds in this file are still stated as proof obligations.
The end-to-end verifier bridge is reduced to explicit codec and fast-kernel
correctness assumptions so the remaining gap is spelled out precisely.

## Per-Operation Error Bounds

Each FPR arithmetic operation introduces at most a relative error of
`2^{-52}` (matching IEEE-754 binary64 precision):

- `|fpr_add(a, b) - (a_real + b_real)| ≤ 2^{-52} · |a_real + b_real|`
- `|fpr_mul(a, b) - a_real · b_real| ≤ 2^{-52} · |a_real · b_real|`

## Accumulated Error in ffSampling

The statistical distance between the FPR-based sampler output and the
ideal discrete Gaussian is bounded by the Rényi divergence analysis
from Pornin 2019, Section 3:

  `R_∞(D_FPR ‖ D_ideal) ≤ 1 + ε_renyi`

where `ε_renyi < 2^{-64}` for 53-bit mantissa precision.

## References

- Pornin 2019 (eprint 2019/893), Section 3 (precision analysis)
- Falcon specification v1.2, Section 2.5.2 (sampler quality)
-/

@[expose] public section


namespace Falcon.Concrete.FPRBridge

open Falcon.Concrete.FPR

noncomputable section

/-! ## Interpretation: FPR → ℝ -/

/-! ### Layer 1: bit-level decomposition (pure `Nat`/`Bool`, no `ℝ`) -/

/-- The three IEEE-754 binary64 bit fields of an `FPR` word: sign bit, 11-bit biased
exponent, and 52-bit mantissa (implicit leading `1` for normal values), matching the
layout documented in `FPR.lean`'s module docstring (bit 63 / bits 62-52 / bits 51-0). -/
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

/-- The mantissa field extracted by `FPR.decode` is always below `2^52`: it is literally
reduced modulo `2^52` in the definition of `FPR.decode`. -/
theorem FPR.decode_mantissa_lt (x : FPR) : (FPR.decode x).mantissa < 2 ^ 52 := by
  unfold FPR.decode
  exact Nat.mod_lt _ (by norm_num)

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
  · rw [if_neg he, if_neg h, if_neg he, max_eq_left (by omega : 1 ≤ b.exponent)]
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
  · rw [if_pos h1, if_pos h1, abs_mul, abs_mul, hsign1,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ (b.mantissa : ℝ)),
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ (-(1074 : ℤ)))]
    ring
  · rw [if_neg h1, if_neg h1]
    by_cases h2 : b.exponent = 2047
    · rw [if_pos h2, if_pos h2, abs_zero]
    · rw [if_neg h2, if_neg h2, abs_mul, abs_mul, hsign1,
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
  rw [FPR.Bits.abs_toReal_eq, if_neg he0, if_neg he]
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
reconstruction, `FPR.Bits.toReal_eq_of_exponent_ne_2047`. -/
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
bit. None of the three reaches `FPR.add` itself yet (the conditional swap and every later pipeline
stage — alignment/sticky-bit shift, sign combination, leading-zero renormalization, final
round-to-nearest — remain open); they are reusable infrastructure for that larger proof. -/

/-- The unsigned integer packing of a decoded field triple's exponent and mantissa fields into
a single natural number, `exponent * 2^52 + mantissa`. Orders identically to real magnitude via
`FPR.Bits.abs_toReal_lt_iff_magKey_lt`, and is exactly what masking an `FPR` word's sign bit off
computes via `toNat_and_low63Mask_eq_magKey`. -/
def FPR.Bits.magKey (b : FPR.Bits) : ℕ := b.exponent * 2 ^ 52 + b.mantissa

/-- Two finite (non-Inf/NaN) decoded field triples are ordered by real magnitude exactly as
their `FPR.Bits.magKey` values are ordered: a strictly larger exponent always dominates any
mantissa difference (the significand fraction is always below `2`), and for equal exponents the
comparison reduces to the mantissa alone. Holds uniformly across the subnormal/normal boundary
(no `FPR.Bits.IsNormal` hypothesis is needed). -/
theorem FPR.Bits.abs_toReal_lt_iff_magKey_lt (b1 b2 : FPR.Bits)
    (hm1 : b1.mantissa < 2 ^ 52) (hm2 : b2.mantissa < 2 ^ 52)
    (h1 : b1.exponent ≠ 2047) (h2 : b2.exponent ≠ 2047) :
    |b1.toReal| < |b2.toReal| ↔ b1.magKey < b2.magKey := by
  unfold FPR.Bits.magKey
  rw [FPR.Bits.abs_toReal_eq, FPR.Bits.abs_toReal_eq]
  rw [if_neg h1, if_neg h2]
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
theorem toNat_and_low63Mask (x : UInt64) :
    (x &&& (((1 : UInt64) <<< 63) - 1)).toNat = x.toNat % 2 ^ 63 := by
  rw [UInt64.toNat_and]
  have h1 : (((1 : UInt64) <<< 63) - 1).toNat = 2 ^ 63 - 1 := by decide
  rw [h1]
  exact Nat.and_two_pow_sub_one_eq_mod x.toNat 63

/-- Masking an `FPR` word with the low-63-bit all-ones pattern (the sign-stripping mask `M63`
used inside `FPR.add`'s compare-and-swap step) computes exactly `FPR.Bits.magKey` of its
decoded fields. -/
theorem toNat_and_low63Mask_eq_magKey (x : FPR) :
    (x &&& (((1 : UInt64) <<< 63) - 1)).toNat = (FPR.decode x).magKey := by
  rw [toNat_and_low63Mask]
  unfold FPR.decode FPR.Bits.magKey
  simp only [Nat.shiftRight_eq_div_pow]
  omega

/-- The classic "subtract and test the top bit" unsigned-comparison trick, valid on 63-bit
`UInt64` patterns (the sign-stripped operand shape `FPR.add`'s `za := (x &&& M63) - (y &&& M63)`
step produces): the top bit of `p - q` is set exactly when `p < q`. Proved by unfolding to the
underlying `Nat` subtraction modulo `2^64` and case-splitting on whether it wraps. -/
theorem sub_shiftRight_63_eq_one_iff_lt (p q : UInt64)
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
theorem or_and_sub_one_shiftRight_63_eq_of_ne_zero (p q x : UInt64) (h : p ≠ q)
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
theorem za'_shiftRight_63_eq_one_iff (p q x : UInt64)
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

end

/-! ## Bit-level structure of the `FPR` arithmetic kernels

The integer kernels `FPR.add` / `FPR.mul` / `FPR.div` / `FPR.sqrt` / `FPR.scaled` all run the
same three-stage pipeline on a working significand: an *alignment/truncation* stage that folds
every discarded bit into a single sticky bit, a *renormalisation* stage that left-aligns the
result using a leading-zero count, and a *final assembly* stage that rounds to nearest with
ties to even and packs the sign/exponent/significand fields into an IEEE-754 word.

The three groups below characterise those stages at the bit level, independently of any one
operation, in terms of the actual `UInt64` / `UInt32` / `Int32` objects the kernels manipulate:

* `stickyShift` and the `or_fold_shiftRight*` family: the `(v ||| ((v &&& mask) + mask)) >>> k`
  idiom computes a right shift whose low bit records whether anything was discarded, so it is
  within one output unit of the exact value (`stickyShift_mul_lt`, `lt_stickyShift_mul_add`)
  and never loses zero-ness (`stickyShift_eq_zero_iff`).
* `lzcnt_nonzero_spec` / `lzcnt64_nonzero_spec` / `lzcnt64_nonzero_unique`: the five-step binary
  search counts leading zeros exactly, so the shifted significand has its top bit set
  (`fpr_ulsh_lzcnt64_top_bit`) and loses no bits (`fpr_ulsh_lzcnt64_toNat`); combined with
  `toInt_sub_lzcnt64_nonzero_or_one_toInt32` this covers both halves of the `(significand,
  exponent)` pair `FPR.add` and `FPR.scaled` renormalise to.
* `roundQuarterTiesEven` and `roundTableBit`: the constant table `0xC8` implements
  round-to-nearest-ties-even on the two bits discarded by `m >>> 2`, and the final assembly
  `FPR.make` / `FPR.make_z` denotes `± m * 2 ^ e` up to relative error `2 ^ (-53)`
  (`abs_toRealBits_make_sub_le`), including the self-normalising case where the rounding carry
  overflows the mantissa field into the exponent field.

Several statements mention `Falcon.Concrete.FPR`'s `private` helpers (`fpr_ulsh`, `fpr_ursh`,
`lzcnt_nonzero`, `lzcnt64_nonzero`, `make`, `make_z`), reachable here through the
`import all` above, and are therefore `private` themselves. -/

/-! ### The sticky fold on `ℕ` -/

/-- The value obtained by shifting `v` right by `k` bits while folding the discarded bits into
a *sticky bit*: the low bit of the result is additionally set whenever any of the `k` discarded
bits of `v` was set. -/
def stickyShift (v k : ℕ) : ℕ := (v >>> k) ||| (if v % 2 ^ k = 0 then 0 else 1)

/-- Bitwise-or with `1` only forces the low bit. -/
theorem or_one_eq (q : ℕ) : q ||| 1 = 2 * (q / 2) + 1 := by
  have h1 : (q ||| 1) / 2 = q / 2 := by
    have := @Nat.shiftRight_or_distrib 1 q 1
    simpa [Nat.shiftRight_eq_div_pow] using this
  have h2 : (q ||| 1) % 2 = 1 := by
    simp
  omega

/-- Adding the all-ones mask `2 ^ k - 1` to a `k`-bit value carries into bit `k` exactly when
that value is nonzero: this is the core of the sticky-bit idiom. -/
theorem shiftRight_add_two_pow_sub_one (k r : ℕ) (hr : r < 2 ^ k) :
    (r + (2 ^ k - 1)) >>> k = if r = 0 then 0 else 1 := by
  rw [Nat.shiftRight_eq_div_pow]
  have hN : 0 < 2 ^ k := Nat.two_pow_pos k
  by_cases h : r = 0
  · subst h
    rw [if_pos rfl]
    exact Nat.div_eq_of_lt (by omega)
  · rw [if_neg h]
    refine Nat.div_eq_of_lt_le ?_ ?_ <;> omega

/-- Closed form of the sticky fold: it is `v` shifted right by `k + 1` and doubled, plus a single
low bit that records whether `v` failed to be an exact multiple of `2 ^ (k + 1)`. -/
theorem stickyShift_eq (v k : ℕ) :
    stickyShift v k = 2 * (v / 2 ^ (k + 1)) + (if v % 2 ^ (k + 1) = 0 then 0 else 1) := by
  have hN : 0 < 2 ^ k := Nat.two_pow_pos k
  have hdiv : v / 2 ^ k / 2 = v / 2 ^ (k + 1) := by
    rw [Nat.div_div_eq_div_mul, ← pow_succ]
  unfold stickyShift
  rw [Nat.shiftRight_eq_div_pow]
  by_cases h : v % 2 ^ k = 0
  · rw [if_pos h, Nat.or_zero]
    have hvm : v = 2 ^ k * (v / 2 ^ k) := (Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero h)).symm
    have hmod : v % 2 ^ (k + 1) = 2 ^ k * ((v / 2 ^ k) % 2) := by
      conv_lhs => rw [hvm]
      rw [pow_succ, Nat.mul_mod_mul_left]
    have hz : v % 2 ^ (k + 1) = 0 ↔ (v / 2 ^ k) % 2 = 0 := by
      rw [hmod]
      constructor
      · intro hc
        rcases Nat.mul_eq_zero.mp hc with hc' | hc' <;> omega
      · intro hc; rw [hc, Nat.mul_zero]
    rw [← hdiv]
    by_cases hm : (v / 2 ^ k) % 2 = 0
    · rw [if_pos (hz.mpr hm)]; omega
    · rw [if_neg (fun hc => hm (hz.mp hc))]; omega
  · rw [if_neg h]
    have h' : v % 2 ^ (k + 1) ≠ 0 := by
      intro hc
      apply h
      have hmm := Nat.mod_mod_of_dvd v (pow_dvd_pow 2 (Nat.le_succ k))
      rw [hc, Nat.zero_mod] at hmm
      exact hmm.symm
    rw [if_neg h', or_one_eq, hdiv]

/-- The sticky fold vanishes exactly on `0`: no information about zero-ness is lost. -/
theorem stickyShift_eq_zero_iff (v k : ℕ) : stickyShift v k = 0 ↔ v = 0 := by
  constructor
  · intro h
    rw [stickyShift_eq] at h
    by_cases hR : v % 2 ^ (k + 1) = 0
    · rw [if_pos hR] at h
      have hD : v / 2 ^ (k + 1) = 0 := by omega
      have hdm := Nat.div_add_mod v (2 ^ (k + 1))
      rw [hD, hR, Nat.mul_zero, Nat.add_zero] at hdm
      exact hdm.symm
    · rw [if_neg hR] at h
      omega
  · rintro rfl
    simp [stickyShift]

/-- The low bit of the sticky fold records whether `v` was an exact multiple of `2 ^ (k + 1)`:
this is precisely the information a subsequent round-to-nearest-even step needs. -/
theorem stickyShift_mod_two (v k : ℕ) :
    stickyShift v k % 2 = if v % 2 ^ (k + 1) = 0 then 0 else 1 := by
  rw [stickyShift_eq]
  by_cases hR : v % 2 ^ (k + 1) = 0
  · rw [if_pos hR]
    omega
  · rw [if_neg hR]
    omega

/-- The sticky fold moves the value by strictly less than one output unit in the last place. -/
theorem stickyShift_mul_lt (v k : ℕ) : stickyShift v k * 2 ^ k < v + 2 ^ k := by
  rw [stickyShift_eq]
  have hN : 0 < (2 : ℕ) ^ k := Nat.two_pow_pos k
  have hp : (2 : ℕ) ^ (k + 1) = 2 * 2 ^ k := by rw [pow_succ]; ring
  have hdm := Nat.div_add_mod v (2 ^ (k + 1))
  have hlt := Nat.mod_lt v (Nat.two_pow_pos (k + 1))
  have hkey : 2 ^ (k + 1) * (v / 2 ^ (k + 1)) = 2 * 2 ^ k * (v / 2 ^ (k + 1)) := by rw [hp]
  by_cases hR : v % 2 ^ (k + 1) = 0
  · rw [if_pos hR]
    linarith
  · rw [if_neg hR]
    have : 0 < v % 2 ^ (k + 1) := Nat.pos_of_ne_zero hR
    linarith

/-- The sticky fold never falls short of the original value by a full output unit in the last
place either: together with `stickyShift_mul_lt` this pins it to within one ulp of `v`. -/
theorem lt_stickyShift_mul_add (v k : ℕ) : v < stickyShift v k * 2 ^ k + 2 ^ k := by
  rw [stickyShift_eq]
  have hN : 0 < (2 : ℕ) ^ k := Nat.two_pow_pos k
  have hp : (2 : ℕ) ^ (k + 1) = 2 * 2 ^ k := by rw [pow_succ]; ring
  have hdm := Nat.div_add_mod v (2 ^ (k + 1))
  have hlt := Nat.mod_lt v (Nat.two_pow_pos (k + 1))
  have hkey : 2 ^ (k + 1) * (v / 2 ^ (k + 1)) = 2 * 2 ^ k * (v / 2 ^ (k + 1)) := by rw [hp]
  by_cases hR : v % 2 ^ (k + 1) = 0
  · rw [if_pos hR]
    linarith
  · rw [if_neg hR]
    linarith

/-! ### The sticky fold on `UInt64` -/

/-- The all-ones mask `(1 <<< k) - 1` denotes `2 ^ k - 1` for shift counts below the word size. -/
theorem toNat_one_shiftLeft_sub_one {k : UInt64} (hk : k.toNat < 64) :
    ((1 : UInt64) <<< k - 1).toNat = 2 ^ k.toNat - 1 := by
  have hlt : 2 ^ k.toNat < 2 ^ 64 := Nat.pow_lt_pow_right (by norm_num) hk
  have h1 : (1 : UInt64).toNat = 1 := by decide
  have hone : ((1 : UInt64) <<< k).toNat = 2 ^ k.toNat := by
    rw [UInt64.toNat_shiftLeft, Nat.mod_eq_of_lt hk, Nat.shiftLeft_eq, h1, one_mul,
      Nat.mod_eq_of_lt hlt]
  have hpos : 0 < 2 ^ k.toNat := Nat.two_pow_pos _
  rw [UInt64.toNat_sub, hone, h1]
  omega

/-- Masking with `(1 <<< k) - 1` keeps exactly the low `k` bits. -/
theorem toNat_and_one_shiftLeft_sub_one (v k : UInt64) (hk : k.toNat < 64) :
    (v &&& ((1 : UInt64) <<< k - 1)).toNat = v.toNat % 2 ^ k.toNat := by
  rw [UInt64.toNat_and, toNat_one_shiftLeft_sub_one hk]
  exact Nat.and_two_pow_sub_one_eq_mod _ _

/-- The masked low bits vanish exactly when the discarded part of `v` is zero. -/
theorem and_one_shiftLeft_sub_one_eq_zero_iff (v k : UInt64) (hk : k.toNat < 64) :
    v &&& ((1 : UInt64) <<< k - 1) = 0 ↔ v.toNat % 2 ^ k.toNat = 0 := by
  rw [← UInt64.toNat_inj, toNat_and_one_shiftLeft_sub_one v k hk]
  constructor
  · intro h; rw [h]; rfl
  · intro h; rw [h]; rfl

/-- Core sticky-bit step on `UInt64`: adding the low-`k` all-ones mask to the masked low bits of
`v` carries into bit `k` exactly when one of those discarded bits was set. -/
theorem and_add_mask_shiftRight (v k : UInt64) (hk : k.toNat < 64) :
    ((v &&& ((1 : UInt64) <<< k - 1)) + ((1 : UInt64) <<< k - 1)) >>> k
      = if v &&& ((1 : UInt64) <<< k - 1) = 0 then 0 else 1 := by
  have hM := toNat_one_shiftLeft_sub_one hk
  have hr := toNat_and_one_shiftLeft_sub_one v k hk
  have hrlt : v.toNat % 2 ^ k.toNat < 2 ^ k.toNat := Nat.mod_lt _ (Nat.two_pow_pos _)
  have hkle : (2 : ℕ) ^ k.toNat ≤ 2 ^ 63 := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h63 : (2 : ℕ) ^ 63 * 2 = 2 ^ 64 := by norm_num
  have hsum : ((v &&& ((1 : UInt64) <<< k - 1)) + ((1 : UInt64) <<< k - 1)).toNat
      = v.toNat % 2 ^ k.toNat + (2 ^ k.toNat - 1) := by
    rw [UInt64.toNat_add, hr, hM]
    exact Nat.mod_eq_of_lt (by omega)
  by_cases h : v &&& ((1 : UInt64) <<< k - 1) = 0
  · rw [if_pos h, ← UInt64.toNat_inj, UInt64.toNat_shiftRight, hsum, Nat.mod_eq_of_lt hk,
      shiftRight_add_two_pow_sub_one _ _ hrlt,
      if_pos ((and_one_shiftLeft_sub_one_eq_zero_iff v k hk).mp h)]
    rfl
  · rw [if_neg h, ← UInt64.toNat_inj, UInt64.toNat_shiftRight, hsum, Nat.mod_eq_of_lt hk,
      shiftRight_add_two_pow_sub_one _ _ hrlt,
      if_neg fun hc => h ((and_one_shiftLeft_sub_one_eq_zero_iff v k hk).mpr hc)]
    rfl

/-- The sticky or-fold on `UInt64`: shifting `v ||| ((v &&& mask) + mask)` right by `k` yields
`v >>> k` with its low bit additionally set exactly when one of the `k` discarded bits of `v`
was set. This is the idiom used by `FPR.add`, `FPR.mul` and `FPR.scaled`. -/
theorem or_fold_shiftRight (v k : UInt64) (hk : k.toNat < 64) :
    (v ||| ((v &&& ((1 : UInt64) <<< k - 1)) + ((1 : UInt64) <<< k - 1))) >>> k
      = (v >>> k) ||| (if v &&& ((1 : UInt64) <<< k - 1) = 0 then 0 else 1) := by
  rw [UInt64.shiftRight_or, and_add_mask_shiftRight v k hk]

/-- A shifted value with an explicit sticky bit or-ed in denotes `stickyShift`. -/
theorem toNat_shiftRight_or_sticky (v k : UInt64) (hk : k.toNat < 64) :
    ((v >>> k) ||| (if v &&& ((1 : UInt64) <<< k - 1) = 0 then 0 else 1)).toNat
      = stickyShift v.toNat k.toNat := by
  rw [UInt64.toNat_or, UInt64.toNat_shiftRight, Nat.mod_eq_of_lt hk, stickyShift]
  by_cases h : v &&& ((1 : UInt64) <<< k - 1) = 0
  · rw [if_pos h, if_pos ((and_one_shiftLeft_sub_one_eq_zero_iff v k hk).mp h)]
    rfl
  · rw [if_neg h, if_neg fun hc => h ((and_one_shiftLeft_sub_one_eq_zero_iff v k hk).mpr hc)]
    rfl

/-- Semantics of the sticky or-fold: it computes exactly `stickyShift` of the underlying
natural number, so the bounds in `stickyShift_mul_lt`, `lt_stickyShift_mul_add`,
`stickyShift_mod_two` and `stickyShift_eq_zero_iff` apply to it. -/
theorem toNat_or_fold_shiftRight (v k : UInt64) (hk : k.toNat < 64) :
    ((v ||| ((v &&& ((1 : UInt64) <<< k - 1)) + ((1 : UInt64) <<< k - 1))) >>> k).toNat
      = stickyShift v.toNat k.toNat := by
  rw [or_fold_shiftRight v k hk, toNat_shiftRight_or_sticky v k hk]

/-- The or-fold preserves zero-ness exactly: the folded value vanishes iff the input did. This is
what makes the subsequent `make_z` zero-detection faithful: a caller who reduces a working
significand's collapse to a statement about the *pre-fold* value being `0` can transport it
through here, then land on `toRealBits_make_z_of_zero` for the resulting denotation. -/
theorem or_fold_shiftRight_eq_zero_iff (v k : UInt64) (hk : k.toNat < 64) :
    (v ||| ((v &&& ((1 : UInt64) <<< k - 1)) + ((1 : UInt64) <<< k - 1))) >>> k = 0 ↔ v = 0 := by
  have h0 : (0 : UInt64).toNat = 0 := rfl
  rw [← UInt64.toNat_inj, ← UInt64.toNat_inj (a := v), h0, toNat_or_fold_shiftRight v k hk]
  exact stickyShift_eq_zero_iff v.toNat k.toNat

/-- The low bit of the or-folded value is the sticky bit: it is set exactly when `v` was not an
exact multiple of `2 ^ (k + 1)`, i.e. exactly when a subsequent round-to-nearest step must
break a tie away from even. -/
theorem toNat_or_fold_shiftRight_mod_two (v k : UInt64) (hk : k.toNat < 64) :
    ((v ||| ((v &&& ((1 : UInt64) <<< k - 1)) + ((1 : UInt64) <<< k - 1))) >>> k).toNat % 2
      = if v.toNat % 2 ^ (k.toNat + 1) = 0 then 0 else 1 := by
  rw [toNat_or_fold_shiftRight v k hk, stickyShift_mod_two]

/-! ### The `FPR.add` alignment shift

`FPR.add` aligns the smaller operand with `fpr_ursh (yu ||| ((yu &&& m) + m)) n'`, where
`m = fpr_ulsh 1 n' - 1` and `n' = n &&& 63`. -/

/-- The shift count `n &&& 63` used by `FPR.add` always stays below the word size. -/
theorem toNat_toUInt64_and_63_lt (n : UInt32) : ((n &&& 63).toUInt64).toNat < 64 := by
  rw [UInt32.toNat_toUInt64, UInt32.toNat_and]
  have hle : n.toNat &&& (63 : UInt32).toNat ≤ (63 : UInt32).toNat := Nat.and_le_right
  have h63 : (63 : UInt32).toNat = 63 := by decide
  omega

/-- The alignment step of `FPR.add`: shifting right by `n &&& 63` after the or-fold keeps the
shifted value and records in its low bit whether any shifted-out bit of `yu` was set.

This is the shape `fpr_ursh (yu ||| ((yu &&& m) + m)) (n &&& 63)` with
`m = fpr_ulsh 1 (n &&& 63) - 1`, after unfolding the two inline shift wrappers. -/
theorem or_fold_shiftRight_toUInt64_and_63 (yu : UInt64) (n : UInt32) :
    (yu ||| ((yu &&& ((1 : UInt64) <<< (n &&& 63).toUInt64 - 1))
          + ((1 : UInt64) <<< (n &&& 63).toUInt64 - 1))) >>> (n &&& 63).toUInt64
      = (yu >>> (n &&& 63).toUInt64)
        ||| (if yu &&& ((1 : UInt64) <<< (n &&& 63).toUInt64 - 1) = 0 then 0 else 1) :=
  or_fold_shiftRight yu (n &&& 63).toUInt64 (toNat_toUInt64_and_63_lt n)

/-- Semantics of the `FPR.add` alignment step. -/
theorem toNat_or_fold_shiftRight_toUInt64_and_63 (yu : UInt64) (n : UInt32) :
    ((yu ||| ((yu &&& ((1 : UInt64) <<< (n &&& 63).toUInt64 - 1))
          + ((1 : UInt64) <<< (n &&& 63).toUInt64 - 1))) >>> (n &&& 63).toUInt64).toNat
      = stickyShift yu.toNat (n &&& 63).toNat := by
  rw [← UInt32.toNat_toUInt64 (n &&& 63)]
  exact toNat_or_fold_shiftRight yu (n &&& 63).toUInt64 (toNat_toUInt64_and_63_lt n)

/-! ### The nine-bit rounding fold of `FPR.add` and `FPR.scaled` -/

/-- The final rounding fold of `FPR.add` (and of `FPR.scaled`), with the concrete mask
`0x1FF = 2 ^ 9 - 1`. -/
theorem or_fold_shiftRight_nine (v : UInt64) :
    (v ||| ((v &&& 0x1FF) + 0x1FF)) >>> 9
      = (v >>> 9) ||| (if v &&& 0x1FF = 0 then 0 else 1) := by
  have hmask : (1 : UInt64) <<< (9 : UInt64) - 1 = 0x1FF := by decide
  have h := or_fold_shiftRight v 9 (by decide)
  rwa [hmask] at h

/-- Semantics of the nine-bit rounding fold. -/
theorem toNat_or_fold_shiftRight_nine (v : UInt64) :
    ((v ||| ((v &&& 0x1FF) + 0x1FF)) >>> 9).toNat = stickyShift v.toNat 9 := by
  have hmask : (1 : UInt64) <<< (9 : UInt64) - 1 = 0x1FF := by decide
  have hk : (9 : UInt64).toNat = 9 := by decide
  have h := toNat_or_fold_shiftRight v 9 (by decide)
  rwa [hmask, hk] at h

/-! ### The `(v >>> es) ||| (v &&& 1)` renormalisation of `FPR.mul` and `FPR.div`

Both `FPR.mul` and `FPR.div` renormalise a `55`-bit quotient/product with
`q >>> es ||| (q &&& 1)`, where `es = q >>> 55` is `0` or `1`. Since at most one bit is
discarded, or-ing bit `0` back in is exactly the sticky fold. The hypothesis `es.toNat ≤ 1`
is the surrounding range invariant of those two kernels, not a bit-level fact: the statement
genuinely fails for larger `es`. -/

/-- Bitwise absorption: or-ing a submask of `v` back into `v` changes nothing. -/
theorem or_and_self (v w : UInt64) : v ||| (v &&& w) = v := by
  rw [← UInt64.toNat_inj, UInt64.toNat_or, UInt64.toNat_and]
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_or, Nat.testBit_and]
  cases v.toNat.testBit i <;> simp

/-- `0` is neutral for bitwise or. -/
theorem or_zero (v : UInt64) : v ||| 0 = v := by
  rw [← UInt64.toNat_inj, UInt64.toNat_or]
  exact Nat.or_zero _

/-- Masking with `1` extracts the low bit, so the result is `0` or `1`. -/
theorem and_one_eq_zero_or_one (v : UInt64) : v &&& 1 = 0 ∨ v &&& 1 = 1 := by
  have hmod : (v &&& 1).toNat = v.toNat % 2 := by
    have h1 : (1 : UInt64).toNat = 2 ^ 1 - 1 := by decide
    rw [UInt64.toNat_and, h1, Nat.and_two_pow_sub_one_eq_mod, pow_one]
  have h2 : v.toNat % 2 = 0 ∨ v.toNat % 2 = 1 := by omega
  rcases h2 with h2 | h2
  · left
    rw [← UInt64.toNat_inj, hmod, h2]
    rfl
  · right
    rw [← UInt64.toNat_inj, hmod, h2]
    rfl

/-- Renormalising by `es ≤ 1` places and or-ing bit `0` back in is the sticky fold for a
shift of `es` places. -/
theorem shiftRight_or_and_one (v es : UInt64) (hes : es.toNat ≤ 1) :
    (v >>> es) ||| (v &&& 1)
      = (v >>> es) ||| (if v &&& ((1 : UInt64) <<< es - 1) = 0 then 0 else 1) := by
  have hcase : es = 0 ∨ es = 1 := by
    have h : es.toNat = 0 ∨ es.toNat = 1 := by omega
    rcases h with h | h
    · left; rw [← UInt64.toNat_inj, h]; rfl
    · right; rw [← UInt64.toNat_inj, h]; rfl
  rcases hcase with rfl | rfl
  · have hm : (1 : UInt64) <<< (0 : UInt64) - 1 = 0 := by decide
    have hz : v &&& (0 : UInt64) = 0 := by
      rw [← UInt64.toNat_inj, UInt64.toNat_and]
      exact Nat.and_zero _
    have hsr : v >>> (0 : UInt64) = v := by
      rw [← UInt64.toNat_inj, UInt64.toNat_shiftRight]
      rfl
    rw [hm, hz, if_pos rfl, hsr, or_and_self, or_zero]
  · have hm : (1 : UInt64) <<< (1 : UInt64) - 1 = 1 := by decide
    rw [hm]
    rcases and_one_eq_zero_or_one v with h | h
    · rw [h, if_pos rfl]
    · rw [h, if_neg (by decide : ¬ (1 : UInt64) = 0)]

/-- Semantics of the `FPR.mul` / `FPR.div` renormalisation step. -/
theorem toNat_shiftRight_or_and_one (v es : UInt64) (hes : es.toNat ≤ 1) :
    ((v >>> es) ||| (v &&& 1)).toNat = stickyShift v.toNat es.toNat := by
  rw [shiftRight_or_and_one v es hes]
  exact toNat_shiftRight_or_sticky v es (by omega)

/-! ### The 25-bit sticky bit inside `FPR.mul` -/

/-- Adding the low-`k` all-ones mask to a value known to fit in `k` bits carries into bit `k`
exactly when the value is nonzero. `UInt32` version. -/
theorem uint32_add_mask_shiftRight_of_lt (v k : UInt32) (hk : k.toNat < 32)
    (hv : v.toNat < 2 ^ k.toNat) :
    (v + ((1 : UInt32) <<< k - 1)) >>> k = if v = 0 then 0 else 1 := by
  have h1 : (1 : UInt32).toNat = 1 := by decide
  have hlt : 2 ^ k.toNat < 2 ^ 32 := Nat.pow_lt_pow_right (by norm_num) hk
  have hone : ((1 : UInt32) <<< k).toNat = 2 ^ k.toNat := by
    rw [UInt32.toNat_shiftLeft, Nat.mod_eq_of_lt hk, Nat.shiftLeft_eq, h1, one_mul,
      Nat.mod_eq_of_lt hlt]
  have hpos : 0 < 2 ^ k.toNat := Nat.two_pow_pos _
  have hM : ((1 : UInt32) <<< k - 1).toNat = 2 ^ k.toNat - 1 := by
    rw [UInt32.toNat_sub, hone, h1]
    omega
  have hkle : (2 : ℕ) ^ k.toNat ≤ 2 ^ 31 := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h31 : (2 : ℕ) ^ 31 * 2 = 2 ^ 32 := by norm_num
  have hsum : (v + ((1 : UInt32) <<< k - 1)).toNat = v.toNat + (2 ^ k.toNat - 1) := by
    rw [UInt32.toNat_add, hM]
    exact Nat.mod_eq_of_lt (by omega)
  have hviff : v = 0 ↔ v.toNat = 0 := by
    constructor
    · rintro rfl; rfl
    · intro h; rw [← UInt32.toNat_inj, h]; rfl
  by_cases h : v = 0
  · rw [if_pos h, ← UInt32.toNat_inj, UInt32.toNat_shiftRight, hsum, Nat.mod_eq_of_lt hk,
      shiftRight_add_two_pow_sub_one _ _ hv, if_pos (hviff.mp h)]
    rfl
  · rw [if_neg h, ← UInt32.toNat_inj, UInt32.toNat_shiftRight, hsum, Nat.mod_eq_of_lt hk,
      shiftRight_add_two_pow_sub_one _ _ hv, if_neg fun hc => h (hviff.mpr hc)]
    rfl

/-- The 25-bit sticky bit `FPR.mul` folds into the product: the low `25`-bit limbs `z0` and
`z1'` contribute a carry into bit `25` exactly when one of them is nonzero. -/
theorem masked_or_add_shiftRight_25 (a b : UInt32) :
    (((a &&& 0x01FFFFFF) ||| (b &&& 0x01FFFFFF)) + 0x01FFFFFF) >>> 25
      = if (a &&& 0x01FFFFFF) ||| (b &&& 0x01FFFFFF) = 0 then 0 else 1 := by
  have hmask : (1 : UInt32) <<< (25 : UInt32) - 1 = 0x01FFFFFF := by decide
  have hMn : (0x01FFFFFF : UInt32).toNat = 2 ^ 25 - 1 := by decide
  have hbound : ∀ x : UInt32, (x &&& 0x01FFFFFF).toNat < 2 ^ 25 := by
    intro x
    rw [UInt32.toNat_and, hMn, Nat.and_two_pow_sub_one_eq_mod]
    exact Nat.mod_lt _ (Nat.two_pow_pos _)
  have hv : ((a &&& 0x01FFFFFF) ||| (b &&& 0x01FFFFFF)).toNat < 2 ^ (25 : UInt32).toNat := by
    rw [show (25 : UInt32).toNat = 25 from by decide, UInt32.toNat_or]
    exact Nat.or_lt_two_pow (hbound a) (hbound b)
  have h := uint32_add_mask_shiftRight_of_lt _ 25 (by decide) hv
  rwa [hmask] at h

/-- `FPR.add` alignment step, in the exact shape of the kernel's `fpr_ursh` / `fpr_ulsh` call. -/
private theorem fpr_ursh_or_fold (yu : UInt64) (n : UInt32) :
    fpr_ursh (yu ||| ((yu &&& (fpr_ulsh 1 (n &&& 63) - 1)) + (fpr_ulsh 1 (n &&& 63) - 1)))
        (n &&& 63)
      = (yu >>> (n &&& 63).toUInt64)
        ||| (if yu &&& ((1 : UInt64) <<< (n &&& 63).toUInt64 - 1) = 0 then 0 else 1) :=
  or_fold_shiftRight_toUInt64_and_63 yu n

/-- `FPR.add` alignment step, semantic form. -/
private theorem toNat_fpr_ursh_or_fold (yu : UInt64) (n : UInt32) :
    (fpr_ursh (yu ||| ((yu &&& (fpr_ulsh 1 (n &&& 63) - 1)) + (fpr_ulsh 1 (n &&& 63) - 1)))
        (n &&& 63)).toNat
      = stickyShift yu.toNat (n &&& 63).toNat :=
  toNat_or_fold_shiftRight_toUInt64_and_63 yu n

/-! ### `UInt32` numeral evaluation for the leading-zero search

The shift amounts and mask widths appearing in `FPR.lzcnt_nonzero` are `UInt32` numerals; these
evaluate them so that `omega` sees genuine literals. -/

private theorem toNat_lit0 : (0 : UInt32).toNat = 0 := by decide
private theorem toNat_lit1 : (1 : UInt32).toNat = 1 := by decide
private theorem toNat_lit2 : (2 : UInt32).toNat = 2 := by decide
private theorem toNat_lit4 : (4 : UInt32).toNat = 4 := by decide
private theorem toNat_lit8 : (8 : UInt32).toNat = 8 := by decide
private theorem toNat_lit16 : (16 : UInt32).toNat = 16 := by decide

/-! ### High-bit masks

Each step of `FPR.lzcnt_nonzero` tests a prefix of its working word against a mask whose set bits
are exactly the top `32 - k` positions, i.e. the numeral `2 ^ 32 - 2 ^ k`. The lemmas here turn
those tests into the arithmetic statement `v.toNat < 2 ^ k`. -/

/-- The bits of the top-`(32 - k)` mask `2 ^ 32 - 2 ^ k` are exactly the positions in `[k, 32)`. -/
private theorem testBit_highMask {k : ℕ} (hk : k ≤ 32) (i : ℕ) :
    (2 ^ 32 - 2 ^ k).testBit i = (decide (k ≤ i) && decide (i < 32)) := by
  have hrw : 2 ^ 32 - 2 ^ k = (2 ^ (32 - k) - 1) <<< k := by
    rw [Nat.shiftLeft_eq, Nat.sub_mul, one_mul, ← pow_add]
    congr 2
    omega
  rw [hrw, Nat.testBit_shiftLeft, Nat.testBit_two_pow_sub_one]
  rcases Nat.lt_or_ge i k with h | h
  · simp [Nat.not_le.mpr h]
  · simp only [ge_iff_le, h, decide_true, Bool.true_and, decide_eq_decide]
    omega

/-- Masking a 32-bit natural number with `2 ^ 32 - 2 ^ k` clears its low `k` bits. -/
private theorem and_highMask_eq_shift {n k : ℕ} (hn : n < 2 ^ 32) (hk : k ≤ 32) :
    n &&& (2 ^ 32 - 2 ^ k) = n >>> k <<< k := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and, testBit_highMask hk, Nat.testBit_shiftLeft, Nat.testBit_shiftRight]
  rcases Nat.lt_or_ge i k with h | h
  · simp [Nat.not_le.mpr h]
  · rw [show k + (i - k) = i from by omega]
    rcases Nat.lt_or_ge i 32 with h2 | h2
    · simp [h, h2]
    · have hb : n.testBit i = false :=
        Nat.testBit_lt_two_pow (lt_of_lt_of_le hn (Nat.pow_le_pow_right (by norm_num) h2))
      simp [h, hb]

/-- A 32-bit natural number has no bits at or above position `k` exactly when it is below
`2 ^ k`. -/
private theorem and_highMask_eq_zero_iff {n k : ℕ} (hn : n < 2 ^ 32) (hk : k ≤ 32) :
    n &&& (2 ^ 32 - 2 ^ k) = 0 ↔ n < 2 ^ k := by
  rw [and_highMask_eq_shift hn hk, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow, Nat.mul_eq_zero]
  constructor
  · rintro (h | h)
    · exact (Nat.div_eq_zero_iff.mp h).resolve_left (Nat.two_pow_pos k).ne'
    · exact absurd h (Nat.two_pow_pos k).ne'
  · intro h
    exact Or.inl (Nat.div_eq_of_lt h)

/-- The `UInt32` form of `and_highMask_eq_zero_iff`, matching the shape of the mask tests inside
`FPR.lzcnt_nonzero`. -/
private theorem uint32_and_highMask_eq_zero_iff (v : UInt32) {k : ℕ} (hk : k ≤ 32)
    {M : UInt32} (hM : M.toNat = 2 ^ 32 - 2 ^ k) :
    (v &&& M = 0) ↔ v.toNat < 2 ^ k := by
  rw [← UInt32.toNat_inj, UInt32.toNat_and, hM, toNat_lit0]
  exact and_highMask_eq_zero_iff (UInt32.toNat_lt v) hk

/-- The step-1 mask test of `FPR.lzcnt_nonzero`. -/
private theorem and_mask16 (v : UInt32) : (v &&& 4294901760 = 0) ↔ v.toNat < 2 ^ 16 :=
  uint32_and_highMask_eq_zero_iff v (by norm_num) (by decide)

/-- The step-2 mask test of `FPR.lzcnt_nonzero`. -/
private theorem and_mask24 (v : UInt32) : (v &&& 4278190080 = 0) ↔ v.toNat < 2 ^ 24 :=
  uint32_and_highMask_eq_zero_iff v (by norm_num) (by decide)

/-- The step-3 mask test of `FPR.lzcnt_nonzero`. -/
private theorem and_mask28 (v : UInt32) : (v &&& 4026531840 = 0) ↔ v.toNat < 2 ^ 28 :=
  uint32_and_highMask_eq_zero_iff v (by norm_num) (by decide)

/-- The step-4 mask test of `FPR.lzcnt_nonzero`. -/
private theorem and_mask30 (v : UInt32) : (v &&& 3221225472 = 0) ↔ v.toNat < 2 ^ 30 :=
  uint32_and_highMask_eq_zero_iff v (by norm_num) (by decide)

/-- The step-5 (top-bit) test of `FPR.lzcnt_nonzero`. -/
private theorem and_mask31 (v : UInt32) : (v &&& 2147483648 = 0) ↔ v.toNat < 2 ^ 31 :=
  uint32_and_highMask_eq_zero_iff v (by norm_num) (by decide)

/-- The step-1 shift of `FPR.lzcnt_nonzero`, in arithmetic form. -/
private theorem toNat_shl16 (v : UInt32) : (v <<< 16).toNat = v.toNat * 2 ^ 16 % 2 ^ 32 := by
  rw [UInt32.toNat_shiftLeft, toNat_lit16, Nat.shiftLeft_eq]

/-- The step-2 shift of `FPR.lzcnt_nonzero`, in arithmetic form. -/
private theorem toNat_shl8 (v : UInt32) : (v <<< 8).toNat = v.toNat * 2 ^ 8 % 2 ^ 32 := by
  rw [UInt32.toNat_shiftLeft, toNat_lit8, Nat.shiftLeft_eq]

/-- The step-3 shift of `FPR.lzcnt_nonzero`, in arithmetic form. -/
private theorem toNat_shl4 (v : UInt32) : (v <<< 4).toNat = v.toNat * 2 ^ 4 % 2 ^ 32 := by
  rw [UInt32.toNat_shiftLeft, toNat_lit4, Nat.shiftLeft_eq]

/-- The step-4 shift of `FPR.lzcnt_nonzero`, in arithmetic form. -/
private theorem toNat_shl2 (v : UInt32) : (v <<< 2).toNat = v.toNat * 2 ^ 2 % 2 ^ 32 := by
  rw [UInt32.toNat_shiftLeft, toNat_lit2, Nat.shiftLeft_eq]

/-! ### 32-bit leading-zero count -/

/-- `FPR.lzcnt_nonzero` never returns more than `31`: each of its five steps contributes at most
its own shift width, and `16 + 8 + 4 + 2 + 1 = 31`. -/
private theorem lzcnt_nonzero_toNat_le (x : UInt32) : (lzcnt_nonzero x).toNat ≤ 31 := by
  simp only [lzcnt_nonzero, Id.run]
  dsimp only [pure, Id.instMonad]
  split_ifs <;>
    norm_num [UInt32.toNat_add, toNat_lit0, toNat_lit1, toNat_lit2, toNat_lit4, toNat_lit8,
      toNat_lit16]

/-- `FPR.lzcnt_nonzero x` is the number of leading zero bits of a nonzero 32-bit word `x`: it is
the unique `c` with `2 ^ (31 - c) ≤ x < 2 ^ (32 - c)`. Proved by running the five-step binary
search symbolically (`split_ifs`), each branch then being linear arithmetic over the mask and
shift translations above. -/
private theorem lzcnt_nonzero_spec (x : UInt32) (hx : x ≠ 0) :
    2 ^ (31 - (lzcnt_nonzero x).toNat) ≤ x.toNat ∧
      x.toNat < 2 ^ (32 - (lzcnt_nonzero x).toNat) := by
  have hxN : x.toNat ≠ 0 := fun h0 => hx (UInt32.toNat_inj.mp (by simpa using h0))
  have hxlt : x.toNat < 2 ^ 32 := UInt32.toNat_lt x
  simp only [lzcnt_nonzero, Id.run]
  dsimp only [pure, Id.instMonad]
  simp only [beq_iff_eq, and_mask16, and_mask24, and_mask28, and_mask30, and_mask31,
    toNat_shl16, toNat_shl8, toNat_shl4, toNat_shl2]
  split_ifs <;>
    (norm_num [UInt32.toNat_add, toNat_lit0, toNat_lit1, toNat_lit2, toNat_lit4, toNat_lit8,
      toNat_lit16]; omega)

/-! ### 64-bit leading-zero count -/

/-- The high half `(x >>> 32).toUInt32` of a `UInt64` is its quotient by `2 ^ 32`. -/
private theorem toUInt32_shiftRight32_toNat (x : UInt64) :
    (x >>> 32).toUInt32.toNat = x.toNat / 2 ^ 32 := by
  rw [UInt64.toNat_toUInt32, UInt64.toNat_shiftRight]
  norm_num [Nat.shiftRight_eq_div_pow]
  have hb : (0 : ℕ) < 2 ^ 32 := by positivity
  have hlt : x.toNat / 2 ^ 32 < 2 ^ 32 := by
    rw [Nat.div_lt_iff_lt_mul hb]
    calc x.toNat < 2 ^ 64 := UInt64.toNat_lt x
      _ = 2 ^ 32 * 2 ^ 32 := by norm_num
  exact Nat.mod_eq_of_lt hlt

/-- The "is it nonzero" idiom `y ||| (0 - y)` of `FPR.lzcnt64_nonzero`: a nonzero word or'd with
its two's-complement negation always has its top bit set, since one of the two summands exceeds
`2 ^ 31`. -/
private theorem or_neg_shiftRight_31 (y : UInt32) (hy : y ≠ 0) :
    (y ||| ((0 : UInt32) - y)) >>> 31 = 1 := by
  have hyN : y.toNat ≠ 0 := fun h0 => hy (UInt32.toNat_inj.mp (by simpa using h0))
  have hylt : y.toNat < 2 ^ 32 := UInt32.toNat_lt y
  rw [← UInt32.toNat_inj, UInt32.toNat_shiftRight, UInt32.toNat_or, UInt32.toNat_sub, toNat_lit0,
    toNat_lit1, show (31 : UInt32).toNat % 32 = 31 from by decide,
    show (2 ^ 32 - y.toNat + 0) % 2 ^ 32 = 2 ^ 32 - y.toNat from Nat.mod_eq_of_lt (by omega),
    Nat.shiftRight_or_distrib, Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow]
  rcases Nat.lt_or_ge y.toNat (2 ^ 31) with h | h
  · rw [show y.toNat / 2 ^ 31 = 0 from by omega,
      show (2 ^ 32 - y.toNat) / 2 ^ 31 = 1 from by omega]
    decide
  · rw [show y.toNat / 2 ^ 31 = 1 from by omega]
    rcases Nat.lt_or_ge (2 ^ 32 - y.toNat) (2 ^ 31) with h2 | h2
    · rw [show (2 ^ 32 - y.toNat) / 2 ^ 31 = 0 from by omega]; decide
    · rw [show (2 ^ 32 - y.toNat) / 2 ^ 31 = 1 from by omega]; decide

/-- When the high half is nonzero, `FPR.lzcnt64_nonzero` selects it and adds no offset: its
conditional mask `m` collapses to `0`. -/
private theorem lzcnt64_nonzero_eq_high (x : UInt64) (h : (x >>> 32).toUInt32 ≠ 0) :
    lzcnt64_nonzero x = lzcnt_nonzero (x >>> 32).toUInt32 := by
  have hm : ~~~(tbmask ((x >>> 32).toUInt32 ||| ((0 : UInt32) - (x >>> 32).toUInt32))) = 0 := by
    unfold tbmask
    rw [or_neg_shiftRight_31 _ h]
    decide
  simp only [lzcnt64_nonzero, hm]
  simp

/-- When the high half is zero, `FPR.lzcnt64_nonzero` counts in the low half and adds `32`: its
conditional mask `m` collapses to all-ones. -/
private theorem lzcnt64_nonzero_eq_low (x : UInt64) (h : (x >>> 32).toUInt32 = 0) :
    lzcnt64_nonzero x = lzcnt_nonzero x.toUInt32 + 32 := by
  have hm : ~~~(tbmask ((x >>> 32).toUInt32 ||| ((0 : UInt32) - (x >>> 32).toUInt32)))
      = 4294967295 := by
    rw [h]; unfold tbmask; decide
  have hand : x.toUInt32 &&& 4294967295 = x.toUInt32 := by
    rw [← UInt32.toNat_inj, UInt32.toNat_and,
      show (4294967295 : UInt32).toNat = 2 ^ 32 - 1 from by decide,
      Nat.and_two_pow_sub_one_eq_mod]
    exact Nat.mod_eq_of_lt (UInt32.toNat_lt x.toUInt32)
  simp only [lzcnt64_nonzero, hm, hand,
    show ((4294967295 : UInt32) &&& 32) = 32 from by decide]
  rw [h, UInt32.zero_or]

/-- `FPR.lzcnt64_nonzero` never returns more than `63`. -/
private theorem lzcnt64_nonzero_toNat_le (x : UInt64) : (lzcnt64_nonzero x).toNat ≤ 63 := by
  have h32 : (32 : UInt32).toNat = 32 := by decide
  by_cases h : (x >>> 32).toUInt32 = 0
  · rw [lzcnt64_nonzero_eq_low x h, UInt32.toNat_add, h32]
    have := lzcnt_nonzero_toNat_le x.toUInt32
    omega
  · rw [lzcnt64_nonzero_eq_high x h]
    exact le_trans (lzcnt_nonzero_toNat_le _) (by norm_num)

/-- `FPR.lzcnt64_nonzero x` is the number of leading zero bits of a nonzero 64-bit word `x`:
`2 ^ (63 - c) ≤ x < 2 ^ (64 - c)`. Both halves of the `UInt32`/`UInt64` dispatch reduce to
`lzcnt_nonzero_spec` on the selected half. -/
private theorem lzcnt64_nonzero_spec (x : UInt64) (hx : x ≠ 0) :
    2 ^ (63 - (lzcnt64_nonzero x).toNat) ≤ x.toNat ∧
      x.toNat < 2 ^ (64 - (lzcnt64_nonzero x).toNat) := by
  have hxN : x.toNat ≠ 0 := fun h0 => hx (UInt64.toNat_inj.mp (by simpa using h0))
  have hhi := toUInt32_shiftRight32_toNat x
  have h32 : (32 : UInt32).toNat = 32 := by decide
  by_cases h : (x >>> 32).toUInt32 = 0
  · have hdiv : x.toNat / 2 ^ 32 = 0 := by rw [← hhi, h]; decide
    have hlt32 : x.toNat < 2 ^ 32 :=
      (Nat.div_eq_zero_iff.mp hdiv).resolve_left (by norm_num)
    have hlow : x.toUInt32.toNat = x.toNat := by
      rw [UInt64.toNat_toUInt32]; exact Nat.mod_eq_of_lt hlt32
    have hne : x.toUInt32 ≠ 0 := by
      intro h0
      rw [h0] at hlow
      exact hxN (by simpa using hlow.symm)
    obtain ⟨hl, hh⟩ := lzcnt_nonzero_spec x.toUInt32 hne
    rw [hlow] at hl hh
    have hc := lzcnt_nonzero_toNat_le x.toUInt32
    rw [lzcnt64_nonzero_eq_low x h, UInt32.toNat_add, h32,
      Nat.mod_eq_of_lt (show (lzcnt_nonzero x.toUInt32).toNat + 32 < 2 ^ 32 from by omega),
      show 63 - ((lzcnt_nonzero x.toUInt32).toNat + 32)
        = 31 - (lzcnt_nonzero x.toUInt32).toNat from by omega,
      show 64 - ((lzcnt_nonzero x.toUInt32).toNat + 32)
        = 32 - (lzcnt_nonzero x.toUInt32).toNat from by omega]
    exact ⟨hl, hh⟩
  · rw [lzcnt64_nonzero_eq_high x h]
    have hc := lzcnt_nonzero_toNat_le (x >>> 32).toUInt32
    obtain ⟨hl, hh⟩ := lzcnt_nonzero_spec (x >>> 32).toUInt32 h
    rw [hhi] at hl hh
    have hdm : x.toNat / 2 ^ 32 * 2 ^ 32 + x.toNat % 2 ^ 32 = x.toNat := by
      rw [Nat.mul_comm]; exact Nat.div_add_mod _ _
    have hmodlt : x.toNat % 2 ^ 32 < 2 ^ 32 := Nat.mod_lt _ (by norm_num)
    have p1 : 2 ^ (31 - (lzcnt_nonzero (x >>> 32).toUInt32).toNat) * 2 ^ 32
        = 2 ^ (63 - (lzcnt_nonzero (x >>> 32).toUInt32).toNat) := by
      rw [← pow_add]; congr 1; omega
    have p2 : 2 ^ (32 - (lzcnt_nonzero (x >>> 32).toUInt32).toNat) * 2 ^ 32
        = 2 ^ (64 - (lzcnt_nonzero (x >>> 32).toUInt32).toNat) := by
      rw [← pow_add]; congr 1; omega
    omega

/-- The bracket of `lzcnt64_nonzero_spec` pins the count down: `FPR.lzcnt64_nonzero x` is the
*unique* `c` with `2 ^ (63 - c) ≤ x < 2 ^ (64 - c)`. No explicit `c ≤ 63` hypothesis is needed:
for `c ≥ 64` the two `Nat`-truncated exponents `63 - c` and `64 - c` both collapse to `0`, so the
hypotheses would demand `1 ≤ x.toNat < 1`, which is unsatisfiable. -/
private theorem lzcnt64_nonzero_unique (x : UInt64) (c : ℕ)
    (h1 : 2 ^ (63 - c) ≤ x.toNat) (h2 : x.toNat < 2 ^ (64 - c)) :
    (lzcnt64_nonzero x).toNat = c := by
  by_cases hc : c ≤ 63
  · have hx : x ≠ 0 := by
      intro h0
      rw [h0] at h1
      simp only [show (0 : UInt64).toNat = 0 from by decide] at h1
      exact absurd h1 (by simp)
    have hd := lzcnt64_nonzero_toNat_le x
    obtain ⟨hl, hh⟩ := lzcnt64_nonzero_spec x hx
    by_contra hne
    rcases Nat.lt_or_ge (lzcnt64_nonzero x).toNat c with hlt | hge
    · have : (2 : ℕ) ^ (64 - c) ≤ 2 ^ (63 - (lzcnt64_nonzero x).toNat) :=
        Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    · have : (2 : ℕ) ^ (64 - (lzcnt64_nonzero x).toNat) ≤ 2 ^ (63 - c) :=
        Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
  · exfalso
    have h63 : 63 - c = 0 := by omega
    have h64 : 64 - c = 0 := by omega
    rw [h63] at h1
    rw [h64] at h2
    omega

/-! ### The `||| 1` guard and the normalising shift

`FPR.norm64` — and its inlined copies in `FPR.scaled` and `FPR.add` — call
`lzcnt64_nonzero (m ||| 1)` rather than `lzcnt64_nonzero m`, so that the count is defined even for
`m = 0`. For nonzero `m` the guard is invisible: setting the low bit cannot change which power of
two brackets the value. -/

/-- The `||| 1` guard makes the argument of the leading-zero count unconditionally nonzero. -/
private theorem or_one_ne_zero (m : UInt64) : m ||| 1 ≠ 0 := by
  intro h
  have h1 : (1 : UInt64) ≤ m ||| 1 := UInt64.right_le_or
  rw [h] at h1
  exact absurd h1 (by decide)

/-- The `||| 1` guard never decreases the value. -/
private theorem le_or_one_toNat (m : UInt64) : m.toNat ≤ (m ||| 1).toNat :=
  UInt64.le_iff_toNat_le.mp UInt64.left_le_or

/-- The `||| 1` guard is invisible above bit `0`. -/
private theorem or_one_shiftRight_one (m : UInt64) : (m ||| 1) >>> 1 = m >>> 1 := by
  rw [UInt64.shiftRight_or, show ((1 : UInt64) >>> 1) = 0 from by decide, UInt64.or_zero]

/-- Setting the low bit cannot push a nonzero word across a power-of-two boundary from below:
`m ||| 1` and `m` have the same leading power of two. -/
private theorem two_pow_le_of_or_one {m : UInt64} {k : ℕ} (hm : m ≠ 0)
    (h : 2 ^ k ≤ (m ||| 1).toNat) : 2 ^ k ≤ m.toNat := by
  have hmN : m.toNat ≠ 0 := fun h0 => hm (UInt64.toNat_inj.mp (by simpa using h0))
  match k with
  | 0 => simpa using Nat.one_le_iff_ne_zero.mpr hmN
  | (j + 1) =>
    have hdiv : (m ||| 1).toNat / 2 = m.toNat / 2 := by
      have hs := congrArg UInt64.toNat (or_one_shiftRight_one m)
      rw [UInt64.toNat_shiftRight, UInt64.toNat_shiftRight] at hs
      simpa [Nat.shiftRight_eq_div_pow] using hs
    have h1 : 2 ^ (j + 1) / 2 ≤ (m ||| 1).toNat / 2 := Nat.div_le_div_right h
    rw [hdiv, pow_succ] at h1
    have h4 : m.toNat / 2 * 2 ≤ m.toNat := Nat.div_mul_le_self _ _
    have hp : (2 : ℕ) ^ (j + 1) = 2 ^ j * 2 := pow_succ 2 j
    omega

/-- The guarded count `lzcnt64_nonzero (m ||| 1)` used by `FPR.norm64`, `FPR.scaled` and `FPR.add`
brackets `m` itself whenever `m` is nonzero. -/
private theorem lzcnt64_nonzero_or_one_spec (m : UInt64) (hm : m ≠ 0) :
    2 ^ (63 - (lzcnt64_nonzero (m ||| 1)).toNat) ≤ m.toNat ∧
      m.toNat < 2 ^ (64 - (lzcnt64_nonzero (m ||| 1)).toNat) := by
  obtain ⟨hl, hh⟩ := lzcnt64_nonzero_spec (m ||| 1) (or_one_ne_zero m)
  exact ⟨two_pow_le_of_or_one hm hl, lt_of_le_of_lt (le_or_one_toNat m) hh⟩

/-- `FPR.fpr_ulsh` is a left shift by a sub-word amount, i.e. multiplication by a power of two
modulo `2 ^ 64`. -/
private theorem toNat_fpr_ulsh (m : UInt64) (c : UInt32) (hc : c.toNat < 64) :
    (fpr_ulsh m c).toNat = m.toNat * 2 ^ c.toNat % 2 ^ 64 := by
  unfold fpr_ulsh
  rw [UInt64.toNat_shiftLeft, UInt32.toNat_toUInt64, Nat.mod_eq_of_lt hc, Nat.shiftLeft_eq]

/-- The normalising shift loses no bits: for nonzero `m`, `fpr_ulsh m (lzcnt64_nonzero (m ||| 1))`
is exactly `m * 2 ^ c`, with no wraparound. This is the "value-preserving in the
significand/exponent pair" half of the renormalisation step. -/
private theorem fpr_ulsh_lzcnt64_toNat (m : UInt64) (hm : m ≠ 0) :
    (fpr_ulsh m (lzcnt64_nonzero (m ||| 1))).toNat
      = m.toNat * 2 ^ (lzcnt64_nonzero (m ||| 1)).toNat := by
  have hc := lzcnt64_nonzero_toNat_le (m ||| 1)
  obtain ⟨hl, hh⟩ := lzcnt64_nonzero_or_one_spec m hm
  rw [toNat_fpr_ulsh m _ (by omega)]
  apply Nat.mod_eq_of_lt
  have hpos : 0 < 2 ^ (lzcnt64_nonzero (m ||| 1)).toNat := Nat.two_pow_pos _
  have hkey := mul_lt_mul_of_pos_right hh hpos
  rwa [← pow_add, show 64 - (lzcnt64_nonzero (m ||| 1)).toNat
      + (lzcnt64_nonzero (m ||| 1)).toNat = 64 from by omega] at hkey

/-- The normalising shift left-aligns: for nonzero `m`, the shifted significand
`fpr_ulsh m (lzcnt64_nonzero (m ||| 1))` has its top (bit 63) set. -/
private theorem fpr_ulsh_lzcnt64_top_bit (m : UInt64) (hm : m ≠ 0) :
    2 ^ 63 ≤ (fpr_ulsh m (lzcnt64_nonzero (m ||| 1))).toNat := by
  have hc := lzcnt64_nonzero_toNat_le (m ||| 1)
  obtain ⟨hl, hh⟩ := lzcnt64_nonzero_or_one_spec m hm
  rw [fpr_ulsh_lzcnt64_toNat m hm]
  have hkey := Nat.mul_le_mul hl (Nat.le_refl (2 ^ (lzcnt64_nonzero (m ||| 1)).toNat))
  rwa [← pow_add, show 63 - (lzcnt64_nonzero (m ||| 1)).toNat
      + (lzcnt64_nonzero (m ||| 1)).toNat = 63 from by omega] at hkey

/-! ### The `FPR.add` / `FPR.scaled` exponent decrement

`FPR.add`'s `ex'' := ex' - c_add.toInt32` (with `c_add := lzcnt64_nonzero (zu ||| 1)`) and
`FPR.scaled`'s `sc' := sc - c_sc.toInt32` (with `c_sc := lzcnt64_nonzero (m ||| 1)`) both inline
this same exponent decrement rather than routing through `FPR.norm64`; the lemma below is stated
directly in that inlined shape. -/

/-- Reinterpreting a small `UInt32` as an `Int32` preserves its value. -/
private theorem toInt_toInt32_of_lt {y : UInt32} (hy : y.toNat < 2 ^ 31) :
    y.toInt32.toInt = (y.toNat : ℤ) := by
  unfold Int32.toInt
  rw [UInt32.toBitVec_toInt32,
    BitVec.toInt_eq_toNat_of_lt (by simp only [UInt32.toNat_toBitVec]; omega),
    UInt32.toNat_toBitVec]

/-- The exponent decrement `e - (lzcnt64_nonzero (m ||| 1)).toInt32` computed by `FPR.add` and
`FPR.scaled` is exactly the shift amount subtracted as an integer, with no `Int32` wraparound. The
hypothesis rules out underflow, which cannot occur for the exponents `FPR.scaled` / `FPR.add`
actually pass (they live near `±1100`, while the bound only excludes `e < -2 ^ 31 + 63`). -/
private theorem toInt_sub_lzcnt64_nonzero_or_one_toInt32 (m : UInt64) (e : Int32)
    (hnf : -(2 ^ 31 : ℤ) ≤ e.toInt - ((lzcnt64_nonzero (m ||| 1)).toNat : ℤ)) :
    (e - (lzcnt64_nonzero (m ||| 1)).toInt32).toInt
      = e.toInt - ((lzcnt64_nonzero (m ||| 1)).toNat : ℤ) := by
  have hc := lzcnt64_nonzero_toNat_le (m ||| 1)
  rw [Int32.toInt_sub, toInt_toInt32_of_lt (by omega)]
  refine Int.bmod_eq_of_le_mul_two ?_ ?_
  · have h := Int32.le_toInt e
    push_cast
    omega
  · have h := Int32.toInt_lt e
    push_cast
    omega

/-! ### Round-to-nearest, ties-to-even on `ℕ`

Both `FPR.make` and `FPR.make_z` finish by discarding the low two bits of a working significand
`m` and adding a correction bit read out of the constant table `0xC8`:

```
cc := ((0xC8 : UInt64) >>> (m.toUInt32 &&& 7).toUInt64) &&& 1
...  + (m >>> 2) + cc
```

The three low bits of `m` are (kept LSB, round bit, sticky bit), and `0xC8 = 0b11001000` has bits
`3`, `6`, `7` set, so `cc = 1` exactly for `m &&& 7 ∈ {3, 6, 7}`. -/

/-- Round `n / 4` to the nearest natural number, breaking exact ties (`n % 4 = 2`) toward
the even quotient. This is IEEE-754's default rounding direction specialized to a two-bit
discard: `n % 4` is the pair (round bit, sticky bit) and `n / 4 % 2` is the kept LSB. -/
def roundQuarterTiesEven (n : ℕ) : ℕ :=
  n / 4 + (if 2 < n % 4 ∨ (n % 4 = 2 ∧ n / 4 % 2 = 1) then 1 else 0)

/-- `roundQuarterTiesEven n` is a nearest integer to `n / 4`: scaled back up by `4` it is
within `2` of `n` from above. -/
theorem four_mul_roundQuarterTiesEven_le (n : ℕ) :
    4 * roundQuarterTiesEven n ≤ n + 2 := by
  unfold roundQuarterTiesEven; split_ifs <;> omega

/-- `roundQuarterTiesEven n` is a nearest integer to `n / 4`: scaled back up by `4` it is
within `2` of `n` from below. -/
theorem le_four_mul_roundQuarterTiesEven (n : ℕ) :
    n ≤ 4 * roundQuarterTiesEven n + 2 := by
  unfold roundQuarterTiesEven; split_ifs <;> omega

/-- Ties (the two cases in which `roundQuarterTiesEven n` is at distance exactly `2/4` from
`n / 4`) are resolved toward an even quotient. -/
theorem roundQuarterTiesEven_even_of_tie (n : ℕ)
    (h : 4 * roundQuarterTiesEven n = n + 2 ∨ n = 4 * roundQuarterTiesEven n + 2) :
    roundQuarterTiesEven n % 2 = 0 := by
  revert h; unfold roundQuarterTiesEven; split_ifs <;> omega

/-- The nearest-with-ties-to-even conditions pin the result uniquely, so any `q` satisfying
them is `roundQuarterTiesEven n`. This is the characterization to use when identifying the
table output with a rounding operator stated some other way. -/
theorem eq_roundQuarterTiesEven (n q : ℕ) (h1 : n ≤ 4 * q + 2) (h2 : 4 * q ≤ n + 2)
    (h3 : 4 * q = n + 2 ∨ n = 4 * q + 2 → q % 2 = 0) :
    q = roundQuarterTiesEven n := by
  by_cases ht : 4 * q = n + 2 ∨ n = 4 * q + 2
  · have hq := h3 ht
    unfold roundQuarterTiesEven; split_ifs <;> omega
  · have ht1 : 4 * q ≠ n + 2 := fun h => ht (Or.inl h)
    have ht2 : n ≠ 4 * q + 2 := fun h => ht (Or.inr h)
    unfold roundQuarterTiesEven; split_ifs <;> omega

/-- Rounding never moves the quotient down. -/
theorem div_four_le_roundQuarterTiesEven (n : ℕ) : n / 4 ≤ roundQuarterTiesEven n := by
  unfold roundQuarterTiesEven; split_ifs <;> omega

/-- Rounding moves the quotient up by at most one. -/
theorem roundQuarterTiesEven_le_div_four_succ (n : ℕ) :
    roundQuarterTiesEven n ≤ n / 4 + 1 := by
  unfold roundQuarterTiesEven; split_ifs <;> omega

/-- Rounding is exact when the two discarded bits are zero. -/
theorem roundQuarterTiesEven_of_mod_four_eq_zero (n : ℕ) (h : n % 4 = 0) :
    roundQuarterTiesEven n = n / 4 := by
  unfold roundQuarterTiesEven; split_ifs <;> omega

/-- A normalized 55-bit working significand rounds to a 53-bit significand, possibly
carrying out to the round power `2 ^ 53` (the case that bumps the exponent field). -/
theorem roundQuarterTiesEven_mem_of_normalized (n : ℕ) (h1 : 2 ^ 54 ≤ n) (h2 : n < 2 ^ 55) :
    2 ^ 52 ≤ roundQuarterTiesEven n ∧ roundQuarterTiesEven n ≤ 2 ^ 53 := by
  refine ⟨le_trans ?_ (div_four_le_roundQuarterTiesEven n),
    le_trans (roundQuarterTiesEven_le_div_four_succ n) ?_⟩ <;> omega

/-- The real-number content of the two nearest-integer bounds: rounding `n / 4` moves it by
at most half a unit. -/
theorem abs_roundQuarterTiesEven_sub_div_four_le (n : ℕ) :
    |(roundQuarterTiesEven n : ℝ) - (n : ℝ) / 4| ≤ 1 / 2 := by
  have h1 := four_mul_roundQuarterTiesEven_le n
  have h2 := le_four_mul_roundQuarterTiesEven n
  have h1' : (4 : ℝ) * (roundQuarterTiesEven n : ℝ) ≤ (n : ℝ) + 2 := by exact_mod_cast h1
  have h2' : (n : ℝ) ≤ 4 * (roundQuarterTiesEven n : ℝ) + 2 := by exact_mod_cast h2
  rw [abs_le]
  constructor <;> linarith

/-! ### The `0xC8` rounding-table lookup -/

/-- The `0xC8` rounding-table lookup used by `FPR.make` and `FPR.make_z`: the low three bits
of the working significand `m` index the constant `0xC8 = 0b11001000`. -/
def roundTableBit (m : UInt64) : UInt64 :=
  ((0xC8 : UInt64) >>> (m.toUInt32 &&& 7).toUInt64) &&& 1

private theorem nat_and_seven (x : ℕ) : x &&& 7 = x % 8 := by
  simpa using Nat.and_two_pow_sub_one_eq_mod x 3

/-- The table index `(m.toUInt32 &&& 7).toUInt64` is exactly the low three bits of `m`,
the truncation to `UInt32` notwithstanding. -/
theorem toNat_tableIndex (m : UInt64) : (m.toUInt32 &&& 7).toUInt64.toNat = m.toNat % 8 := by
  rw [UInt32.toNat_toUInt64]
  simp only [UInt32.toNat_and, UInt64.toNat_toUInt32, UInt32.reduceToNat]
  rw [nat_and_seven]
  exact Nat.mod_mod_of_dvd _ (by norm_num)

/-- The eight-entry rounding table, read off `0xC8 = 0b11001000`: the correction bit is `1`
exactly on the low-three-bit patterns `3`, `6`, `7`. -/
theorem toNat_roundTableBit_eq_ite_mod_eight (m : UInt64) :
    (roundTableBit m).toNat =
      if m.toNat % 8 = 3 ∨ m.toNat % 8 = 6 ∨ m.toNat % 8 = 7 then 1 else 0 := by
  rw [roundTableBit, UInt64.toNat_and, UInt64.toNat_shiftRight, toNat_tableIndex,
    Nat.mod_eq_of_lt (by omega : m.toNat % 8 < 64)]
  have h8 : m.toNat % 8 < 8 := Nat.mod_lt _ (by norm_num)
  generalize m.toNat % 8 = k at h8 ⊢
  interval_cases k <;> decide

/-- The rounding table restated in IEEE terms: the correction bit is `1` exactly when the
discarded two bits `m % 4` exceed a half, or form an exact half whose kept LSB is odd. -/
theorem toNat_roundTableBit (m : UInt64) :
    (roundTableBit m).toNat =
      if 2 < m.toNat % 4 ∨ (m.toNat % 4 = 2 ∧ m.toNat / 4 % 2 = 1) then 1 else 0 := by
  rw [toNat_roundTableBit_eq_ite_mod_eight]
  split_ifs <;> omega

/-- The correction bit is a bit. -/
theorem toNat_roundTableBit_le_one (m : UInt64) : (roundTableBit m).toNat ≤ 1 := by
  rw [toNat_roundTableBit]; split_ifs <;> omega

/-- The rounding table as a `UInt64`-level case split. -/
theorem roundTableBit_eq_ite (m : UInt64) :
    roundTableBit m =
      if m.toNat % 8 = 3 ∨ m.toNat % 8 = 6 ∨ m.toNat % 8 = 7 then 1 else 0 := by
  apply UInt64.toNat_inj.mp
  rw [toNat_roundTableBit_eq_ite_mod_eight]
  split_ifs <;> rfl

private theorem toNat_shiftRight_two (m : UInt64) : (m >>> 2).toNat = m.toNat / 4 := by
  have h2 : (2 : UInt64).toNat = 2 := rfl
  rw [UInt64.toNat_shiftRight, h2]
  norm_num [Nat.shiftRight_eq_div_pow]

/-- The `0xC8` rounding table implements round-to-nearest, ties-to-even: discarding the
low two bits of the working significand `m` and adding the table bit yields exactly the
nearest integer to `m / 4`, with exact halves resolved toward an even result. -/
theorem toNat_shiftRight_two_add_roundTableBit (m : UInt64) :
    ((m >>> 2) + roundTableBit m).toNat = roundQuarterTiesEven m.toNat := by
  have hm : m.toNat < 2 ^ 64 := m.toNat_lt_size
  rw [UInt64.toNat_add, toNat_shiftRight_two, toNat_roundTableBit]
  unfold roundQuarterTiesEven
  split_ifs <;> omega

/-- The rounded significand of a `UInt64` never overflows into the exponent field's carry
region: it is at most `2 ^ 62`. -/
theorem roundQuarterTiesEven_toNat_le (m : UInt64) : roundQuarterTiesEven m.toNat ≤ 2 ^ 62 := by
  have hm : m.toNat < 2 ^ 64 := m.toNat_lt_size
  have := roundQuarterTiesEven_le_div_four_succ m.toNat
  omega

/-- Injecting the rounded significand back into `UInt64` is faithful. -/
theorem toNat_ofNat_roundQuarterTiesEven (m : UInt64) :
    (UInt64.ofNat (roundQuarterTiesEven m.toNat)).toNat = roundQuarterTiesEven m.toNat := by
  have := roundQuarterTiesEven_toNat_le m
  rw [UInt64.toNat_ofNat']
  exact Nat.mod_eq_of_lt (by omega)

/-- The `UInt64`-level form: `(m >>> 2) + cc` is the injection of the rounded quotient. -/
theorem shiftRight_two_add_roundTableBit (m : UInt64) :
    (m >>> 2) + roundTableBit m = UInt64.ofNat (roundQuarterTiesEven m.toNat) := by
  apply UInt64.toNat_inj.mp
  rw [toNat_shiftRight_two_add_roundTableBit, toNat_ofNat_roundQuarterTiesEven]

/-! ### The final assembly `FPR.make` / `FPR.make_z`

The three fields are combined with **plain `UInt64` addition**, not with `|||`. The summand
`(m >>> 2) + cc` lies in `[2 ^ 52, 2 ^ 53]`, i.e. it is the *full* significand including the
implicit leading bit, so its top bit always carries into the exponent slot: the stored exponent
field is `e + 1077`, not `e + 1076`. When round-to-nearest pushes the significand all the way to
`2 ^ 53` the same carry fires a second time, incrementing the exponent field once more and leaving
a zero mantissa — exactly "increment the exponent and halve the significand". `toRealBits_make`
states both cases uniformly.

Every field-range side condition is an explicit hypothesis: `s.toNat ≤ 1`,
`2 ^ 54 ≤ m.toNat < 2 ^ 55` (the normalized-significand invariant a caller establishes with
`fpr_ulsh_lzcnt64_top_bit`), and an interval on `e.toInt` keeping the packed exponent field
strictly between the subnormal marker `0` and the Inf/NaN marker `2047`. -/

/-- `FPR.make` in terms of the rounding-table bit, verbatim in the shape of the kernel's body. -/
private theorem make_eq_add_roundTableBit (s : UInt64) (e : Int32) (m : UInt64) :
    make s e m =
      s <<< 63 + (e + 1076).toUInt32.toUInt64 <<< 52 + (m >>> 2) + roundTableBit m := rfl

/-- `FPR.make_z` in terms of the rounding-table bit, verbatim in the shape of the kernel's
body. -/
private theorem make_z_eq_add_roundTableBit (s : UInt64) (e : Int32) (m : UInt64) :
    make_z s e m =
      s <<< 63 + ((e + 1076).toUInt32 &&& ((0 : UInt32) - (m >>> 54).toUInt32)).toUInt64 <<< 52
        + (m >>> 2) + roundTableBit m := rfl

/-- `FPR.make` assembles the sign and exponent fields and adds the round-to-nearest,
ties-to-even rounding of `m / 4`. -/
private theorem make_eq_roundQuarterTiesEven (s : UInt64) (e : Int32) (m : UInt64) :
    make s e m =
      s <<< 63 + (e + 1076).toUInt32.toUInt64 <<< 52
        + UInt64.ofNat (roundQuarterTiesEven m.toNat) := by
  rw [make_eq_add_roundTableBit, UInt64.add_assoc, shiftRight_two_add_roundTableBit]

/-- `FPR.make_z` assembles the sign and (zero-collapsing) exponent fields and adds the
round-to-nearest, ties-to-even rounding of `m / 4`. -/
private theorem make_z_eq_roundQuarterTiesEven (s : UInt64) (e : Int32) (m : UInt64) :
    make_z s e m =
      s <<< 63 + ((e + 1076).toUInt32 &&& ((0 : UInt32) - (m >>> 54).toUInt32)).toUInt64 <<< 52
        + UInt64.ofNat (roundQuarterTiesEven m.toNat) := by
  rw [make_z_eq_add_roundTableBit, UInt64.add_assoc, shiftRight_two_add_roundTableBit]

/-- The exponent word `(e + 1076).toUInt32.toUInt64` computes the biased exponent `e + 1076` on
the nose, provided no `Int32` wraparound can occur. The stated interval is the one under which
`FPR.make`'s packed exponent field stays inside the finite range. -/
theorem FPR.toNat_biasedExponentWord (e : Int32) (h1 : -1076 ≤ e.toInt) (h2 : e.toInt ≤ 969) :
    (e + 1076).toUInt32.toUInt64.toNat = (e.toInt + 1076).toNat := by
  have h1076 : (1076 : Int32).toInt = 1076 := by decide
  have hadd : (e + 1076).toInt = e.toInt + 1076 := by
    rw [Int32.toInt_add, h1076, Int.bmod_eq_emod_of_lt (by omega)]
    omega
  have hnn : (0 : Int32) ≤ e + 1076 := by
    rw [Int32.le_iff_toInt_le, hadd, show (0 : Int32).toInt = 0 from by decide]
    omega
  rw [UInt32.toNat_toUInt64, Int32.toNat_toUInt32_of_le hnn, ← Int32.toNat_toInt, hadd]

/-- The word `FPR.make` builds, as a natural number: the three field contributions are simply
*added*, with no wraparound anywhere. The hypotheses are exactly what rules the wraparound out —
a single sign bit, an exponent word below `2046`, and a significand `m` below `2 ^ 55` (so
`m >>> 2 < 2 ^ 53`). Note that the significand contribution is *not* pre-masked into the low 52
bits: it exceeds `2 ^ 52`, and the excess carries into the exponent field. -/
private theorem FPR.toNat_make (s : UInt64) (e : Int32) (m : UInt64)
    (hs : s.toNat ≤ 1) (he1 : -1076 ≤ e.toInt) (he2 : e.toInt ≤ 969)
    (hm : m.toNat < 2 ^ 55) :
    (make s e m).toNat =
      s.toNat * 2 ^ 63 + (e.toInt + 1076).toNat * 2 ^ 52 + roundQuarterTiesEven m.toNat := by
  have hA : (s <<< 63 : UInt64).toNat = s.toNat * 2 ^ 63 := by
    rw [UInt64.toNat_shiftLeft]
    simp only [UInt64.reduceToNat, Nat.reduceMod, Nat.shiftLeft_eq, Nat.reducePow]
    omega
  have hE : (e + 1076).toUInt32.toUInt64.toNat = (e.toInt + 1076).toNat :=
    FPR.toNat_biasedExponentWord e he1 he2
  have hEle : (e.toInt + 1076).toNat ≤ 2045 := by omega
  have hB : ((e + 1076).toUInt32.toUInt64 <<< 52 : UInt64).toNat =
      (e.toInt + 1076).toNat * 2 ^ 52 := by
    rw [UInt64.toNat_shiftLeft]
    simp only [UInt64.reduceToNat, Nat.reduceMod, Nat.shiftLeft_eq, Nat.reducePow, hE]
    omega
  have hR : roundQuarterTiesEven m.toNat ≤ 2 ^ 53 := by
    have := roundQuarterTiesEven_le_div_four_succ m.toNat
    omega
  rw [make_eq_roundQuarterTiesEven, UInt64.toNat_add, UInt64.toNat_add, hA, hB,
    toNat_ofNat_roundQuarterTiesEven]
  omega

/-- Decode round-trip for `FPR.make`, ordinary case: the rounded significand stays below `2 ^ 53`.
The sign bit is returned unchanged, the mantissa field is the significand with its implicit leading
bit stripped, and the exponent field is `e + 1077` — one more than the word `(e + 1076)` that was
shifted into place, because the significand's leading bit carried into it. -/
private theorem FPR.decode_make_of_no_carry (s : UInt64) (e : Int32) (m : UInt64)
    (hs : s.toNat ≤ 1) (he1 : -1076 ≤ e.toInt) (he2 : e.toInt ≤ 969)
    (hm1 : 2 ^ 54 ≤ m.toNat) (hm2 : m.toNat < 2 ^ 55)
    (hnc : roundQuarterTiesEven m.toNat < 2 ^ 53) :
    FPR.decode (make s e m) =
      { sign := decide (s.toNat = 1),
        exponent := (e.toInt + 1076).toNat + 1,
        mantissa := roundQuarterTiesEven m.toNat - 2 ^ 52 } := by
  have hb := (roundQuarterTiesEven_mem_of_normalized m.toNat hm1 hm2).1
  have hE : (e.toInt + 1076).toNat ≤ 2045 := by omega
  unfold FPR.decode
  rw [FPR.toNat_make s e m hs he1 he2 hm2]
  simp only [Nat.testBit_eq_decide_div_mod_eq, Nat.shiftRight_eq_div_pow, FPR.Bits.mk.injEq,
    decide_eq_decide]
  refine ⟨?_, ?_, ?_⟩ <;> omega

/-- Decode round-trip for `FPR.make`, rounding-carry case: rounding pushed the significand to
`2 ^ 53`, one bit too wide for the mantissa field. Because the fields are combined with plain
addition, the overflow carries into the exponent slot all by itself, producing exponent field
`e + 1078` (one more than the ordinary `e + 1077`) and mantissa `0`. That is precisely "increment
the exponent and halve the significand", so no explicit renormalization step is needed. -/
private theorem FPR.decode_make_of_carry (s : UInt64) (e : Int32) (m : UInt64)
    (hs : s.toNat ≤ 1) (he1 : -1076 ≤ e.toInt) (he2 : e.toInt ≤ 969)
    (hm2 : m.toNat < 2 ^ 55)
    (hc : roundQuarterTiesEven m.toNat = 2 ^ 53) :
    FPR.decode (make s e m) =
      { sign := decide (s.toNat = 1),
        exponent := (e.toInt + 1076).toNat + 2,
        mantissa := 0 } := by
  have hE : (e.toInt + 1076).toNat ≤ 2045 := by omega
  unfold FPR.decode
  rw [FPR.toNat_make s e m hs he1 he2 hm2]
  simp only [Nat.testBit_eq_decide_div_mod_eq, Nat.shiftRight_eq_div_pow, FPR.Bits.mk.injEq,
    decide_eq_decide]
  refine ⟨?_, ?_, ?_⟩ <;> omega

/-- Denotation of `FPR.make`, stated uniformly across the rounding carry: the word always denotes
`± roundQuarterTiesEven m * 2 ^ (e + 2)`, whether or not the significand carried out of the
mantissa field. In the carry case the exponent field is one larger and the mantissa is zero, and
the two changes cancel exactly — this is the statement that the self-normalizing carry does the
right thing. The hypothesis `e.toInt ≤ 968` keeps the exponent field below the Inf/NaN marker
`2047` even after the carry, and `-1076 ≤ e.toInt` keeps it above the subnormal marker `0`. -/
private theorem toRealBits_make (s : UInt64) (e : Int32) (m : UInt64)
    (hs : s.toNat ≤ 1) (he1 : -1076 ≤ e.toInt) (he2 : e.toInt ≤ 968)
    (hm1 : 2 ^ 54 ≤ m.toNat) (hm2 : m.toNat < 2 ^ 55) :
    toRealBits (make s e m) =
      (if s.toNat = 1 then (-1 : ℝ) else 1) * (roundQuarterTiesEven m.toNat : ℝ) *
        (2 : ℝ) ^ (e.toInt + 2) := by
  obtain ⟨hlo, hhi⟩ := roundQuarterTiesEven_mem_of_normalized m.toNat hm1 hm2
  have hE : ((e.toInt + 1076).toNat : ℤ) = e.toInt + 1076 := Int.toNat_of_nonneg (by omega)
  have hEle : (e.toInt + 1076).toNat ≤ 2044 := by omega
  rcases lt_or_eq_of_le hhi with hcase | hcase
  · rw [toRealBits, FPR.decode_make_of_no_carry s e m hs he1 (by omega) hm1 hm2 hcase]
    unfold FPR.Bits.toReal
    simp only [decide_eq_true_eq]
    rw [if_neg (by omega : ¬ (e.toInt + 1076).toNat + 1 = 0),
      if_neg (by omega : ¬ (e.toInt + 1076).toNat + 1 = 2047)]
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
  · rw [toRealBits, FPR.decode_make_of_carry s e m hs he1 (by omega) hm2 hcase]
    unfold FPR.Bits.toReal
    simp only [decide_eq_true_eq]
    rw [if_neg (by omega : ¬ (e.toInt + 1076).toNat + 2 = 0),
      if_neg (by omega : ¬ (e.toInt + 1076).toNat + 2 = 2047)]
    have hexp : (((e.toInt + 1076).toNat + 2 : ℕ) : ℤ) - 1023 = e.toInt + 55 := by
      push_cast [hE]; ring
    rw [hexp, hcase]
    push_cast
    rw [show (2 : ℝ) ^ (e.toInt + 55) = (2 : ℝ) ^ (e.toInt + 2) * 2 ^ (53 : ℕ) from by
      rw [show e.toInt + 55 = (e.toInt + 2) + (53 : ℤ) from by ring,
        zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
      norm_num]
    split_ifs <;> norm_num <;> ring

/-- `FPR.make` is the correctly-rounded encoder of `± m * 2 ^ e`: it denotes that value up to
relative error `2 ^ (-53)`. This packages `abs_roundQuarterTiesEven_sub_div_four_le` (rounding
moves the significand by at most half a unit) together with `toRealBits_make` (the packing,
including its self-normalizing carry, is exact), and is the final-assembly half of the
per-operation `2 ^ (-52)` relative-error bounds.

This route is direct, phrased in the pre-rounding pair `(m, e)` that `FPR.make` consumes, rather
than through the general-theory `FPR.ulpOfExponent` / `FPR.ulpOfExponent_le_two_pow_neg52_mul_abs`
(which bound the spacing between adjacent representable values at a *decoded* exponent field).
The two routes agree in substance — in the no-carry case, `FPR.ulpOfExponent` at the decoded
output's exponent field `(e.toInt + 1076).toNat + 1` works out to the same scale factor
`2 ^ (e.toInt + 2)` that `toRealBits_make` produces — but formally connecting them would need that
equality re-derived alongside a case split on the rounding carry, for no shorter a proof than the
direct route already gives. -/
private theorem abs_toRealBits_make_sub_le (s : UInt64) (e : Int32) (m : UInt64)
    (hs : s.toNat ≤ 1) (he1 : -1076 ≤ e.toInt) (he2 : e.toInt ≤ 968)
    (hm1 : 2 ^ 54 ≤ m.toNat) (hm2 : m.toNat < 2 ^ 55) :
    |toRealBits (make s e m) -
        (if s.toNat = 1 then (-1 : ℝ) else 1) * (m.toNat : ℝ) * (2 : ℝ) ^ e.toInt| ≤
      (2 : ℝ) ^ (-(53 : ℤ)) *
        |(if s.toNat = 1 then (-1 : ℝ) else 1) * (m.toNat : ℝ) * (2 : ℝ) ^ e.toInt| := by
  rw [toRealBits_make s e m hs he1 he2 hm1 hm2]
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

/-- On a normalized significand `FPR.make_z` is `FPR.make`. The extra masking in `make_z` keys on
`m >>> 54`, i.e. on the *significand* being small, not on the exponent underflowing; the hypothesis
`2 ^ 54 ≤ m.toNat` is exactly the regime where that mask is all-ones and the two functions agree,
and no assumption on `e` is needed. -/
private theorem FPR.make_z_eq_make (s : UInt64) (e : Int32) (m : UInt64)
    (hm1 : 2 ^ 54 ≤ m.toNat) (hm2 : m.toNat < 2 ^ 55) :
    make_z s e m = make s e m := by
  have hsh : (m >>> 54 : UInt64) = 1 := by
    rw [← UInt64.toNat_inj, UInt64.toNat_shiftRight]
    simp only [UInt64.reduceToNat, Nat.reduceMod, Nat.shiftRight_eq_div_pow, Nat.reducePow]
    omega
  have hmask : ((0 : UInt32) - (m >>> 54).toUInt32) = 4294967295 := by
    rw [hsh]; decide
  unfold make make_z
  simp only [hmask]
  have hand : ∀ x : UInt32, x &&& 4294967295 = x := by
    intro x
    have hx : x.toNat < 2 ^ 32 := x.toNat_lt_size
    rw [← UInt32.toNat_inj, UInt32.toNat_and]
    rw [show (4294967295 : UInt32).toNat = 2 ^ 32 - 1 from by decide,
      Nat.and_two_pow_sub_one_eq_mod]
    omega
  rw [hand]

/-- Decode round-trip for `FPR.make_z`, ordinary case. -/
private theorem FPR.decode_make_z_of_no_carry (s : UInt64) (e : Int32) (m : UInt64)
    (hs : s.toNat ≤ 1) (he1 : -1076 ≤ e.toInt) (he2 : e.toInt ≤ 969)
    (hm1 : 2 ^ 54 ≤ m.toNat) (hm2 : m.toNat < 2 ^ 55)
    (hnc : roundQuarterTiesEven m.toNat < 2 ^ 53) :
    FPR.decode (make_z s e m) =
      { sign := decide (s.toNat = 1),
        exponent := (e.toInt + 1076).toNat + 1,
        mantissa := roundQuarterTiesEven m.toNat - 2 ^ 52 } := by
  rw [FPR.make_z_eq_make s e m hm1 hm2]
  exact FPR.decode_make_of_no_carry s e m hs he1 he2 hm1 hm2 hnc

/-- Decode round-trip for `FPR.make_z`, rounding-carry case. -/
private theorem FPR.decode_make_z_of_carry (s : UInt64) (e : Int32) (m : UInt64)
    (hs : s.toNat ≤ 1) (he1 : -1076 ≤ e.toInt) (he2 : e.toInt ≤ 969)
    (hm1 : 2 ^ 54 ≤ m.toNat) (hm2 : m.toNat < 2 ^ 55)
    (hc : roundQuarterTiesEven m.toNat = 2 ^ 53) :
    FPR.decode (make_z s e m) =
      { sign := decide (s.toNat = 1),
        exponent := (e.toInt + 1076).toNat + 2,
        mantissa := 0 } := by
  rw [FPR.make_z_eq_make s e m hm1 hm2]
  exact FPR.decode_make_of_carry s e m hs he1 he2 hm2 hc

/-- Denotation of `FPR.make_z` on a normalized significand, uniformly across the rounding
carry. -/
private theorem toRealBits_make_z (s : UInt64) (e : Int32) (m : UInt64)
    (hs : s.toNat ≤ 1) (he1 : -1076 ≤ e.toInt) (he2 : e.toInt ≤ 968)
    (hm1 : 2 ^ 54 ≤ m.toNat) (hm2 : m.toNat < 2 ^ 55) :
    toRealBits (make_z s e m) =
      (if s.toNat = 1 then (-1 : ℝ) else 1) * (roundQuarterTiesEven m.toNat : ℝ) *
        (2 : ℝ) ^ (e.toInt + 2) := by
  rw [FPR.make_z_eq_make s e m hm1 hm2]
  exact toRealBits_make s e m hs he1 he2 hm1 hm2

/-- `FPR.make_z` denotes `± m * 2 ^ e` up to relative error `2 ^ (-53)` on a normalized
significand. -/
private theorem abs_toRealBits_make_z_sub_le (s : UInt64) (e : Int32) (m : UInt64)
    (hs : s.toNat ≤ 1) (he1 : -1076 ≤ e.toInt) (he2 : e.toInt ≤ 968)
    (hm1 : 2 ^ 54 ≤ m.toNat) (hm2 : m.toNat < 2 ^ 55) :
    |toRealBits (make_z s e m) -
        (if s.toNat = 1 then (-1 : ℝ) else 1) * (m.toNat : ℝ) * (2 : ℝ) ^ e.toInt| ≤
      (2 : ℝ) ^ (-(53 : ℤ)) *
        |(if s.toNat = 1 then (-1 : ℝ) else 1) * (m.toNat : ℝ) * (2 : ℝ) ^ e.toInt| := by
  rw [FPR.make_z_eq_make s e m hm1 hm2]
  exact abs_toRealBits_make_sub_le s e m hs he1 he2 hm1 hm2

/-! ### The `m = 0` branch of `FPR.make_z`

The denotation lemmas above all require `2 ^ 54 ≤ m.toNat`, the normalized-significand range a
caller establishes with `fpr_ulsh_lzcnt64_top_bit` — which excludes exactly the collapsed case
`m = 0` that `FPR.make_z`'s extra `&&& ((0 : UInt32) - (m >>> 54).toUInt32)` mask exists to
handle (exact cancellation in `FPR.add`, or a zero operand in `FPR.mul` / `FPR.div`). On `m = 0`
that mask is `(0 : UInt32) - 0 = 0`, so it clears the exponent field outright regardless of what
`e` was computed, and the rounding fold of `m >>> 2` is `0` too: `FPR.make_z s e 0` is exactly
IEEE-754's signed-zero bit pattern, denoting `0`. This is the fact `or_fold_shiftRight_eq_zero_iff`
/ `stickyShift_eq_zero_iff` exist to feed: a caller who has shown a working significand's
pre-fold value was `0` (via those two) lands here for the resulting `FPR.make_z` call's
denotation. -/

/-- `FPR.make_z` collapses to the signed-zero bit pattern `s <<< 63` on a zero significand: the
mask `(0 : UInt32) - (m >>> 54).toUInt32` is `0` when `m = 0`, clearing the exponent field, and
`m >>> 2 = 0` together with `roundTableBit 0 = 0` clears the mantissa field. -/
private theorem make_z_of_zero (s : UInt64) (e : Int32) : make_z s e 0 = s <<< 63 := by
  rw [make_z_eq_roundQuarterTiesEven]
  have h0 : ((0 : UInt64) >>> 54).toUInt32 = 0 := by decide
  have hr : roundQuarterTiesEven (0 : UInt64).toNat = 0 := by decide
  rw [h0, hr]
  simp

/-- Decode of `FPR.make_z` on a zero significand: the sign bit is returned unchanged, and both
the exponent and mantissa fields are `0` — IEEE-754's signed-zero bit pattern — independently of
`e`. -/
private theorem FPR.decode_make_z_of_zero (s : UInt64) (e : Int32) (hs : s.toNat ≤ 1) :
    FPR.decode (make_z s e 0) =
      { sign := decide (s.toNat = 1), exponent := 0, mantissa := 0 } := by
  rw [make_z_of_zero]
  have hA : (s <<< 63 : UInt64).toNat = s.toNat * 2 ^ 63 := by
    rw [UInt64.toNat_shiftLeft]
    simp only [UInt64.reduceToNat, Nat.reduceMod, Nat.shiftLeft_eq, Nat.reducePow]
    omega
  unfold FPR.decode
  rw [hA]
  simp only [Nat.testBit_eq_decide_div_mod_eq, Nat.shiftRight_eq_div_pow, FPR.Bits.mk.injEq,
    decide_eq_decide]
  refine ⟨?_, ?_, ?_⟩ <;> omega

/-- `FPR.make_z` denotes exactly `0` on a zero significand, for any sign `s` and any exponent
`e`: the collapsed-significand counterpart to `abs_toRealBits_make_z_sub_le`'s normalized-range
relative-error bound. -/
private theorem toRealBits_make_z_of_zero (s : UInt64) (e : Int32) (hs : s.toNat ≤ 1) :
    toRealBits (make_z s e 0) = 0 := by
  unfold toRealBits
  rw [FPR.decode_make_z_of_zero s e hs]
  unfold FPR.Bits.toReal
  norm_num

/-! ### Sanity witnesses -/

/-- The eight rounded quotients for the eight low-bit patterns of the working significand:
`0.00, 0.25, 0.50, 0.75, 1.00, 1.25, 1.50, 1.75` round to `0, 0, 0, 1, 1, 1, 2, 2`. -/
example : (List.range 8).map roundQuarterTiesEven = [0, 0, 0, 1, 1, 1, 2, 2] := by decide

/-- The eight table entries of `0xC8 = 0b11001000`. -/
example :
    (List.range 8).map (fun i => (roundTableBit (UInt64.ofNat i)).toNat) =
      [0, 0, 0, 1, 0, 0, 1, 1] := by decide

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

private theorem addPipeline_n' (x y : FPR) : (addPipeline x y).n' = (addPipeline x y).n &&& 63 :=
  rfl

private theorem addPipeline_m (x y : FPR) :
    (addPipeline x y).m = fpr_ulsh 1 (addPipeline x y).n' - 1 := rfl

private theorem addPipeline_yu (x y : FPR) :
    (addPipeline x y).yu =
      fpr_ursh
        ((addPipeline x y).yu'
          ||| (((addPipeline x y).yu' &&& (addPipeline x y).m) + (addPipeline x y).m))
        (addPipeline x y).n' := rfl

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

/-- The `bit ≤ 1` generalisation of `or_two_pow_add_of_lt`, matching the shape of the implicit-bit
fold `xu`/`yu_` use. -/
private theorem or_mul_two_pow_add_of_lt (a k bit : ℕ) (hbit : bit ≤ 1) (ha : a < 2 ^ k) :
    a ||| bit * 2 ^ k = a + bit * 2 ^ k := by
  interval_cases bit
  · simp
  · simpa using or_two_pow_add_of_lt a k ha

/-- Masking an `FPR` word with `M52` computes exactly its decoded mantissa. -/
private theorem toNat_and_M52_eq_mantissa (w : FPR) :
    (w &&& M52).toNat = (FPR.decode w).mantissa := by
  have h : (w &&& M52).toNat = w.toNat % 2 ^ 52 :=
    toNat_and_one_shiftLeft_sub_one w (52 : UInt64) (by decide)
  rw [h]
  rfl

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

/-- The combined sign+exponent word `(w >>> 52).toUInt32` computed from any `FPR` word `w` is
exactly `w.toNat / 2 ^ 52`, with no truncation from the `UInt64 → UInt32` narrowing (the value
never exceeds `2 ^ 12`). -/
private theorem toNat_ex_of (w : FPR) : ((w >>> 52).toUInt32).toNat = w.toNat / 2 ^ 52 := by
  rw [UInt64.toNat_toUInt32, UInt64.toNat_shiftRight,
    show (52 : UInt64).toNat % 64 = 52 from by decide, Nat.shiftRight_eq_div_pow]
  have hb : w.toNat < 2 ^ 64 := w.toNat_lt_size
  exact Nat.mod_eq_of_lt (by omega)

/-- The sign-bit extraction `((w >>> 52).toUInt32) >>> 11` recovers the top bit of `w`. -/
private theorem toNat_sx_of (w : FPR) :
    (((w >>> 52).toUInt32) >>> 11).toNat = w.toNat / 2 ^ 63 := by
  rw [UInt32.toNat_shiftRight, toNat_ex_of,
    show (11 : UInt32).toNat % 32 = 11 from by decide, Nat.shiftRight_eq_div_pow,
    Nat.div_div_eq_div_mul, show (2 : ℕ) ^ 52 * 2 ^ 11 = 2 ^ 63 from by norm_num]

/-- The exponent-field extraction `((w >>> 52).toUInt32) &&& 0x7FF` recovers exactly
`FPR.decode`'s exponent field. -/
private theorem toNat_ex_field_of (w : FPR) :
    (((w >>> 52).toUInt32) &&& 0x7FF).toNat = (FPR.decode w).exponent := by
  rw [UInt32.toNat_and, toNat_ex_of, show (0x7FF : UInt32).toNat = 2 ^ 11 - 1 from by decide,
    Nat.and_two_pow_sub_one_eq_mod]
  unfold FPR.decode
  rw [Nat.shiftRight_eq_div_pow]

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

/-- Reducing a shift amount below `64` mod `64` is the identity. -/
private theorem toNat_and_63_of_lt {n : UInt32} (h : n.toNat < 64) :
    (n &&& 63).toNat = n.toNat := by
  rw [UInt32.toNat_and, show (63 : UInt32).toNat = 2 ^ 6 - 1 from by decide,
    Nat.and_two_pow_sub_one_eq_mod]
  exact Nat.mod_eq_of_lt (by omega)

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

/-- For a normal operand's biased exponent field (`1 ≤ ex.toNat ≤ 2046`), the `ex'` step of
`FPR.add`'s pipeline (`UInt32` subtraction by `1078`, reinterpreted as `Int32`) computes the plain
integer difference `ex.toNat - 1078`: the wraparound pattern the `UInt32` subtraction produces
when `ex.toNat < 1078` lands exactly on the two's-complement encoding of the intended negative
value. -/
private theorem toInt_sub_1078_toInt32 (ex : UInt32) (h1 : 1 ≤ ex.toNat) (h2 : ex.toNat ≤ 2046) :
    (ex - 1078).toInt32.toInt = (ex.toNat : ℤ) - 1078 :=
  toInt_sub_1078_toInt32_of_lt (by omega)

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

/-- The magnitude of a decoded field triple's real value, in the uniform
`significand * 2 ^ (exponent - 1075)` shape (a restatement of `FPR.Bits.abs_toReal_eq` folding the
implicit leading bit into `FPR.Bits.significand`, dropping the subnormal/normal case split
entirely once `exponent ≠ 0` is known). -/
private theorem abs_toReal_eq_significand_mul_two_zpow {bx : FPR.Bits} (h0 : bx.exponent ≠ 0)
    (h2047 : bx.exponent ≠ 2047) :
    |bx.toReal| = (bx.significand : ℝ) * (2 : ℝ) ^ ((bx.exponent : ℤ) - 1075) := by
  rw [FPR.Bits.abs_toReal_eq, if_neg h0, if_neg h2047]
  unfold FPR.Bits.significand
  rw [if_neg h0]
  push_cast
  rw [show ((bx.exponent : ℤ) - 1075) = ((bx.exponent : ℤ) - 1023) + (-52 : ℤ) by ring,
    zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
  ring

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
  · rw [if_pos hc] at h
    have hsel : ((n - 60) >>> 31 : UInt32) = 0 := by rw [← UInt32.toNat_inj, h]; rfl
    rw [if_pos hc, hsel]
    decide
  · rw [if_neg hc] at h
    have hsel : ((n - 60) >>> 31 : UInt32) = 1 := by rw [← UInt32.toNat_inj, h]; rfl
    rw [if_neg hc, hsel]
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
  rw [addPipeline_yu'_eq, if_neg (by omega)]

/-- Flush to zero from an exponent gap of `60` on. -/
private theorem addPipeline_yu'_eq_zero (a b : FPR) (h60 : 60 ≤ (addPipeline a b).n.toNat) :
    (addPipeline a b).yu' = 0 := by
  have hb := addPipeline_n_lt a b
  rw [addPipeline_yu'_eq, if_pos ⟨h60, by omega⟩]

/-- The flushed operand contributes nothing to the sum. -/
private theorem addPipeline_yu_eq_zero (a b : FPR) (h60 : 60 ≤ (addPipeline a b).n.toNat) :
    (addPipeline a b).yu = 0 := by
  have h0 : (addPipeline a b).yu.toNat = 0 := by
    rw [addPipeline_yu_toNat, addPipeline_yu'_eq_zero a b h60]
    exact (stickyShift_eq_zero_iff _ _).mpr rfl
  rw [← UInt64.toNat_inj, h0]
  rfl

/-- The exponent gap in decoded terms. -/
private theorem addPipeline_n_toNat_eq_exponent_sub (a b : FPR) :
    (addPipeline a b).n.toNat
      = (FPR.decode (addPipeline a b).x').exponent
        - (FPR.decode (addPipeline a b).y').exponent := by
  rw [addPipeline_n_toNat, addPipeline_ex_eq_exponent, addPipeline_ey_eq_exponent]

/-- The flush condition, with the unreachable wrapping window eliminated: `FPR.add` zeroes the
smaller operand exactly when the exponent gap reaches `60`. -/
private theorem addPipeline_yu'_eq_of_gap (a b : FPR) :
    (addPipeline a b).yu'
      = if 60 ≤ (addPipeline a b).n.toNat then 0 else (addPipeline a b).yu_ := by
  by_cases hc : 60 ≤ (addPipeline a b).n.toNat
  · rw [if_pos hc]; exact addPipeline_yu'_eq_zero a b hc
  · rw [if_neg hc]; exact addPipeline_yu'_eq_yuRaw a b (by omega)

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

/-- The aligned significand is within one unit in the last place of the exactly-scaled one. -/
private theorem abs_addPipeline_yu_sub_lt (a b : FPR) :
    |((addPipeline a b).yu.toNat : ℝ)
        - ((addPipeline a b).yu'.toNat : ℝ) / 2 ^ ((addPipeline a b).n &&& 63).toNat| < 1 := by
  obtain ⟨h1, h2⟩ := addPipeline_yu_real_bracket a b
  rw [abs_lt]
  constructor <;> linarith

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

/-- The ulp bracket, packaged against the decoded significand of the smaller operand: below the
flush threshold, the aligned significand `yu` is within one ulp of `8 * S / 2 ^ n`. -/
private theorem abs_addPipeline_yu_sub_significand_lt (a b : FPR)
    (h : (addPipeline a b).n.toNat < 60) :
    |((addPipeline a b).yu.toNat : ℝ)
        - (8 * (FPR.decode (addPipeline a b).y').significand : ℕ)
            / 2 ^ (addPipeline a b).n.toNat| < 1 := by
  have hk : ((addPipeline a b).n &&& 63).toNat = (addPipeline a b).n.toNat :=
    toNat_and_63_of_lt (by omega)
  have hv : (addPipeline a b).yu'.toNat
      = (8 * (FPR.decode (addPipeline a b).y').significand : ℕ) := by
    rw [addPipeline_yu'_eq_yuRaw a b h, addPipeline_yuRaw_toNat]
  have := abs_addPipeline_yu_sub_lt a b
  rwa [hk, hv] at this

/-- The alignment step loses no zero-ness: the aligned significand vanishes exactly when the
(post-flush) input did. -/
private theorem addPipeline_yu_eq_zero_iff (a b : FPR) :
    (addPipeline a b).yu = 0 ↔ (addPipeline a b).yu' = 0 := by
  rw [← UInt64.toNat_inj, ← UInt64.toNat_inj (a := (addPipeline a b).yu'),
    show (0 : UInt64).toNat = 0 from rfl, addPipeline_yu_toNat]
  exact stickyShift_eq_zero_iff _ _

/-- The low bit of the aligned significand is the sticky bit: it is set exactly when the
alignment discarded a nonzero bit. -/
private theorem addPipeline_yu_toNat_mod_two (a b : FPR) :
    (addPipeline a b).yu.toNat % 2
      = if (addPipeline a b).yu'.toNat % 2 ^ (((addPipeline a b).n &&& 63).toNat + 1) = 0
        then 0 else 1 := by
  rw [addPipeline_yu_toNat, stickyShift_mod_two]

/-- The sticky bit is set exactly when alignment discarded something. -/
private theorem addPipeline_yu_sticky_iff (a b : FPR) :
    (addPipeline a b).yu.toNat % 2 = 1
      ↔ (addPipeline a b).yu'.toNat % 2 ^ (((addPipeline a b).n &&& 63).toNat + 1) ≠ 0 := by
  constructor
  · intro h1 h0
    rw [addPipeline_yu_toNat_mod_two, if_pos h0] at h1
    exact absurd h1 (by decide)
  · intro h0
    rw [addPipeline_yu_toNat_mod_two, if_neg h0]

/-- Closed form of the aligned significand: the exact right shift by `n' + 1`, doubled, plus the
sticky bit. -/
private theorem addPipeline_yu_toNat_eq (a b : FPR) :
    (addPipeline a b).yu.toNat
      = 2 * ((addPipeline a b).yu'.toNat / 2 ^ (((addPipeline a b).n &&& 63).toNat + 1))
        + (if (addPipeline a b).yu'.toNat % 2 ^ (((addPipeline a b).n &&& 63).toNat + 1) = 0
            then 0 else 1) := by
  rw [addPipeline_yu_toNat, stickyShift_eq]

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
  · rw [if_pos hc] at h; right; apply UInt32.toNat_inj.mp; rw [h]; decide
  · rw [if_neg hc] at h; left; apply UInt32.toNat_inj.mp; rw [h]; decide

/-- The pipeline's `sy` field is a packed sign bit, hence `0` or `1`. -/
private theorem addPipeline_sy_eq_zero_or_one (a b : FPR) :
    (addPipeline a b).sy = 0 ∨ (addPipeline a b).sy = 1 := by
  have h := addPipeline_sy_toNat a b
  rcases Classical.em (FPR.decode (addPipeline a b).y').sign with hc | hc
  · rw [if_pos hc] at h; right; apply UInt32.toNat_inj.mp; rw [h]; decide
  · rw [if_neg hc] at h; left; apply UInt32.toNat_inj.mp; rw [h]; decide

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
  rw [if_neg (by omega : ¬ (e.toInt + 1076).toNat + 1 = 0),
    if_neg (by omega : ¬ (e.toInt + 1076).toNat + 1 = 2047)]
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

/-! ## (II) Signed denotation of the two pipeline operands -/

private theorem toReal_eq_significand_mul_two_zpow {bx : FPR.Bits} (h0 : bx.exponent ≠ 0)
    (h2047 : bx.exponent ≠ 2047) :
    bx.toReal = (if bx.sign then (-1 : ℝ) else 1) * (bx.significand : ℝ) *
      (2 : ℝ) ^ ((bx.exponent : ℤ) - 1075) := by
  unfold FPR.Bits.toReal
  rw [if_neg h0, if_neg h2047]
  unfold FPR.Bits.significand
  rw [if_neg h0]
  push_cast
  rw [show ((bx.exponent : ℤ) - 1075) = ((bx.exponent : ℤ) - 1023) + (-52 : ℤ) by ring,
    zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
  ring

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

private theorem significand_mem_of_isNormal {b : FPR.Bits} (h0 : b.exponent ≠ 0)
    (hm : b.mantissa < 2 ^ 52) : 2 ^ 52 ≤ b.significand ∧ b.significand < 2 ^ 53 := by
  unfold FPR.Bits.significand
  rw [if_neg h0]
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

/-! ## (IV) Signed denotation of the two pipeline operands -/

private theorem addPipeline_sign_x' (a b : FPR) :
    (if (addPipeline a b).sx.toNat = 1 then (-1 : ℝ) else 1)
      = (if (FPR.decode (addPipeline a b).x').sign then (-1 : ℝ) else 1) := by
  rw [addPipeline_sx_toNat]
  split_ifs <;> simp_all

private theorem addPipeline_sign_y' (a b : FPR) :
    (if (addPipeline a b).sy.toNat = 1 then (-1 : ℝ) else 1)
      = (if (FPR.decode (addPipeline a b).y').sign then (-1 : ℝ) else 1) := by
  rw [addPipeline_sy_toNat]
  split_ifs <;> simp_all

private theorem addPipeline_toReal_x'_eq (a b : FPR) (ha : FPR.IsNormal a) (hb : FPR.IsNormal b) :
    toReal (addPipeline a b).x' =
      (if (addPipeline a b).sx.toNat = 1 then (-1 : ℝ) else 1) *
        ((addPipeline a b).xu.toNat : ℝ) * (2 : ℝ) ^ (addPipeline a b).ex'.toInt := by
  obtain ⟨h0, h2047⟩ := addPipeline_x'_isNormal a b ha hb
  rw [addPipeline_sign_x', addPipeline_xu_toNat, addPipeline_ex'_toInt, addPipeline_ex_eq_exponent]
  change (FPR.decode (addPipeline a b).x').toReal = _
  rw [toReal_eq_significand_mul_two_zpow h0 h2047]
  push_cast
  rw [show (((FPR.decode (addPipeline a b).x').exponent : ℤ) - 1078)
      = (((FPR.decode (addPipeline a b).x').exponent : ℤ) - 1075) + (-3 : ℤ) by ring,
    zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
  ring

private theorem addPipeline_ey_toInt_eq (a b : FPR) :
    ((FPR.decode (addPipeline a b).y').exponent : ℤ) - 1078
      = (addPipeline a b).ex'.toInt - ((addPipeline a b).n.toNat : ℤ) := by
  have hn := addPipeline_n_toNat a b
  have hle := addPipeline_ey_le_ex a b
  have hex' := addPipeline_ex'_toInt a b
  rw [← addPipeline_ey_eq_exponent, hex', hn]
  omega

private theorem addPipeline_toReal_y'_eq (a b : FPR) (ha : FPR.IsNormal a) (hb : FPR.IsNormal b) :
    toReal (addPipeline a b).y' =
      (if (addPipeline a b).sy.toNat = 1 then (-1 : ℝ) else 1) *
        (((addPipeline a b).yu_.toNat : ℝ) / 2 ^ (addPipeline a b).n.toNat) *
        (2 : ℝ) ^ (addPipeline a b).ex'.toInt := by
  obtain ⟨h0, h2047⟩ := addPipeline_y'_isNormal a b ha hb
  rw [addPipeline_sign_y', addPipeline_yuRaw_toNat]
  change (FPR.decode (addPipeline a b).y').toReal = _
  rw [toReal_eq_significand_mul_two_zpow h0 h2047]
  push_cast
  rw [show (((FPR.decode (addPipeline a b).y').exponent : ℤ) - 1075)
      = ((((FPR.decode (addPipeline a b).y').exponent : ℤ) - 1078)) + (3 : ℤ) by ring,
    addPipeline_ey_toInt_eq, zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0),
    zpow_sub₀ (by norm_num : (2 : ℝ) ≠ 0), zpow_natCast]
  field_simp
  ring

/-! ## (V) The alignment error -/

private theorem stickyShift_of_dvd (v k : ℕ) (h : v % 2 ^ k = 0) : stickyShift v k = v / 2 ^ k := by
  unfold stickyShift
  rw [if_pos h, Nat.or_zero, Nat.shiftRight_eq_div_pow]

private theorem addPipeline_align_lt (a b : FPR) (ha : FPR.IsNormal a) (hb : FPR.IsNormal b) :
    |((addPipeline a b).yu.toNat : ℝ)
        - ((addPipeline a b).yu_.toNat : ℝ) / 2 ^ (addPipeline a b).n.toNat| < 1 := by
  by_cases hn : (addPipeline a b).n.toNat < 60
  · obtain ⟨h1, h2⟩ := addPipeline_yu_real_bracket_yuRaw a b hn
    rw [abs_lt]
    constructor <;> linarith
  · have hz : (addPipeline a b).yu = 0 := addPipeline_yu_eq_zero a b (by omega)
    have hyu : ((addPipeline a b).yu.toNat : ℝ) = 0 := by rw [hz]; norm_num
    have hlt : (addPipeline a b).yu_.toNat < 2 ^ (addPipeline a b).n.toNat := by
      have h56 := (addPipeline_yuRaw_mem a b ha hb).2
      have : (2 : ℕ) ^ 56 ≤ 2 ^ (addPipeline a b).n.toNat :=
        Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    have hltR : ((addPipeline a b).yu_.toNat : ℝ) < 2 ^ (addPipeline a b).n.toNat := by
      exact_mod_cast hlt
    have hpos : (0 : ℝ) < 2 ^ (addPipeline a b).n.toNat := by positivity
    rw [hyu, zero_sub, abs_neg, abs_of_nonneg (by positivity)]
    rw [div_lt_one hpos]
    exact hltR

private theorem addPipeline_align_exact (a b : FPR) (h : (addPipeline a b).n.toNat ≤ 3) :
    ((addPipeline a b).yu.toNat : ℝ)
      = ((addPipeline a b).yu_.toNat : ℝ) / 2 ^ (addPipeline a b).n.toNat := by
  have hk : ((addPipeline a b).n &&& 63).toNat = (addPipeline a b).n.toNat :=
    toNat_and_63_of_lt (by omega)
  have hv : (addPipeline a b).yu'.toNat = (addPipeline a b).yu_.toNat := by
    rw [addPipeline_yu'_eq_yuRaw a b (by omega)]
  have hdvd : 2 ^ (addPipeline a b).n.toNat ∣ (addPipeline a b).yu_.toNat := by
    rw [addPipeline_yuRaw_toNat]
    have h8 : (2 : ℕ) ^ (addPipeline a b).n.toNat ∣ 8 := by
      have := pow_dvd_pow 2 h
      rwa [show (2 : ℕ) ^ 3 = 8 from by norm_num] at this
    exact h8.trans (dvd_mul_right 8 _)
  have hnat : (addPipeline a b).yu.toNat
      = (addPipeline a b).yu_.toNat / 2 ^ (addPipeline a b).n.toNat := by
    rw [addPipeline_yu_toNat, hk, hv]
    exact stickyShift_of_dvd _ _ (Nat.dvd_iff_mod_eq_zero.mp hdvd)
  rw [hnat, Nat.cast_div hdvd (by positivity)]
  norm_num

private theorem addPipeline_abs_toReal_le (a b : FPR) (ha : FPR.IsNormal a)
    (hb : FPR.IsNormal b) :
    |toReal (addPipeline a b).y'| ≤ |toReal (addPipeline a b).x'| := by
  by_contra hc
  push Not at hc
  have hkey := (FPR.Bits.abs_toReal_lt_iff_magKey_lt (FPR.decode (addPipeline a b).x')
    (FPR.decode (addPipeline a b).y') (FPR.decode_mantissa_lt _) (FPR.decode_mantissa_lt _)
    (addPipeline_x'_isNormal a b ha hb).2 (addPipeline_y'_isNormal a b ha hb).2).mp hc
  exact absurd (addPipeline_swap_cases a b).2 (by omega)

/-! ## (VI) The combined significand's value -/

private theorem addPipeline_abs_toReal_y'_eq (a b : FPR) (ha : FPR.IsNormal a)
    (hb : FPR.IsNormal b) :
    |toReal (addPipeline a b).y'| =
      (((addPipeline a b).yu_.toNat : ℝ) / 2 ^ (addPipeline a b).n.toNat) *
        (2 : ℝ) ^ (addPipeline a b).ex'.toInt := by
  rw [addPipeline_toReal_y'_eq a b ha hb, abs_mul, abs_mul,
    show |(if (addPipeline a b).sy.toNat = 1 then (-1 : ℝ) else 1)| = 1 from by
      split_ifs <;> norm_num,
    abs_of_nonneg (show (0 : ℝ) ≤ ((addPipeline a b).yu_.toNat : ℝ)
      / 2 ^ (addPipeline a b).n.toNat by positivity),
    abs_of_pos (show (0 : ℝ) < (2 : ℝ) ^ (addPipeline a b).ex'.toInt from
      zpow_pos (by norm_num) _), one_mul]

private theorem addPipeline_Yprime_le_xu (a b : FPR) (ha : FPR.IsNormal a) (hb : FPR.IsNormal b) :
    ((addPipeline a b).yu_.toNat : ℝ) / 2 ^ (addPipeline a b).n.toNat
      ≤ ((addPipeline a b).xu.toNat : ℝ) := by
  have hp : (0 : ℝ) < (2 : ℝ) ^ (addPipeline a b).ex'.toInt := zpow_pos (by norm_num) _
  have h := addPipeline_abs_toReal_le a b ha hb
  rw [addPipeline_abs_toReal_y'_eq a b ha hb,
    addPipeline_abs_toReal_x'_eq a b (addPipeline_x'_isNormal a b ha hb).1
      (addPipeline_x'_isNormal a b ha hb).2] at h
  exact le_of_mul_le_mul_right (by linarith) hp

private theorem addPipeline_yu_le_xu (a b : FPR) (ha : FPR.IsNormal a) (hb : FPR.IsNormal b) :
    (addPipeline a b).yu.toNat ≤ (addPipeline a b).xu.toNat := by
  have h1 := addPipeline_align_lt a b ha hb
  have h2 := addPipeline_Yprime_le_xu a b ha hb
  rw [abs_lt] at h1
  have : ((addPipeline a b).yu.toNat : ℝ) < ((addPipeline a b).xu.toNat : ℝ) + 1 := by linarith
  have hcast : ((addPipeline a b).yu.toNat : ℝ) < (((addPipeline a b).xu.toNat + 1 : ℕ) : ℝ) := by
    push_cast; linarith
  have := Nat.cast_lt (α := ℝ).mp hcast
  omega

private theorem addPipeline_sigma_rel (a b : FPR) :
    (if (addPipeline a b).sy.toNat = 1 then (-1 : ℝ) else 1)
      = (if (addPipeline a b).sx = (addPipeline a b).sy then (1 : ℝ) else -1) *
        (if (addPipeline a b).sx.toNat = 1 then (-1 : ℝ) else 1) := by
  rcases addPipeline_sx_eq_zero_or_one a b with hx | hx <;>
    rcases addPipeline_sy_eq_zero_or_one a b with hy | hy <;> rw [hx, hy] <;>
      simp only [toNat_lit0, toNat_lit1, show ((0 : UInt32) = 1) = False from by simp,
        show ((1 : UInt32) = 0) = False from by simp] <;> norm_num

private theorem addPipeline_zu_real (a b : FPR) (ha : FPR.IsNormal a) (hb : FPR.IsNormal b) :
    ((addPipeline a b).zu.toNat : ℝ)
      = ((addPipeline a b).xu.toNat : ℝ)
        + (if (addPipeline a b).sx = (addPipeline a b).sy then (1 : ℝ) else -1) *
          ((addPipeline a b).yu.toNat : ℝ) := by
  have hle := addPipeline_yu_le_xu a b ha hb
  have hxu := (addPipeline_xu_mem a b ha hb).2
  by_cases hs : (addPipeline a b).sx = (addPipeline a b).sy
  · rw [if_pos hs, addPipeline_zu_eq_add_of_sx_eq_sy a b hs, UInt64.toNat_add]
    rw [Nat.mod_eq_of_lt (by omega)]
    push_cast
    ring
  · rw [if_neg hs, addPipeline_zu_toNat_eq_of_sx_ne_sy a b hs hle, Nat.cast_sub hle]
    ring

private theorem addPipeline_S_eq (a b : FPR) (ha : FPR.IsNormal a) (hb : FPR.IsNormal b) :
    toReal a + toReal b =
      (if (addPipeline a b).sx.toNat = 1 then (-1 : ℝ) else 1) *
        (((addPipeline a b).xu.toNat : ℝ)
          + (if (addPipeline a b).sx = (addPipeline a b).sy then (1 : ℝ) else -1) *
            (((addPipeline a b).yu_.toNat : ℝ) / 2 ^ (addPipeline a b).n.toNat)) *
        (2 : ℝ) ^ (addPipeline a b).ex'.toInt := by
  rw [← addPipeline_sum_eq a b, addPipeline_toReal_x'_eq a b ha hb,
    addPipeline_toReal_y'_eq a b ha hb, addPipeline_sigma_rel a b]
  ring

/-! ## (VII) Exponent bounds and the rounding fold -/

private theorem addPipeline_ex'_le (a b : FPR) (ha : FPR.IsNormal a) (hb : FPR.IsNormal b) :
    (addPipeline a b).ex'.toInt ≤ 968 := by
  have h1 := addPipeline_ex'_toInt a b
  have h2 := addPipeline_ex_lt a b
  have h3 : (addPipeline a b).ex.toNat ≠ 2047 := by
    rw [addPipeline_ex_eq_exponent]; exact (addPipeline_x'_isNormal a b ha hb).2
  omega

private theorem addPipeline_ex'_ge (a b : FPR) (ha : FPR.IsNormal a) (hb : FPR.IsNormal b) :
    ((addPipeline a b).n.toNat : ℤ) - 1077 ≤ (addPipeline a b).ex'.toInt := by
  have h1 := addPipeline_ex'_toInt a b
  have h2 := addPipeline_n_toNat a b
  have h3 := addPipeline_ey_le_ex a b
  have h4 : (addPipeline a b).ey.toNat ≠ 0 := by
    rw [addPipeline_ey_eq_exponent]; exact (addPipeline_y'_isNormal a b ha hb).1
  omega

private theorem addPipeline_ex'_ge' (a b : FPR) (ha : FPR.IsNormal a) (hb : FPR.IsNormal b) :
    (-1077 : ℤ) ≤ (addPipeline a b).ex'.toInt := by
  have := addPipeline_ex'_ge a b ha hb
  omega

private theorem addPipeline_zu''_sticky (a b : FPR) :
    (addPipeline a b).zu''.toNat = stickyShift (addPipeline a b).zu'.toNat 9 := by
  rw [addPipeline_zu'', toNat_or_fold_shiftRight_nine]

private theorem addPipeline_zu'_ge (a b : FPR) (h : (addPipeline a b).zu ≠ 0) :
    2 ^ 63 ≤ (addPipeline a b).zu'.toNat := by
  rw [addPipeline_zu', addPipeline_c]
  exact fpr_ulsh_lzcnt64_top_bit _ h

/-- The nine-bit rounding fold moves the working value by less than `2 ^ 9` ulps at the
post-renormalisation scale. -/
private theorem addPipeline_fold_abs_lt (a b : FPR) :
    |((addPipeline a b).zu''.toNat : ℝ) * 2 ^ (9 : ℕ) - ((addPipeline a b).zu'.toNat : ℝ)|
      < 2 ^ (9 : ℕ) := by
  have h1 := stickyShift_mul_lt (addPipeline a b).zu'.toNat 9
  have h2 := lt_stickyShift_mul_add (addPipeline a b).zu'.toNat 9
  rw [← addPipeline_zu''_sticky] at h1 h2
  have h1' : ((addPipeline a b).zu''.toNat : ℝ) * 2 ^ (9 : ℕ)
      < ((addPipeline a b).zu'.toNat : ℝ) + 2 ^ (9 : ℕ) := by exact_mod_cast h1
  have h2' : ((addPipeline a b).zu'.toNat : ℝ)
      < ((addPipeline a b).zu''.toNat : ℝ) * 2 ^ (9 : ℕ) + 2 ^ (9 : ℕ) := by exact_mod_cast h2
  rw [abs_lt]
  constructor <;> linarith

/-- The exponent identity `ex''' = ex'' + 9`, as plain integers. -/
private theorem addPipeline_ex'''_eq_ex''_add (a b : FPR) :
    (addPipeline a b).ex'''.toInt = (addPipeline a b).ex''.toInt + 9 := by
  rw [addPipeline_ex'''_toInt, addPipeline_ex''_toInt]

/-- The rounding fold's contribution to the error, relative to the pre-fold working value. -/
private theorem addPipeline_fold_error (a b : FPR) (hzu : (addPipeline a b).zu ≠ 0)
    (hb31 : -(2 ^ 31 : ℤ) + 63 ≤ (addPipeline a b).ex'.toInt) :
    |((addPipeline a b).zu''.toNat : ℝ) * (2 : ℝ) ^ (addPipeline a b).ex'''.toInt
        - ((addPipeline a b).zu.toNat : ℝ) * (2 : ℝ) ^ (addPipeline a b).ex'.toInt|
      ≤ (2 : ℝ) ^ (-(54 : ℤ)) *
        (((addPipeline a b).zu.toNat : ℝ) * (2 : ℝ) ^ (addPipeline a b).ex'.toInt) := by
  have hren := addPipeline_renorm_value_preserving a b hzu hb31
  have hq : (0 : ℝ) < (2 : ℝ) ^ (addPipeline a b).ex''.toInt := zpow_pos (by norm_num) _
  have hsplit : (2 : ℝ) ^ (addPipeline a b).ex'''.toInt
      = (2 : ℝ) ^ (addPipeline a b).ex''.toInt * 2 ^ (9 : ℕ) := by
    rw [addPipeline_ex'''_eq_ex''_add, zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
    norm_num
  rw [← hren, hsplit,
    show ((addPipeline a b).zu''.toNat : ℝ) *
        ((2 : ℝ) ^ (addPipeline a b).ex''.toInt * 2 ^ (9 : ℕ))
        - ((addPipeline a b).zu'.toNat : ℝ) * (2 : ℝ) ^ (addPipeline a b).ex''.toInt
      = (2 : ℝ) ^ (addPipeline a b).ex''.toInt *
        (((addPipeline a b).zu''.toNat : ℝ) * 2 ^ (9 : ℕ)
          - ((addPipeline a b).zu'.toNat : ℝ)) from by ring,
    abs_mul, abs_of_pos hq]
  have hf := addPipeline_fold_abs_lt a b
  have hge : (2 : ℝ) ^ (63 : ℕ) ≤ ((addPipeline a b).zu'.toNat : ℝ) := by
    exact_mod_cast addPipeline_zu'_ge a b hzu
  have hc : (2 : ℝ) ^ (-(54 : ℤ)) * (2 : ℝ) ^ (63 : ℕ) = 2 ^ (9 : ℕ) := by
    rw [← zpow_natCast (2 : ℝ) 63, ← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
    norm_num
  have hcpos : (0 : ℝ) < (2 : ℝ) ^ (-(54 : ℤ)) := zpow_pos (by norm_num) _
  have hstep : (2 : ℝ) ^ (9 : ℕ) ≤ (2 : ℝ) ^ (-(54 : ℤ)) * ((addPipeline a b).zu'.toNat : ℝ) := by
    have := mul_le_mul_of_nonneg_left hge hcpos.le
    rw [hc] at this
    linarith
  calc (2 : ℝ) ^ (addPipeline a b).ex''.toInt *
        |((addPipeline a b).zu''.toNat : ℝ) * 2 ^ (9 : ℕ) - ((addPipeline a b).zu'.toNat : ℝ)|
      ≤ (2 : ℝ) ^ (addPipeline a b).ex''.toInt * (2 : ℝ) ^ (9 : ℕ) :=
        mul_le_mul_of_nonneg_left hf.le hq.le
    _ ≤ (2 : ℝ) ^ (-(54 : ℤ)) *
        (((addPipeline a b).zu'.toNat : ℝ) * (2 : ℝ) ^ (addPipeline a b).ex''.toInt) := by
        nlinarith

/-! ## (VIII) The pre-rounding working value -/

private theorem two_pow_mul_zpow (k : ℕ) (m : ℤ) :
    (2 : ℝ) ^ (k : ℕ) * (2 : ℝ) ^ m = (2 : ℝ) ^ ((k : ℤ) + m) := by
  rw [← zpow_natCast (2 : ℝ) k, ← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]

private theorem addPipeline_abs_sigma (a b : FPR) :
    |(if (addPipeline a b).sx.toNat = 1 then (-1 : ℝ) else 1)| = 1 := by
  split_ifs <;> norm_num

private theorem addPipeline_abs_sigma_tau (a b : FPR) :
    |(if (addPipeline a b).sx.toNat = 1 then (-1 : ℝ) else 1) *
        (if (addPipeline a b).sx = (addPipeline a b).sy then (1 : ℝ) else -1)| = 1 := by
  rw [abs_mul, addPipeline_abs_sigma]
  split_ifs <;> norm_num

private theorem addPipeline_p_ge (a b : FPR) (ha : FPR.IsNormal a) (hb : FPR.IsNormal b) :
    (2 : ℝ) ^ (-(1077 : ℤ)) ≤ (2 : ℝ) ^ (addPipeline a b).ex'.toInt :=
  zpow_le_zpow_right₀ (by norm_num) (addPipeline_ex'_ge' a b ha hb)

/-- The pre-rounding working value `± zu * 2 ^ ex'` is within relative `(2/3) * 2 ^ (-54)` of the
exact sum, and its magnitude stays at or above the smallest normal magnitude. The three branches
are: matching signs (no cancellation), differing signs with an exponent gap of at most `3` (where
the `× 8` scaling of the significands makes the alignment shift exact, so the working value is the
exact sum), and differing signs with a larger gap (where cancellation is bounded away by the
leading bits of the two significands). -/
private theorem addPipeline_pre_round (a b : FPR) (ha : FPR.IsNormal a) (hb : FPR.IsNormal b)
    (hmin : FPR.minNormalReal ≤ |toReal a + toReal b|) :
    |(if (addPipeline a b).sx.toNat = 1 then (-1 : ℝ) else 1) *
          (((addPipeline a b).zu.toNat : ℝ) * (2 : ℝ) ^ (addPipeline a b).ex'.toInt)
        - (toReal a + toReal b)|
      ≤ 2 / 3 * (2 : ℝ) ^ (-(54 : ℤ)) * |toReal a + toReal b|
    ∧ FPR.minNormalReal ≤
        ((addPipeline a b).zu.toNat : ℝ) * (2 : ℝ) ^ (addPipeline a b).ex'.toInt := by
  have hp : (0 : ℝ) < (2 : ℝ) ^ (addPipeline a b).ex'.toInt := zpow_pos (by norm_num) _
  have hS := addPipeline_S_eq a b ha hb
  have hzr := addPipeline_zu_real a b ha hb
  have hal := addPipeline_align_lt a b ha hb
  have hxm := addPipeline_xu_mem a b ha hb
  have hym := addPipeline_yuRaw_mem a b ha hb
  have hYple := addPipeline_Yprime_le_xu a b ha hb
  have hYpnn : (0 : ℝ) ≤ ((addPipeline a b).yu_.toNat : ℝ) / 2 ^ (addPipeline a b).n.toNat := by
    positivity
  have hYvnn : (0 : ℝ) ≤ ((addPipeline a b).yu.toNat : ℝ) := by positivity
  have hX55 : (2 : ℝ) ^ (55 : ℕ) ≤ ((addPipeline a b).xu.toNat : ℝ) := by exact_mod_cast hxm.1
  have hpge := addPipeline_p_ge a b ha hb
  -- the two abs computations
  have hdiff : (if (addPipeline a b).sx.toNat = 1 then (-1 : ℝ) else 1) *
        (((addPipeline a b).zu.toNat : ℝ) * (2 : ℝ) ^ (addPipeline a b).ex'.toInt)
        - (toReal a + toReal b)
      = ((if (addPipeline a b).sx.toNat = 1 then (-1 : ℝ) else 1) *
          (if (addPipeline a b).sx = (addPipeline a b).sy then (1 : ℝ) else -1)) *
        ((((addPipeline a b).yu.toNat : ℝ)
            - ((addPipeline a b).yu_.toNat : ℝ) / 2 ^ (addPipeline a b).n.toNat) *
          (2 : ℝ) ^ (addPipeline a b).ex'.toInt) := by
    rw [hzr, hS]; ring
  have habsdiff : |(if (addPipeline a b).sx.toNat = 1 then (-1 : ℝ) else 1) *
        (((addPipeline a b).zu.toNat : ℝ) * (2 : ℝ) ^ (addPipeline a b).ex'.toInt)
        - (toReal a + toReal b)|
      = |((addPipeline a b).yu.toNat : ℝ)
          - ((addPipeline a b).yu_.toNat : ℝ) / 2 ^ (addPipeline a b).n.toNat| *
        (2 : ℝ) ^ (addPipeline a b).ex'.toInt := by
    rw [hdiff, abs_mul, addPipeline_abs_sigma_tau, one_mul, abs_mul, abs_of_pos hp]
  have habsS : |toReal a + toReal b|
      = |((addPipeline a b).xu.toNat : ℝ)
          + (if (addPipeline a b).sx = (addPipeline a b).sy then (1 : ℝ) else -1) *
            (((addPipeline a b).yu_.toNat : ℝ) / 2 ^ (addPipeline a b).n.toNat)| *
        (2 : ℝ) ^ (addPipeline a b).ex'.toInt := by
    rw [hS, abs_mul, abs_mul, addPipeline_abs_sigma, one_mul, abs_of_pos hp]
  have hc55 : (2 : ℝ) ^ (-(54 : ℤ)) * (2 : ℝ) ^ (55 : ℕ) = 2 := by
    rw [mul_comm, two_pow_mul_zpow]; norm_num
  have hc52 : (2 : ℝ) ^ (-(54 : ℤ)) * (2 : ℝ) ^ (52 : ℕ) = 1 / 4 := by
    rw [mul_comm, two_pow_mul_zpow]; norm_num
  have hmn : FPR.minNormalReal = (2 : ℝ) ^ (-(1022 : ℤ)) := rfl
  by_cases hs : (addPipeline a b).sx = (addPipeline a b).sy
  · -- matching signs: no cancellation
    rw [if_pos hs] at habsS hzr
    rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ ((addPipeline a b).xu.toNat : ℝ)
      + 1 * (((addPipeline a b).yu_.toNat : ℝ) / 2 ^ (addPipeline a b).n.toNat))] at habsS
    rw [abs_lt] at hal
    constructor
    · rw [habsdiff, habsS]
      have hbig : (1 : ℝ) ≤ 2 / 3 * (2 : ℝ) ^ (-(54 : ℤ)) *
          (((addPipeline a b).xu.toNat : ℝ)
            + 1 * (((addPipeline a b).yu_.toNat : ℝ) / 2 ^ (addPipeline a b).n.toNat)) := by
        have hpos : (0 : ℝ) < (2 : ℝ) ^ (-(54 : ℤ)) := zpow_pos (by norm_num) _
        nlinarith [hc55]
      have hsmall : |((addPipeline a b).yu.toNat : ℝ)
          - ((addPipeline a b).yu_.toNat : ℝ) / 2 ^ (addPipeline a b).n.toNat| ≤ 1 := by
        rw [abs_le]; constructor <;> linarith
      nlinarith
    · rw [hzr, hmn]
      have : (2 : ℝ) ^ (-(1022 : ℤ)) = (2 : ℝ) ^ (55 : ℕ) * (2 : ℝ) ^ (-(1077 : ℤ)) := by
        rw [two_pow_mul_zpow]; norm_num
      rw [this]
      nlinarith
  · -- differing signs: cancellation
    rw [if_neg hs] at habsS hzr
    have hYleX : (((addPipeline a b).yu_.toNat : ℝ) / 2 ^ (addPipeline a b).n.toNat)
        ≤ ((addPipeline a b).xu.toNat : ℝ) := hYple
    rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ ((addPipeline a b).xu.toNat : ℝ)
      + -1 * (((addPipeline a b).yu_.toNat : ℝ) / 2 ^ (addPipeline a b).n.toNat))] at habsS
    by_cases hn : (addPipeline a b).n.toNat ≤ 3
    · -- exact alignment: the working value *is* the exact sum
      have hex := addPipeline_align_exact a b hn
      constructor
      · rw [habsdiff, hex, sub_self, abs_zero, zero_mul]
        have : (0 : ℝ) ≤ |toReal a + toReal b| := abs_nonneg _
        have hpos : (0 : ℝ) < (2 : ℝ) ^ (-(54 : ℤ)) := zpow_pos (by norm_num) _
        nlinarith
      · rw [hzr, hex]
        rw [habsS] at hmin
        linarith
    · -- gap of at least 4: cancellation bounded away
      push Not at hn
      have hYplt : (((addPipeline a b).yu_.toNat : ℝ) / 2 ^ (addPipeline a b).n.toNat)
          < (2 : ℝ) ^ (52 : ℕ) := by
        have hpn : (0 : ℝ) < (2 : ℝ) ^ (addPipeline a b).n.toNat := by positivity
        rw [div_lt_iff₀ hpn]
        have h1 : ((addPipeline a b).yu_.toNat : ℝ) < (2 : ℝ) ^ (56 : ℕ) := by exact_mod_cast hym.2
        have h2 : (2 : ℝ) ^ (4 : ℕ) ≤ (2 : ℝ) ^ (addPipeline a b).n.toNat := by
          exact_mod_cast Nat.pow_le_pow_right (by norm_num : 1 ≤ 2) (by omega)
        nlinarith
      rw [abs_lt] at hal
      constructor
      · rw [habsdiff, habsS]
        have hbig : (1 : ℝ) ≤ 2 / 3 * (2 : ℝ) ^ (-(54 : ℤ)) *
            (((addPipeline a b).xu.toNat : ℝ)
              + -1 * (((addPipeline a b).yu_.toNat : ℝ) / 2 ^ (addPipeline a b).n.toNat)) := by
          have hpos : (0 : ℝ) < (2 : ℝ) ^ (-(54 : ℤ)) := zpow_pos (by norm_num) _
          nlinarith [hc55, hc52]
        have hsmall : |((addPipeline a b).yu.toNat : ℝ)
            - ((addPipeline a b).yu_.toNat : ℝ) / 2 ^ (addPipeline a b).n.toNat| ≤ 1 := by
          rw [abs_le]; constructor <;> linarith
        nlinarith
      · rw [hzr, hmn]
        have hpge4 : (2 : ℝ) ^ (-(1073 : ℤ)) ≤ (2 : ℝ) ^ (addPipeline a b).ex'.toInt := by
          refine zpow_le_zpow_right₀ (by norm_num) ?_
          have := addPipeline_ex'_ge a b ha hb
          omega
        have hkey : (2 : ℝ) ^ (54 : ℕ) ≤ ((addPipeline a b).xu.toNat : ℝ)
            + -1 * ((addPipeline a b).yu.toNat : ℝ) := by
          have h55 : (2 : ℝ) ^ (55 : ℕ) = 2 * (2 : ℝ) ^ (54 : ℕ) := by norm_num
          have h52 : (2 : ℝ) ^ (52 : ℕ) = (2 : ℝ) ^ (54 : ℕ) / 4 := by norm_num
          have h54 : (1 : ℝ) ≤ (2 : ℝ) ^ (54 : ℕ) := by norm_num
          nlinarith
        have hlow : (2 : ℝ) ^ (-(1022 : ℤ)) ≤ (2 : ℝ) ^ (54 : ℕ) * (2 : ℝ) ^ (-(1073 : ℤ)) := by
          rw [two_pow_mul_zpow]
          exact zpow_le_zpow_right₀ (by norm_num) (by norm_num)
        have hpos54 : (0 : ℝ) < (2 : ℝ) ^ (54 : ℕ) := by positivity
        calc (2 : ℝ) ^ (-(1022 : ℤ))
            ≤ (2 : ℝ) ^ (54 : ℕ) * (2 : ℝ) ^ (-(1073 : ℤ)) := hlow
          _ ≤ (2 : ℝ) ^ (54 : ℕ) * (2 : ℝ) ^ (addPipeline a b).ex'.toInt :=
              mul_le_mul_of_nonneg_left hpge4 hpos54.le
          _ ≤ (((addPipeline a b).xu.toNat : ℝ) + -1 * ((addPipeline a b).yu.toNat : ℝ)) *
                (2 : ℝ) ^ (addPipeline a b).ex'.toInt :=
              mul_le_mul_of_nonneg_right hkey hp.le

/-! ## (IX) Absolute error forms and the exponent window -/

/-- The alignment error, in absolute terms: the pre-rounding working value is within one ulp at
the working scale `2 ^ ex'` of the exact sum, unconditionally. -/
private theorem addPipeline_pre_round_abs (a b : FPR) (ha : FPR.IsNormal a) (hb : FPR.IsNormal b) :
    |(if (addPipeline a b).sx.toNat = 1 then (-1 : ℝ) else 1) *
          (((addPipeline a b).zu.toNat : ℝ) * (2 : ℝ) ^ (addPipeline a b).ex'.toInt)
        - (toReal a + toReal b)|
      ≤ (2 : ℝ) ^ (addPipeline a b).ex'.toInt := by
  have hp : (0 : ℝ) < (2 : ℝ) ^ (addPipeline a b).ex'.toInt := zpow_pos (by norm_num) _
  have hS := addPipeline_S_eq a b ha hb
  have hzr := addPipeline_zu_real a b ha hb
  have hal := addPipeline_align_lt a b ha hb
  have hdiff : (if (addPipeline a b).sx.toNat = 1 then (-1 : ℝ) else 1) *
        (((addPipeline a b).zu.toNat : ℝ) * (2 : ℝ) ^ (addPipeline a b).ex'.toInt)
        - (toReal a + toReal b)
      = ((if (addPipeline a b).sx.toNat = 1 then (-1 : ℝ) else 1) *
          (if (addPipeline a b).sx = (addPipeline a b).sy then (1 : ℝ) else -1)) *
        ((((addPipeline a b).yu.toNat : ℝ)
            - ((addPipeline a b).yu_.toNat : ℝ) / 2 ^ (addPipeline a b).n.toNat) *
          (2 : ℝ) ^ (addPipeline a b).ex'.toInt) := by
    rw [hzr, hS]; ring
  rw [hdiff, abs_mul, addPipeline_abs_sigma_tau, one_mul, abs_mul, abs_of_pos hp]
  nlinarith [hal.le]

/-- The rounding fold's contribution, as a difference at the post-renormalisation scale. -/
private theorem addPipeline_fold_diff_eq (a b : FPR) (hzu : (addPipeline a b).zu ≠ 0)
    (hb31 : -(2 ^ 31 : ℤ) + 63 ≤ (addPipeline a b).ex'.toInt) :
    ((addPipeline a b).zu''.toNat : ℝ) * (2 : ℝ) ^ (addPipeline a b).ex'''.toInt
        - ((addPipeline a b).zu.toNat : ℝ) * (2 : ℝ) ^ (addPipeline a b).ex'.toInt
      = (2 : ℝ) ^ (addPipeline a b).ex''.toInt *
        (((addPipeline a b).zu''.toNat : ℝ) * 2 ^ (9 : ℕ)
          - ((addPipeline a b).zu'.toNat : ℝ)) := by
  have hren := addPipeline_renorm_value_preserving a b hzu hb31
  have hsplit : (2 : ℝ) ^ (addPipeline a b).ex'''.toInt
      = (2 : ℝ) ^ (addPipeline a b).ex''.toInt * 2 ^ (9 : ℕ) := by
    rw [addPipeline_ex'''_eq_ex''_add, zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
    norm_num
  rw [← hren, hsplit]
  ring

private theorem addPipeline_fold_abs_error (a b : FPR) (hzu : (addPipeline a b).zu ≠ 0)
    (hb31 : -(2 ^ 31 : ℤ) + 63 ≤ (addPipeline a b).ex'.toInt) :
    |((addPipeline a b).zu''.toNat : ℝ) * (2 : ℝ) ^ (addPipeline a b).ex'''.toInt
        - ((addPipeline a b).zu.toNat : ℝ) * (2 : ℝ) ^ (addPipeline a b).ex'.toInt|
      ≤ (2 : ℝ) ^ (9 : ℕ) * (2 : ℝ) ^ (addPipeline a b).ex''.toInt := by
  have hq : (0 : ℝ) < (2 : ℝ) ^ (addPipeline a b).ex''.toInt := zpow_pos (by norm_num) _
  rw [addPipeline_fold_diff_eq a b hzu hb31, abs_mul, abs_of_pos hq]
  have hf := addPipeline_fold_abs_lt a b
  nlinarith [hf.le]

/-- The final exponent handed to the assembly stays inside the window the encoder needs: the
lower end comes from the result not underflowing into the subnormal band, the upper end from it
not overflowing past the largest finite magnitude. -/
private theorem addPipeline_ex'''_window (a b : FPR) (hzu : (addPipeline a b).zu ≠ 0)
    (hb31 : -(2 ^ 31 : ℤ) + 63 ≤ (addPipeline a b).ex'.toInt)
    (hlo : FPR.minNormalReal ≤
      ((addPipeline a b).zu.toNat : ℝ) * (2 : ℝ) ^ (addPipeline a b).ex'.toInt)
    (hhi : ((addPipeline a b).zu.toNat : ℝ) * (2 : ℝ) ^ (addPipeline a b).ex'.toInt
      < (2 : ℝ) ^ (1024 : ℤ)) :
    -1076 ≤ (addPipeline a b).ex'''.toInt ∧ (addPipeline a b).ex'''.toInt ≤ 969 := by
  have hren := addPipeline_renorm_value_preserving a b hzu hb31
  have hq : (0 : ℝ) < (2 : ℝ) ^ (addPipeline a b).ex''.toInt := zpow_pos (by norm_num) _
  have h63 : (2 : ℝ) ^ (63 : ℕ) ≤ ((addPipeline a b).zu'.toNat : ℝ) := by
    exact_mod_cast addPipeline_zu'_ge a b hzu
  have h64 : ((addPipeline a b).zu'.toNat : ℝ) < (2 : ℝ) ^ (64 : ℕ) := by
    exact_mod_cast (addPipeline a b).zu'.toNat_lt_size
  rw [← hren] at hlo hhi
  have hup : (2 : ℝ) ^ (((63 : ℕ) : ℤ) + (addPipeline a b).ex''.toInt) < (2 : ℝ) ^ (1024 : ℤ) := by
    rw [← two_pow_mul_zpow]
    have hmul : (2 : ℝ) ^ (63 : ℕ) * (2 : ℝ) ^ (addPipeline a b).ex''.toInt
        ≤ ((addPipeline a b).zu'.toNat : ℝ) * (2 : ℝ) ^ (addPipeline a b).ex''.toInt :=
      mul_le_mul_of_nonneg_right h63 hq.le
    linarith
  have hdown : (2 : ℝ) ^ (-(1022 : ℤ))
      < (2 : ℝ) ^ (((64 : ℕ) : ℤ) + (addPipeline a b).ex''.toInt) := by
    rw [← two_pow_mul_zpow]
    have hmn : FPR.minNormalReal = (2 : ℝ) ^ (-(1022 : ℤ)) := rfl
    rw [hmn] at hlo
    have hmul : ((addPipeline a b).zu'.toNat : ℝ) * (2 : ℝ) ^ (addPipeline a b).ex''.toInt
        < (2 : ℝ) ^ (64 : ℕ) * (2 : ℝ) ^ (addPipeline a b).ex''.toInt :=
      mul_lt_mul_of_pos_right h64 hq
    linarith
  have hup' := (zpow_lt_zpow_iff_right₀ (by norm_num : (1 : ℝ) < 2)).mp hup
  have hdown' := (zpow_lt_zpow_iff_right₀ (by norm_num : (1 : ℝ) < 2)).mp hdown
  have hE := addPipeline_ex'''_eq_ex''_add a b
  omega

/-! ## (X) Ruling out overflow at the top exponent -/

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

private theorem addPipeline_abs_pre_round (a b : FPR) :
    |(if (addPipeline a b).sx.toNat = 1 then (-1 : ℝ) else 1) *
        (((addPipeline a b).zu.toNat : ℝ) * (2 : ℝ) ^ (addPipeline a b).ex'.toInt)|
      = ((addPipeline a b).zu.toNat : ℝ) * (2 : ℝ) ^ (addPipeline a b).ex'.toInt := by
  rw [abs_mul, addPipeline_abs_sigma, one_mul, abs_of_nonneg (by positivity)]

/-- Abstract shape of the "no overflow" step: a value within relative `2 / 3 * E` of a quantity
bounded by `P - 2 * Q`, with `E` times that quantity below `Q`, stays below `P`. -/
private theorem lt_top_aux {S B P Q E : ℝ} (hQ : 0 < Q) (hmax : S ≤ P - 2 * Q)
    (hgap : B - S ≤ 2 / 3 * E * S) (hES : E * S ≤ Q) : B < P := by linarith

private theorem two_zpow_pos (m : ℤ) : (0 : ℝ) < (2 : ℝ) ^ m := zpow_pos (by norm_num) _

private theorem addPipeline_pre_round_lt (a b : FPR) (ha : FPR.IsNormal a) (hb : FPR.IsNormal b)
    (hmin : FPR.minNormalReal ≤ |toReal a + toReal b|)
    (hmax : |toReal a + toReal b| ≤ FPR.maxFiniteReal) :
    ((addPipeline a b).zu.toNat : ℝ) * (2 : ℝ) ^ (addPipeline a b).ex'.toInt
      < (2 : ℝ) ^ (1024 : ℤ) := by
  have h1 := (addPipeline_pre_round a b ha hb hmin).1
  have hgap := abs_sub_abs_le_abs_sub
    ((if (addPipeline a b).sx.toNat = 1 then (-1 : ℝ) else 1) *
      (((addPipeline a b).zu.toNat : ℝ) * (2 : ℝ) ^ (addPipeline a b).ex'.toInt))
    (toReal a + toReal b)
  rw [addPipeline_abs_pre_round] at hgap
  have h971 : (2 : ℝ) ^ (971 : ℤ) = 2 * (2 : ℝ) ^ (970 : ℤ) := by
    rw [show (971 : ℤ) = 970 + 1 from by norm_num, zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
    ring
  have hprod : (2 : ℝ) ^ (-(54 : ℤ)) * (2 : ℝ) ^ (1024 : ℤ) = (2 : ℝ) ^ (970 : ℤ) := by
    rw [← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
    norm_num
  rw [maxFiniteReal_eq, h971] at hmax
  have hSle : |toReal a + toReal b| ≤ (2 : ℝ) ^ (1024 : ℤ) :=
    hmax.trans (sub_le_self _ (by positivity))
  have hES : (2 : ℝ) ^ (-(54 : ℤ)) * |toReal a + toReal b| ≤ (2 : ℝ) ^ (970 : ℤ) := by
    have h := mul_le_mul_of_nonneg_left hSle (two_zpow_pos (-(54 : ℤ))).le
    rwa [hprod] at h
  exact lt_top_aux (two_zpow_pos (970 : ℤ)) hmax (hgap.trans h1) hES

/-- Abstract shape of the "no carry at the top exponent" contradiction. -/
private theorem no_carry_aux {S B W P U : ℝ} (hP : 0 < P) (hWge : (U - 2) * P ≤ W)
    (hfold : W - B ≤ P) (halign : B - S ≤ P / 2) (hmax : S ≤ U * P - 4 * P) : False := by
  linarith

/-- At the very top of the exponent range the final rounding cannot carry out of the mantissa
field: a carry there would force the exact sum past the largest finite magnitude, which the
result-range hypothesis of `add_error` excludes. -/
private theorem addPipeline_no_carry (a b : FPR) (ha : FPR.IsNormal a) (hb : FPR.IsNormal b)
    (hzu : (addPipeline a b).zu ≠ 0)
    (hb31 : -(2 ^ 31 : ℤ) + 63 ≤ (addPipeline a b).ex'.toInt)
    (hmax : |toReal a + toReal b| ≤ FPR.maxFiniteReal)
    (hex : (addPipeline a b).ex'''.toInt = 969) :
    roundQuarterTiesEven (addPipeline a b).zu''.toNat < 2 ^ 53 := by
  by_contra hc
  push Not at hc
  have hmem := addPipeline_zu''_mem a b hzu
  have hhi := (roundQuarterTiesEven_mem_of_normalized (addPipeline a b).zu''.toNat
    hmem.1 hmem.2).2
  have heq : roundQuarterTiesEven (addPipeline a b).zu''.toNat = 2 ^ 53 := by omega
  have h4 := four_mul_roundQuarterTiesEven_le (addPipeline a b).zu''.toNat
  rw [heq] at h4
  have hzuge : (2 : ℝ) ^ (55 : ℕ) - 2 ≤ ((addPipeline a b).zu''.toNat : ℝ) := by
    have hn : (2 : ℕ) ^ 55 ≤ (addPipeline a b).zu''.toNat + 2 := by omega
    have hR : (((2 : ℕ) ^ 55 : ℕ) : ℝ) ≤ (((addPipeline a b).zu''.toNat + 2 : ℕ) : ℝ) := by
      exact_mod_cast hn
    push_cast at hR
    linarith
  have hex2 : (addPipeline a b).ex''.toInt = 960 := by
    have := addPipeline_ex'''_eq_ex''_add a b
    omega
  have hq := two_zpow_pos (969 : ℤ)
  have e1 : (2 : ℝ) ^ (9 : ℕ) * (2 : ℝ) ^ (960 : ℤ) = (2 : ℝ) ^ (969 : ℤ) := by
    rw [two_pow_mul_zpow]; norm_num
  have eA : (2 : ℝ) ^ (55 : ℕ) * (2 : ℝ) ^ (969 : ℤ) = (2 : ℝ) ^ (1024 : ℤ) := by
    rw [two_pow_mul_zpow]; norm_num
  have eB : (4 : ℝ) * (2 : ℝ) ^ (969 : ℤ) = (2 : ℝ) ^ (971 : ℤ) := by
    rw [show (971 : ℤ) = 2 + 969 from by norm_num, zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
    norm_num
  have e3 : FPR.maxFiniteReal
      = (2 : ℝ) ^ (55 : ℕ) * (2 : ℝ) ^ (969 : ℤ) - 4 * (2 : ℝ) ^ (969 : ℤ) := by
    rw [maxFiniteReal_eq, eA, eB]
  have hexle : (2 : ℝ) ^ (addPipeline a b).ex'.toInt ≤ (2 : ℝ) ^ (969 : ℤ) / 2 := by
    have h968 : (2 : ℝ) ^ (addPipeline a b).ex'.toInt ≤ (2 : ℝ) ^ (968 : ℤ) :=
      zpow_le_zpow_right₀ (by norm_num) (addPipeline_ex'_le a b ha hb)
    have hsplit : (2 : ℝ) ^ (969 : ℤ) = 2 * (2 : ℝ) ^ (968 : ℤ) := by
      rw [show (969 : ℤ) = 968 + 1 from by norm_num, zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
      ring
    rw [hsplit]
    linarith
  have hfold := addPipeline_fold_abs_error a b hzu hb31
  rw [hex, hex2, e1] at hfold
  have halign := addPipeline_pre_round_abs a b ha hb
  have hgap := abs_sub_abs_le_abs_sub
    ((if (addPipeline a b).sx.toNat = 1 then (-1 : ℝ) else 1) *
      (((addPipeline a b).zu.toNat : ℝ) * (2 : ℝ) ^ (addPipeline a b).ex'.toInt))
    (toReal a + toReal b)
  rw [addPipeline_abs_pre_round] at hgap
  rw [e3] at hmax
  exact no_carry_aux hq (mul_le_mul_of_nonneg_right hzuge hq.le) (abs_le.mp hfold).2
    ((hgap.trans halign).trans hexle) hmax

/-! ## (XI) The error budget -/

private theorem add_error_combine {R W V S δ : ℝ} (hδ : 0 < δ) (hδ16 : δ ≤ 1 / 16)
    (h1 : |R - W| ≤ 2 * δ * |W|) (h2 : |W - V| ≤ δ * |V|)
    (h3 : |V - S| ≤ 2 / 3 * δ * |S|) : |R - S| ≤ 4 * δ * |S| := by
  have hSnn : (0 : ℝ) ≤ |S| := abs_nonneg _
  have hVnn : (0 : ℝ) ≤ |V| := abs_nonneg _
  have hV : |V| ≤ |S| + 2 / 3 * δ * |S| := by
    have := abs_sub_abs_le_abs_sub V S
    linarith
  have hW : |W| ≤ |V| + δ * |V| := by
    have := abs_sub_abs_le_abs_sub W V
    linarith
  have htri : |R - S| ≤ |R - W| + |W - V| + |V - S| := by
    calc |R - S| = |(R - W) + (W - V) + (V - S)| := by congr 1; ring
      _ ≤ |R - W| + |W - V| + |V - S| := abs_add_three _ _ _
  have hVS : |V| ≤ (1 + 2 / 3 * δ) * |S| := by linarith
  have hWS : |W| ≤ (1 + δ) * ((1 + 2 / 3 * δ) * |S|) := by
    have h1' : (1 + δ) * |V| ≤ (1 + δ) * ((1 + 2 / 3 * δ) * |S|) :=
      mul_le_mul_of_nonneg_left hVS (by linarith)
    linarith
  have hrem : (0 : ℝ) ≤ 1 / 3 - 4 * δ - 4 / 3 * δ ^ 2 := by nlinarith
  have hkey := mul_nonneg (mul_nonneg hδ.le hSnn) hrem
  have hb1 : 2 * δ * |W| ≤ 2 * δ * ((1 + δ) * ((1 + 2 / 3 * δ) * |S|)) :=
    mul_le_mul_of_nonneg_left hWS (by linarith)
  have hb2 : δ * |V| ≤ δ * ((1 + 2 / 3 * δ) * |S|) :=
    mul_le_mul_of_nonneg_left hVS hδ.le
  nlinarith [hkey, hb1, hb2, htri, h1, h2, h3]

/-! ## (XII) The exact-cancellation branch -/

/-- When the exact sum is `0` the two operands have equal magnitudes and opposite signs, so their
exponent gap is `0`, the alignment shift is the identity, and the combined significand cancels
exactly. -/
private theorem addPipeline_zu_eq_zero_of_sum_eq_zero (a b : FPR) (ha : FPR.IsNormal a)
    (hb : FPR.IsNormal b) (h : toReal a + toReal b = 0) : (addPipeline a b).zu = 0 := by
  have hp : (0 : ℝ) < (2 : ℝ) ^ (addPipeline a b).ex'.toInt := zpow_pos (by norm_num) _
  have hS := addPipeline_S_eq a b ha hb
  have hxm := addPipeline_xu_mem a b ha hb
  have hym := addPipeline_yuRaw_mem a b ha hb
  have hX55 : (2 : ℝ) ^ (55 : ℕ) ≤ ((addPipeline a b).xu.toNat : ℝ) := by exact_mod_cast hxm.1
  have hYpnn : (0 : ℝ) ≤ ((addPipeline a b).yu_.toNat : ℝ) / 2 ^ (addPipeline a b).n.toNat := by
    positivity
  have hσne : (if (addPipeline a b).sx.toNat = 1 then (-1 : ℝ) else 1) ≠ 0 := by
    split_ifs <;> norm_num
  have hz : ((addPipeline a b).xu.toNat : ℝ)
      + (if (addPipeline a b).sx = (addPipeline a b).sy then (1 : ℝ) else -1) *
        (((addPipeline a b).yu_.toNat : ℝ) / 2 ^ (addPipeline a b).n.toNat) = 0 := by
    have hzero := hS.symm.trans h
    rcases mul_eq_zero.mp hzero with h' | h'
    · rcases mul_eq_zero.mp h' with h'' | h''
      · exact absurd h'' hσne
      · exact h''
    · exact absurd h' (ne_of_gt hp)
  by_cases hs : (addPipeline a b).sx = (addPipeline a b).sy
  · rw [if_pos hs] at hz
    exfalso
    have : (0 : ℝ) < (2 : ℝ) ^ (55 : ℕ) := by positivity
    linarith
  · rw [if_neg hs] at hz
    have hpn : (0 : ℝ) < (2 : ℝ) ^ (addPipeline a b).n.toNat := by positivity
    have hdiv : ((addPipeline a b).yu_.toNat : ℝ) / 2 ^ (addPipeline a b).n.toNat
        = ((addPipeline a b).xu.toNat : ℝ) := by linarith
    have heq := (div_eq_iff hpn.ne').mp hdiv
    have hy56 : ((addPipeline a b).yu_.toNat : ℝ) < (2 : ℝ) ^ (56 : ℕ) := by exact_mod_cast hym.2
    have h56 : (2 : ℝ) ^ (56 : ℕ) = 2 * (2 : ℝ) ^ (55 : ℕ) := by norm_num
    have h2n : (2 : ℝ) ^ (addPipeline a b).n.toNat < 2 := by nlinarith
    have hn0 : (addPipeline a b).n.toNat = 0 := by
      by_contra hne
      have hge : (2 : ℝ) ^ (1 : ℕ) ≤ (2 : ℝ) ^ (addPipeline a b).n.toNat :=
        pow_le_pow_right₀ (by norm_num) (by omega)
      rw [pow_one] at hge
      linarith
    have hexact := addPipeline_align_exact a b (by omega)
    have hyx : ((addPipeline a b).yu.toNat : ℝ) = ((addPipeline a b).xu.toNat : ℝ) := by
      rw [hexact, hdiv]
    have hnat : (addPipeline a b).yu.toNat = (addPipeline a b).xu.toNat := by exact_mod_cast hyx
    have huint : (addPipeline a b).yu = (addPipeline a b).xu := UInt64.toNat_inj.mp hnat
    rw [addPipeline_zu_eq_sub_of_sx_ne_sy a b hs, huint]
    simp

noncomputable section

/-! ## Verification-only concrete primitives -/

/-- Concrete primitive bundle restricted to the fields used by `Falcon.verify`.
The sampler and FFT bridge fields are dummy placeholders because verification never
invokes them. -/
def verifyPrimitives (p : Falcon.Params) (hn : p.n = 2 ^ p.logn) : Falcon.Primitives p where
  publicKeyBytes := fun h => Falcon.Concrete.publicKeyBytes p.logn h
  hashToPoint := fun salt pkBytes msg => Falcon.Concrete.hashToPoint p.n salt pkBytes msg
  samplerZ := fun _ _ => pure 0
  fftTarget := fun _ => 0
  fftInt := fun _ => 0
  ifftRound := fun _ => 0
  compress := Falcon.Concrete.compress p.n
  decompress := Falcon.Concrete.decompress p.n
  nttOps := hn ▸ Falcon.Concrete.concreteNTTRingOps p.logn

/-! ## Per-operation error bounds -/

/-- Relative error bound for `FPR.add`, on normal (non-subnormal, finite) operands whose exact
sum stays in the correctly-rounded binary64 magnitude window (`FPR.InNormalMagnitudeRange`):
neither overflowing past `FPR.maxFiniteReal` nor underflowing into the open subnormal band below
`FPR.minNormalReal`. Both restrictions are load-bearing: two maximal-magnitude normal operands
overflow the exponent field on summation, and two normal operands whose exact difference is
subnormal (e.g. `2^-1022` and its next-representable neighbor) are mis-rounded by the alignment
step, in both cases producing a result unrelated to the true sum. -/
theorem add_error (a b : FPR) (ha : FPR.IsNormal a) (hb : FPR.IsNormal b)
    (hr : FPR.InNormalMagnitudeRange (toReal a + toReal b)) :
    |toReal (FPR.add a b) - (toReal a + toReal b)| ≤
    (2 : ℝ) ^ (-(52 : ℤ)) * |toReal a + toReal b| := by
  rcases hr with h0 | ⟨hmin, hmax⟩
  · rw [h0, add_toReal_eq_zero_of_zu_eq_zero' a b
      (addPipeline_zu_eq_zero_of_sum_eq_zero a b ha hb h0)]
    simp
  · obtain ⟨herr, hBmin⟩ := addPipeline_pre_round a b ha hb hmin
    have hmn : FPR.minNormalReal = (2 : ℝ) ^ (-(1022 : ℤ)) := rfl
    have hb31 : -(2 ^ 31 : ℤ) + 63 ≤ (addPipeline a b).ex'.toInt := by
      have := addPipeline_ex'_ge' a b ha hb
      omega
    have hzu : (addPipeline a b).zu ≠ 0 := by
      intro hc
      rw [hc, hmn] at hBmin
      have hz : (((0 : UInt64).toNat : ℝ)) * (2 : ℝ) ^ (addPipeline a b).ex'.toInt = 0 := by
        norm_num
      rw [hz] at hBmin
      exact absurd hBmin (not_le.mpr (two_zpow_pos (-(1022 : ℤ))))
    have hlt := addPipeline_pre_round_lt a b ha hb hmin hmax
    obtain ⟨he1, he2⟩ := addPipeline_ex'''_window a b hzu hb31 hBmin hlt
    have hmem := addPipeline_zu''_mem a b hzu
    have hs : ((addPipeline a b).sx.toUInt64).toNat ≤ 1 := by
      rcases addPipeline_sx_eq_zero_or_one a b with hc | hc <;> rw [hc] <;> decide
    have hδ : (0 : ℝ) < (2 : ℝ) ^ (-(54 : ℤ)) := two_zpow_pos _
    have hδ16 : (2 : ℝ) ^ (-(54 : ℤ)) ≤ 1 / 16 := by
      have h := zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2)
        (by norm_num : (-(54 : ℤ)) ≤ -(4 : ℤ))
      rw [show (2 : ℝ) ^ (-(4 : ℤ)) = 1 / 16 from by norm_num] at h
      exact h
    have h52 : (2 : ℝ) ^ (-(52 : ℤ)) = 4 * (2 : ℝ) ^ (-(54 : ℤ)) := by
      rw [show (-(52 : ℤ)) = 2 + -(54 : ℤ) from by norm_num,
        zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
      norm_num
    have h53 : (2 : ℝ) ^ (-(53 : ℤ)) = 2 * (2 : ℝ) ^ (-(54 : ℤ)) := by
      rw [show (-(53 : ℤ)) = 1 + -(54 : ℤ) from by norm_num,
        zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
      norm_num
    have hbase : toReal (FPR.add a b) =
        toRealBits (make_z ((addPipeline a b).sx.toUInt64) (addPipeline a b).ex'''
          (addPipeline a b).zu'') := by
      unfold toReal
      rw [add_eq_make_z]
    have hasm : |toRealBits (make_z ((addPipeline a b).sx.toUInt64) (addPipeline a b).ex'''
          (addPipeline a b).zu'') -
        (if ((addPipeline a b).sx.toUInt64).toNat = 1 then (-1 : ℝ) else 1) *
          ((addPipeline a b).zu''.toNat : ℝ) * (2 : ℝ) ^ (addPipeline a b).ex'''.toInt| ≤
        (2 : ℝ) ^ (-(53 : ℤ)) *
          |(if ((addPipeline a b).sx.toUInt64).toNat = 1 then (-1 : ℝ) else 1) *
            ((addPipeline a b).zu''.toNat : ℝ) * (2 : ℝ) ^ (addPipeline a b).ex'''.toInt| := by
      by_cases hcw : (addPipeline a b).ex'''.toInt ≤ 968
      · exact abs_toRealBits_make_z_sub_le _ _ _ hs he1 hcw hmem.1 hmem.2
      · exact abs_toRealBits_make_z_sub_le_of_no_carry _ _ _ hs he1 he2 hmem.1 hmem.2
          (addPipeline_no_carry a b ha hb hzu hb31 hmax (by omega))
    rw [UInt32.toNat_toUInt64, h53, ← hbase] at hasm
    have hfold : |(if (addPipeline a b).sx.toNat = 1 then (-1 : ℝ) else 1) *
          ((addPipeline a b).zu''.toNat : ℝ) * (2 : ℝ) ^ (addPipeline a b).ex'''.toInt
        - (if (addPipeline a b).sx.toNat = 1 then (-1 : ℝ) else 1) *
          (((addPipeline a b).zu.toNat : ℝ) * (2 : ℝ) ^ (addPipeline a b).ex'.toInt)|
      ≤ (2 : ℝ) ^ (-(54 : ℤ)) *
        |(if (addPipeline a b).sx.toNat = 1 then (-1 : ℝ) else 1) *
          (((addPipeline a b).zu.toNat : ℝ) * (2 : ℝ) ^ (addPipeline a b).ex'.toInt)| := by
      rw [show (if (addPipeline a b).sx.toNat = 1 then (-1 : ℝ) else 1) *
            ((addPipeline a b).zu''.toNat : ℝ) * (2 : ℝ) ^ (addPipeline a b).ex'''.toInt
          - (if (addPipeline a b).sx.toNat = 1 then (-1 : ℝ) else 1) *
            (((addPipeline a b).zu.toNat : ℝ) * (2 : ℝ) ^ (addPipeline a b).ex'.toInt)
        = (if (addPipeline a b).sx.toNat = 1 then (-1 : ℝ) else 1) *
            (((addPipeline a b).zu''.toNat : ℝ) * (2 : ℝ) ^ (addPipeline a b).ex'''.toInt
              - ((addPipeline a b).zu.toNat : ℝ) * (2 : ℝ) ^ (addPipeline a b).ex'.toInt)
        from by ring,
        abs_mul, addPipeline_abs_sigma, one_mul, addPipeline_abs_pre_round]
      exact addPipeline_fold_error a b hzu hb31
    rw [h52]
    exact add_error_combine hδ hδ16 hasm hfold herr

/-- Negation preserves normality: flipping the sign bit leaves the exponent field alone. -/
theorem FPR.isNormal_neg {b : FPR} (hb : FPR.IsNormal b) : FPR.IsNormal (FPR.neg b) := by
  unfold FPR.IsNormal FPR.Bits.IsNormal at hb ⊢
  rw [decode_neg_exponent]
  exact hb

/-- Relative error bound for `FPR.sub`, on the same domain as `add_error`. Subtraction is
addition against a negated operand, and negation is exact, so the bound transfers with no
further rounding analysis. -/
theorem sub_error (a b : FPR) (ha : FPR.IsNormal a) (hb : FPR.IsNormal b)
    (hr : FPR.InNormalMagnitudeRange (toReal a - toReal b)) :
    |toReal (FPR.sub a b) - (toReal a - toReal b)| ≤
    (2 : ℝ) ^ (-(52 : ℤ)) * |toReal a - toReal b| := by
  have hsum : toReal a + toReal (FPR.neg b) = toReal a - toReal b := by
    rw [toReal_neg]; ring
  have h := add_error a (FPR.neg b) ha (FPR.isNormal_neg hb) (by rw [hsum]; exact hr)
  rw [hsum] at h
  exact h

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
  · rw [if_pos h, if_pos ((mulPipeline_stickyWord_eq_zero_iff x y).mp h)]; rfl
  · rw [if_neg h, if_neg fun hc => h ((mulPipeline_stickyWord_eq_zero_iff x y).mpr hc)]; rfl

/-! ### Bracketing the sticky shift, and the renormalisation step -/

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

private theorem stickyShift_zero (v : ℕ) : stickyShift v 0 = v := by
  rw [stickyShift]
  norm_num [Nat.mod_one]

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

private theorem uint32_zero_and (w : UInt32) : (0 : UInt32) &&& w = 0 := by
  rw [← UInt32.toNat_inj, UInt32.toNat_and]; simp

private theorem uint32_xor_zero (w : UInt32) : w ^^^ (0 : UInt32) = w := by
  rw [← UInt32.toNat_inj, UInt32.toNat_xor]; simp

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

private theorem mulPipeline_abs_toReal_x (x y : FPR) (ha : FPR.IsNormal x) :
    |toReal x| = ((mulPipeline x y).xu.toNat : ℝ)
      * (2 : ℝ) ^ (((FPR.decode x).exponent : ℤ) - 1075) := by
  rw [mulPipeline_xu_toNat]
  change |(FPR.decode x).toReal| = _
  rw [abs_toReal_eq_significand_mul_two_zpow ha.1 ha.2]
  unfold FPR.Bits.significand
  rw [if_neg ha.1]

private theorem mulPipeline_abs_toReal_y (x y : FPR) (hb : FPR.IsNormal y) :
    |toReal y| = ((mulPipeline x y).yu.toNat : ℝ)
      * (2 : ℝ) ^ (((FPR.decode y).exponent : ℤ) - 1075) := by
  rw [mulPipeline_yu_toNat]
  change |(FPR.decode y).toReal| = _
  rw [abs_toReal_eq_significand_mul_two_zpow hb.1 hb.2]
  unfold FPR.Bits.significand
  rw [if_neg hb.1]

private theorem toNat_shiftRight_63_uint64 (w : UInt64) :
    (w >>> 63).toNat = w.toNat / 2 ^ 63 := by
  rw [UInt64.toNat_shiftRight, show (63 : UInt64).toNat % 64 = 63 from by decide,
    Nat.shiftRight_eq_div_pow]

private theorem div_two_pow_63_eq_testBit (n : ℕ) (hn : n < 2 ^ 64) :
    n / 2 ^ 63 = if n.testBit 63 then 1 else 0 := by
  rw [Nat.testBit_eq_decide_div_mod_eq]
  have h2 : n / 2 ^ 63 < 2 := by omega
  interval_cases h : (n / 2 ^ 63) <;> simp_all

/-- The sign word is the exclusive-or of the two operands' sign bits. -/
private theorem mulPipeline_s_toNat (x y : FPR) :
    (mulPipeline x y).s.toNat
      = if xor (FPR.decode x).sign (FPR.decode y).sign then 1 else 0 := by
  rw [mulPipeline_s, toNat_shiftRight_63_uint64, UInt64.toNat_xor,
    div_two_pow_63_eq_testBit _ (Nat.xor_lt_two_pow x.toNat_lt_size y.toNat_lt_size),
    Nat.testBit_xor]
  rfl

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

/-! ### Pinning the exponent from the result-range hypothesis

The exponent window `FPR.make`'s rounding analysis needs is not implied by the operands being
normal — the product of two normals ranges over roughly `[2 ^ -2044, 2 ^ 2046]`. It comes from
`mul_error`'s result-range hypothesis, which is exactly the statement that the exact product is
representable. -/

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
      unfold FPR.Bits.significand; rw [if_neg h.1]; omega
    exact_mod_cast this
  have hp : (0 : ℝ) < (2 : ℝ) ^ (((FPR.decode w).exponent : ℤ) - 1075) := zpow_pos (by norm_num) _
  nlinarith

/-- Relative error bound for `FPR.mul`, on normal operands whose exact product stays in the
correctly-rounded binary64 magnitude window (`FPR.InNormalMagnitudeRange`); see `add_error` for
why both the operand- and result-side restrictions are necessary. -/
theorem mul_error (a b : FPR) (ha : FPR.IsNormal a) (hb : FPR.IsNormal b)
    (hr : FPR.InNormalMagnitudeRange (toReal a * toReal b)) :
    |toReal (FPR.mul a b) - toReal a * toReal b| ≤
    (2 : ℝ) ^ (-(52 : ℤ)) * |toReal a * toReal b| := by
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
  rw [hQsign]
  refine mul_error_combine (by split_ifs <;> simp) hc (by rw [hWdef]; positivity) hK ?_
    hbr1 hbr2 hkey
  rw [show (if (mulPipeline a b).s.toNat = 1 then (-1 : ℝ) else 1) * (W * K * c)
      = (if (mulPipeline a b).s.toNat = 1 then (-1 : ℝ) else 1) * W
        * (2 : ℝ) ^ (mulPipeline a b).e'.toInt from by rw [he'I, hScale]; ring]
  exact hMV

/-- Relative error bound for `FPR.div`, on normal operands whose exact quotient stays in the
correctly-rounded binary64 magnitude window (`FPR.InNormalMagnitudeRange`); see `add_error` for
why both the operand- and result-side restrictions are necessary. -/
theorem div_error (a b : FPR) (hb : toReal b ≠ 0) (ha : FPR.IsNormal a) (hb' : FPR.IsNormal b)
    (hr : FPR.InNormalMagnitudeRange (toReal a / toReal b)) :
    |toReal (FPR.div a b) - toReal a / toReal b| ≤
    (2 : ℝ) ^ (-(52 : ℤ)) * |toReal a / toReal b| := by
  sorry

/-- Relative error bound for `FPR.sqrt`, on a normal, nonnegative operand. Unlike `add_error` /
`mul_error` / `div_error`, no separate magnitude-range hypothesis on the exact result is needed:
the square root of a value already bracketed in `[FPR.minNormalReal, FPR.maxFiniteReal]` lands in
`[2 ^ (-511), 2 ^ 512]`, hundreds of bits inside that same window on both ends, so a normal operand
can never drive `FPR.sqrt` to overflow or underflow. -/
theorem sqrt_error (a : FPR) (ha' : FPR.IsNormal a) (ha : 0 ≤ toReal a) :
    |toReal (FPR.sqrt a) - Real.sqrt (toReal a)| ≤
    (2 : ℝ) ^ (-(52 : ℤ)) * Real.sqrt (toReal a) := by
  sorry

/-! ## Non-vacuity witnesses for the per-operation error bounds

Concrete instances showing the domain hypotheses added to `add_error`, `mul_error`, `div_error`
and `sqrt_error` above are jointly satisfiable by ordinary values, not merely by a degenerate
operand such as zero. -/

/-- `toReal` is nonnegative whenever the sign bit is unset, uniformly across the
subnormal/normal/non-finite case split of `FPR.Bits.toReal`. -/
theorem FPR.Bits.toReal_nonneg_of_sign_false {b : FPR.Bits} (h : b.sign = false) :
    0 ≤ b.toReal := by
  unfold FPR.Bits.toReal
  simp only [h, Bool.false_eq_true, if_false]
  split_ifs <;> positivity

private theorem decode_two : FPR.decode FPR.two = ⟨false, 1024, 0⟩ := by
  unfold FPR.decode FPR.two; decide

/-- `toReal` of the `FPR` constant `2`. -/
theorem toReal_two : toReal FPR.two = 2 := by
  unfold toReal toRealBits
  rw [decode_two]
  simp [FPR.Bits.toReal]

/-- The bit pattern of the binary64 value `1.5`. -/
private def onePointFive : FPR := (0x3FF8000000000000 : UInt64)

private theorem decode_onePointFive :
    FPR.decode onePointFive = ⟨false, 1023, 2 ^ 51⟩ := by
  unfold FPR.decode onePointFive; decide

private theorem toReal_onePointFive : toReal onePointFive = 1.5 := by
  unfold toReal toRealBits
  rw [decode_onePointFive]
  norm_num [FPR.Bits.toReal]

/-- The bit pattern of the binary64 value `2.25`. -/
private def twoPointTwoFive : FPR := (0x4002000000000000 : UInt64)

private theorem decode_twoPointTwoFive :
    FPR.decode twoPointTwoFive = ⟨false, 1024, 2 ^ 49⟩ := by
  unfold FPR.decode twoPointTwoFive; decide

private theorem toReal_twoPointTwoFive : toReal twoPointTwoFive = 2.25 := by
  unfold toReal toRealBits
  rw [decode_twoPointTwoFive]
  norm_num [FPR.Bits.toReal]

private theorem FPR.minNormalReal_le_two_pow {k : ℤ} (hk : -1022 ≤ k) :
    FPR.minNormalReal ≤ (2 : ℝ) ^ k :=
  zpow_le_zpow_right₀ (by norm_num) hk

private theorem FPR.two_pow_le_maxFiniteReal {k : ℤ} (hk : k ≤ 1023) :
    (2 : ℝ) ^ k ≤ FPR.maxFiniteReal := by
  unfold FPR.maxFiniteReal
  have h1 : (2 : ℝ) ^ k ≤ (2 : ℝ) ^ (1023 : ℤ) := zpow_le_zpow_right₀ (by norm_num) hk
  have h2 : (2 : ℝ) ^ (-(52 : ℤ)) ≤ (1 : ℝ) := by
    calc (2 : ℝ) ^ (-(52 : ℤ)) ≤ (2 : ℝ) ^ (0 : ℤ) :=
          zpow_le_zpow_right₀ (by norm_num) (by omega)
      _ = 1 := by norm_num
  have h3 : (1 : ℝ) ≤ 2 - (2 : ℝ) ^ (-(52 : ℤ)) := by linarith
  calc (2 : ℝ) ^ k ≤ (2 : ℝ) ^ (1023 : ℤ) := h1
    _ = 1 * (2 : ℝ) ^ (1023 : ℤ) := (one_mul _).symm
    _ ≤ (2 - (2 : ℝ) ^ (-(52 : ℤ))) * (2 : ℝ) ^ (1023 : ℤ) :=
        mul_le_mul_of_nonneg_right h3 (le_of_lt (zpow_pos (by norm_num) _))

/-- Any positive real bracketed between two powers of two with exponents inside `[-1022, 1023]`
lands in `FPR.InNormalMagnitudeRange`: the reusable step behind the concrete witnesses below. -/
private theorem FPR.in_normal_range_of_pos_le {r : ℝ} {k1 k2 : ℤ}
    (hk1 : -1022 ≤ k1) (hk2 : k2 ≤ 1023)
    (hr0 : (2 : ℝ) ^ k1 ≤ r) (hr1 : r ≤ (2 : ℝ) ^ k2) :
    FPR.InNormalMagnitudeRange r := by
  right
  have hpos : 0 < r := lt_of_lt_of_le (zpow_pos (by norm_num) _) hr0
  rw [abs_of_pos hpos]
  exact ⟨(FPR.minNormalReal_le_two_pow hk1).trans hr0,
    hr1.trans (FPR.two_pow_le_maxFiniteReal hk2)⟩

private theorem isNormal_one : FPR.IsNormal FPR.one := by
  unfold FPR.IsNormal FPR.Bits.IsNormal FPR.decode FPR.one; decide

private theorem isNormal_two : FPR.IsNormal FPR.two := by
  unfold FPR.IsNormal FPR.Bits.IsNormal FPR.decode FPR.two; decide

private theorem isNormal_onePointFive : FPR.IsNormal onePointFive := by
  unfold FPR.IsNormal FPR.Bits.IsNormal FPR.decode onePointFive; decide

private theorem isNormal_twoPointTwoFive : FPR.IsNormal twoPointTwoFive := by
  unfold FPR.IsNormal FPR.Bits.IsNormal FPR.decode twoPointTwoFive; decide

private theorem isNormal_q : FPR.IsNormal FPR.q := by
  unfold FPR.IsNormal FPR.Bits.IsNormal FPR.decode FPR.q; decide

private theorem decode_q_sign_false : (FPR.decode FPR.q).sign = false := by
  unfold FPR.decode FPR.q; decide

/-- `add_error` is not vacuous: `1.0 + 1.0` is an ordinary witness satisfying every hypothesis. -/
example : FPR.IsNormal FPR.one ∧ FPR.IsNormal FPR.one ∧
    FPR.InNormalMagnitudeRange (toReal FPR.one + toReal FPR.one) := by
  refine ⟨isNormal_one, isNormal_one, ?_⟩
  rw [toReal_one]
  exact FPR.in_normal_range_of_pos_le (k1 := 0) (k2 := 1)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- `add_error` is not vacuous: `1.5 + 2.25` is a second, non-round-number witness. -/
example : FPR.IsNormal onePointFive ∧ FPR.IsNormal twoPointTwoFive ∧
    FPR.InNormalMagnitudeRange (toReal onePointFive + toReal twoPointTwoFive) := by
  refine ⟨isNormal_onePointFive, isNormal_twoPointTwoFive, ?_⟩
  rw [toReal_onePointFive, toReal_twoPointTwoFive]
  exact FPR.in_normal_range_of_pos_le (k1 := 0) (k2 := 2)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- `mul_error` is not vacuous: `2.0 * 2.0` is an ordinary witness. -/
example : FPR.IsNormal FPR.two ∧ FPR.IsNormal FPR.two ∧
    FPR.InNormalMagnitudeRange (toReal FPR.two * toReal FPR.two) := by
  refine ⟨isNormal_two, isNormal_two, ?_⟩
  rw [toReal_two]
  exact FPR.in_normal_range_of_pos_le (k1 := 0) (k2 := 2)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- `div_error` is not vacuous: `2.0 / 1.0` is an ordinary witness. -/
example : toReal FPR.one ≠ 0 ∧ FPR.IsNormal FPR.two ∧ FPR.IsNormal FPR.one ∧
    FPR.InNormalMagnitudeRange (toReal FPR.two / toReal FPR.one) := by
  refine ⟨by rw [toReal_one]; norm_num, isNormal_two, isNormal_one, ?_⟩
  rw [toReal_two, toReal_one, div_one]
  exact FPR.in_normal_range_of_pos_le (k1 := 0) (k2 := 1)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- `sqrt_error` is not vacuous: `FPR.q`, the Falcon modulus `12289` used throughout the concrete
NTT/FFT and rounding kernels (`FPR.q` in `LatticeCrypto/Falcon/Concrete/FPR.lean`), is a normal,
nonnegative operand — and, unlike `add_error` / `mul_error` / `div_error`, needs no further
magnitude side condition; see `sqrt_error`'s docstring for why. -/
example : FPR.IsNormal FPR.q ∧ 0 ≤ toReal FPR.q := by
  refine ⟨isNormal_q, ?_⟩
  unfold toReal toRealBits
  exact FPR.Bits.toReal_nonneg_of_sign_false decode_q_sign_false

/-! ## Sampler quality -/

/-- Absolute approximation bound for the FACCT-based `expm_p63` routine, on the domain the
routine is written for: `x` in `[0, log 2)` and `ccs` in `[0, 1)`.

Both sides of the `ccs` restriction are load-bearing. `expm_p63` reads its operands through a
fixed-point conversion that keeps `⌊2 ^ 63 * ccs⌋` in 63 bits and drops the sign bit, so the scale
factor must be a nonnegative fraction below one. At `ccs = 1` the conversion wraps to `0`, and with
it the whole product, for every `x` in range — against a true value of `Real.exp (-(toReal x))`,
never below one half. Above `1` the claim fails outright: the returned `UInt64` read at scale
`2 ^ 63` is smaller than `2`, while `toReal ccs * Real.exp (-(toReal x))` grows without bound. -/
theorem expm_p63_error (x ccs : FPR)
    (hx : 0 ≤ toReal x) (hx' : toReal x < Real.log 2)
    (hccs : 0 ≤ toReal ccs) (hccs' : toReal ccs < 1) :
    abs ((((FPR.expm_p63 x ccs).toNat : ℕ) : ℝ) / (2 : ℝ) ^ 63 -
      (toReal ccs * Real.exp (-(toReal x)))) ≤
    (2 : ℝ) ^ (-(51 : ℤ)) := by
  sorry

/-- The bit pattern of the binary64 value `0.5`. -/
private def half : FPR := (0x3FE0000000000000 : UInt64)

private theorem decode_half : FPR.decode half = ⟨false, 1022, 0⟩ := by
  unfold FPR.decode half; decide

private theorem toReal_half : toReal half = 0.5 := by
  unfold toReal toRealBits
  rw [decode_half]
  norm_num [FPR.Bits.toReal]

/-- `expm_p63_error` is not vacuous: `x = 0`, `ccs = 0.5` meets all four side conditions. -/
example : 0 ≤ toReal FPR.zero ∧ toReal FPR.zero < Real.log 2 ∧
    0 ≤ toReal half ∧ toReal half < 1 := by
  refine ⟨by rw [toReal_zero], ?_, by rw [toReal_half]; norm_num,
    by rw [toReal_half]; norm_num⟩
  rw [toReal_zero]
  exact Real.log_pos (by norm_num)

/-! ## End-to-end correctness -/

/-- The concrete Falcon verifier agrees with the abstract verifier once the concrete signature
codec, public-key codec, and fast arithmetic kernels are related to their specification-level
counterparts. The abstract verifier is instantiated with the same concrete verification fields. -/
theorem concrete_verify_eq_verify
    (p : Falcon.Params) (hn : p.n = 2 ^ p.logn) (hsbytelen : 0 < p.sbytelen)
    (hsigDecode : ∀ (salt : Bytes 40) (compSig : List Byte),
      compSig ≠ [] →
        Falcon.Concrete.sigDecode (Falcon.Concrete.sigEncode salt compSig p.logn) p.logn =
          some (salt, compSig))
    (hpkDecode : ∀ h : Falcon.Rq p.n,
      Falcon.Concrete.pkDecode p.n
        ((Falcon.Concrete.publicKeyBytes p.logn h).extract 1
          (Falcon.Concrete.publicKeyBytes p.logn h).size) = some h)
    (hmul : ∀ s2 h : Falcon.Rq p.n,
      Falcon.Concrete.negacyclicMulU32 s2 h = Falcon.negacyclicMul s2 h)
    (hnorm : ∀ s1 s2 : Falcon.Rq p.n,
      Falcon.Concrete.pairL2NormSqU32 s1 s2 = Falcon.pairL2NormSq s1 s2)
    (pk : Falcon.PublicKey p) (msg : List Falcon.Byte) (sig : Falcon.Signature) :
    let prims := verifyPrimitives p hn;
    Falcon.Concrete.concreteVerify p (prims.publicKeyBytes pk.h) msg
      (Falcon.Concrete.sigEncode sig.salt sig.compressedS2 p.logn) =
        Falcon.verify p prims pk msg sig := by
  dsimp
  by_cases hcomp : sig.compressedS2 = []
  · have hdecomp : (verifyPrimitives p hn).decompress [] p.sbytelen = none := by
      apply Falcon.Concrete.decompress_eq_none_of_length_ne
      simpa using Nat.ne_of_lt hsbytelen
    have hleft :
        Falcon.Concrete.concreteVerify p ((verifyPrimitives p hn).publicKeyBytes pk.h) msg
          (Falcon.Concrete.sigEncode sig.salt [] p.logn) = false := by
      exact Falcon.Concrete.concreteVerify_sigEncode_nil_eq_false p
        ((verifyPrimitives p hn).publicKeyBytes pk.h) sig.salt msg
    have hright : Falcon.verify p (verifyPrimitives p hn) pk msg sig = false := by
      simp [Falcon.verify, hcomp, hdecomp]
    simpa [hcomp] using hleft.trans hright.symm
  · simp [Falcon.Concrete.concreteVerify, Falcon.verify,
      hsigDecode sig.salt sig.compressedS2 hcomp, Falcon.Primitives.hashToPointForPublicKey,
      verifyPrimitives, hpkDecode, hmul, hnorm]
    rfl

end

end Falcon.Concrete.FPRBridge
