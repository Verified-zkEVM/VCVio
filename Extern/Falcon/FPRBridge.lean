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
FPR.maxFiniteReal]`: the range a correctly-rounded binary64 operation can represent with
the standard `2^(-52)` relative-error guarantee, excluding both overflow (magnitude above
`maxFiniteReal`) and underflow into the subnormal range (nonzero magnitude strictly below
`minNormalReal`). -/
def FPR.ExactInNormalRange (r : ℝ) : Prop :=
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

/-- Relative error bound for `FPR.add`. -/
theorem add_error (a b : FPR) :
    |toReal (FPR.add a b) - (toReal a + toReal b)| ≤
    (2 : ℝ) ^ (-(52 : ℤ)) * |toReal a + toReal b| := by
  sorry

/-- Relative error bound for `FPR.mul`. -/
theorem mul_error (a b : FPR) :
    |toReal (FPR.mul a b) - toReal a * toReal b| ≤
    (2 : ℝ) ^ (-(52 : ℤ)) * |toReal a * toReal b| := by
  sorry

/-- Relative error bound for `FPR.div`. -/
theorem div_error (a b : FPR) (hb : toReal b ≠ 0) :
    |toReal (FPR.div a b) - toReal a / toReal b| ≤
    (2 : ℝ) ^ (-(52 : ℤ)) * |toReal a / toReal b| := by
  sorry

/-- Relative error bound for `FPR.sqrt`. -/
theorem sqrt_error (a : FPR) (ha : 0 ≤ toReal a) :
    |toReal (FPR.sqrt a) - Real.sqrt (toReal a)| ≤
    (2 : ℝ) ^ (-(52 : ℤ)) * Real.sqrt (toReal a) := by
  sorry

/-! ## Sampler quality -/

/-- Absolute approximation bound for the FACCT-based `expm_p63` routine. -/
theorem expm_p63_error (x ccs : FPR)
    (hx : 0 ≤ toReal x) (hx' : toReal x < Real.log 2) :
    abs ((((FPR.expm_p63 x ccs).toNat : ℕ) : ℝ) / (2 : ℝ) ^ 63 -
      (toReal ccs * Real.exp (-(toReal x)))) ≤
    (2 : ℝ) ^ (-(51 : ℤ)) := by
  sorry

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
