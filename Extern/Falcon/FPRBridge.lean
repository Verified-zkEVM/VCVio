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
