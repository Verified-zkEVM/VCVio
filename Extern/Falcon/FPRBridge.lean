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
