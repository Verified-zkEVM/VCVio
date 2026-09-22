/-
Copyright (c) 2026 Oleksandr Vovkotrub. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oleksandr Vovkotrub
-/

module
public import Extern.Falcon.Expm.FixedPoint
public import Extern.Falcon.Expm.Certificates

/-!
# Accuracy of Falcon's `expm_p63`

`Falcon.Concrete.FPR.expm_p63` evaluates a degree-twelve polynomial in `UInt64` fixed point and
scales the result, computing `⌊2 ^ 63 * ccs * exp (-x)⌋` for a scale factor `ccs` in `[0, 1)` and
an argument `x` in `[0, log 2)`. Its accuracy splits in two, and so does its proof:

* `Extern.Falcon.Expm.FixedPoint` bounds how faithfully the fixed-point pipeline evaluates the
  polynomial it is given;
* `Extern.Falcon.Expm.Certificates` bounds how well that polynomial approximates `exp (-x)`, by
  kernel-checked Chebyshev certificates (see `docs/agents/expm-certification.md`).

This module adds the two, with the Taylor truncation `abs_taylorExpNeg_sub_exp_le`, into
`expm_p63_error`. The two halves share no proof code and compile in parallel.
-/

public section

namespace Falcon.Concrete.FPRBridge

open Falcon.Concrete.FPR

/-! ## Assembly

The three error sources add in units of `2 ^ (-63)`: the fixed-point pipeline contributes `10`,
the certificates `3574`, and the Taylor truncation `80`. Their sum `3664` is under the `4096`
units that `2 ^ (-51)` allows. -/

/-- Absolute approximation bound for the FACCT-based `expm_p63` routine, on the domain the
routine is written for: `x` in `[0, 0.694]` and `ccs` in `[0, 1)`.

The routine is documented for `x` in `[0, log 2)`, and `0.694` is the smallest constant above
`log 2` that the proof already carries — it is the contraction factor of the Horner error
induction (`scaledArg_le_694`), and the Chebyshev certificates run to `89/128 = 0.6953125`.
Stating the hypothesis at `0.694` rather than `log 2` is what lets a caller feed a *computed*
reduction. A caller that reduces modulo `log 2` by rounding a floating-point quotient obtains a
remainder that can sit a few ulps above `log 2` when the argument is near a multiple of it, so no
statement closed at `log 2` would apply to one.

Both sides of the `ccs` restriction are load-bearing. `expm_p63` reads its operands through a
fixed-point conversion that keeps `⌊2 ^ 63 * ccs⌋` in 63 bits and drops the sign bit, so the scale
factor must be a nonnegative fraction below one. At `ccs = 1` the conversion wraps to `0`, and with
it the whole product, for every `x` in range — against a true value of `Real.exp (-(toReal x))`,
never below one half. Above `1` the claim fails outright: the returned `UInt64` read at scale
`2 ^ 63` is smaller than `2`, while `toReal ccs * Real.exp (-(toReal x))` grows without bound.

The `2 ^ (-51)` is very nearly saturated, and by the approximation rather than the arithmetic
around it. Measured in units of `2 ^ (-63)`, against a budget of `4096`: the fixed-point pipeline
costs `10` (`expm_p63_sub_trueArg_le`), the Chebyshev certificates covering `[0, 89/128]` cost
`3574` (`abs_certQ_le`), and the degree-`19` Taylor truncation of `Real.exp` costs `80`. That
`3574` is where the difficulty lies: `FPR.facctCoeffs` is a minimax fit rather than a Taylor
truncation, so `P - T` carries `O(1)` coefficients while being `O(2 ^ (-51))`, and any bound
applying a triangle inequality to those coefficients discards exactly the cancellation the fit
relies on. Subdividing restores locality, which is why the bound is a family of per-interval
certificates rather than a single estimate. -/
theorem expm_p63_error (x ccs : FPR)
    (hx : 0 ≤ toReal x) (hx' : toReal x ≤ 694 / 1000)
    (hccs : 0 ≤ toReal ccs) (hccs' : toReal ccs < 1) :
    abs ((((FPR.expm_p63 x ccs).toNat : ℕ) : ℝ) / (2 : ℝ) ^ 63 -
      (toReal ccs * Real.exp (-(toReal x)))) ≤
    (2 : ℝ) ^ (-(51 : ℤ)) := by
  have ht89 : toReal x ≤ 89 / 128 := by linarith
  have ht1 : toReal x ≤ 1 := by linarith
  have hmain := expm_p63_sub_trueArg_le x ccs hx hx' hccs hccs'
  have hQ := abs_certQ_le (toReal x) hx ht89
  have hT := abs_taylorExpNeg_sub_exp_le (toReal x) hx ht1
  have hc : |toReal ccs| ≤ 1 := by rw [abs_of_nonneg hccs]; linarith
  have hdef : hornerExact (toReal x) 12
      = certQ (toReal x) + 2 ^ 63 * taylorExpNeg 18 (toReal x) := by
    exact hornerExact_eq_certQ_add _
  have hB : |certQ (toReal x)
      + 2 ^ 63 * (taylorExpNeg 18 (toReal x) - Real.exp (-(toReal x)))| ≤ 3654 := by
    refine le_trans (abs_add_le _ _) ?_
    rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ 63)]
    nlinarith [abs_nonneg (taylorExpNeg 18 (toReal x) - Real.exp (-(toReal x)))]
  have key : |((expm_p63 x ccs).toNat : ℝ)
      - toReal ccs * ((2 : ℝ) ^ 63 * Real.exp (-(toReal x)))| ≤ 3664 := by
    have e1 : ((expm_p63 x ccs).toNat : ℝ)
        - toReal ccs * ((2 : ℝ) ^ 63 * Real.exp (-(toReal x)))
        = (((expm_p63 x ccs).toNat : ℝ) - toReal ccs * hornerExact (toReal x) 12)
          + toReal ccs * (certQ (toReal x)
            + 2 ^ 63 * (taylorExpNeg 18 (toReal x) - Real.exp (-(toReal x)))) := by
      rw [hdef]; ring
    rw [e1]
    refine le_trans (abs_add_le _ _) ?_
    rw [abs_mul]
    nlinarith [abs_nonneg (certQ (toReal x)
      + 2 ^ 63 * (taylorExpNeg 18 (toReal x) - Real.exp (-(toReal x)))), abs_nonneg (toReal ccs)]
  have hscale : (((FPR.expm_p63 x ccs).toNat : ℕ) : ℝ) / (2 : ℝ) ^ 63
      - toReal ccs * Real.exp (-(toReal x))
      = (((expm_p63 x ccs).toNat : ℝ)
        - toReal ccs * ((2 : ℝ) ^ 63 * Real.exp (-(toReal x)))) / (2 : ℝ) ^ 63 := by
    field_simp
  rw [hscale, abs_div, abs_of_pos (by positivity : (0 : ℝ) < (2 : ℝ) ^ 63),
    div_le_iff₀ (by positivity : (0 : ℝ) < (2 : ℝ) ^ 63)]
  refine le_trans key ?_
  norm_num

/-- `expm_p63_error` on the whole symmetric domain: the routine approximates `exp (-|x|)`.

This is the form a caller wants when the argument is *computed* rather than assumed nonnegative,
since it separates the approximation question from the sign question. Note that it is not an
extension of `expm_p63_error` to negative arguments in the naive sense — on `toReal x < 0` the
value approximated is `Real.exp (-|toReal x|)`, which is `Real.exp (toReal x)`, the reciprocal of
what an unwary reader of `expm_p63` might expect. -/
theorem expm_p63_error_abs (x ccs : FPR)
    (hx : |toReal x| ≤ 694 / 1000)
    (hccs : 0 ≤ toReal ccs) (hccs' : toReal ccs < 1) :
    abs ((((FPR.expm_p63 x ccs).toNat : ℕ) : ℝ) / (2 : ℝ) ^ 63 -
      (toReal ccs * Real.exp (-|toReal x|))) ≤ (2 : ℝ) ^ (-(51 : ℤ)) := by
  rcases le_or_gt 0 (toReal x) with h | h
  · rw [abs_of_nonneg h] at hx ⊢
    exact expm_p63_error x ccs h hx hccs hccs'
  · have hneg : toReal (FPR.neg x) = -toReal x := toReal_neg x
    have h0 : 0 ≤ toReal (FPR.neg x) := by rw [hneg]; linarith
    have habs : |toReal x| = toReal (FPR.neg x) := by
      rw [hneg, abs_of_neg h]
    rw [habs, ← expm_p63_neg x ccs]
    exact expm_p63_error _ ccs h0 (by rw [← habs]; exact hx) hccs hccs'

end Falcon.Concrete.FPRBridge
