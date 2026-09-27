/-
Copyright (c) 2026 Oleksandr Vovkotrub. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oleksandr Vovkotrub
-/

module
import all LatticeCrypto.Falcon.Concrete.FPR
public import LatticeCrypto.Falcon.Concrete.FPR
public import Extern.Falcon.Expm.CertificateCore
public import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# The polynomial behind Falcon's `expm_p63`

`Falcon.Concrete.FPR.expm_p63` evaluates the FACCT coefficient table by Horner's rule. This module
names the exact real Horner value `hornerExact` of that table, the degree-18 Taylor truncation
`taylorExpNeg` of `exp (-x)`, and their scaled difference `certQ`, the quantity the Chebyshev
certificates in `Extern.Falcon.Expm.Certificates` bound.

Clearing `18!` makes `certQ` an integer polynomial, `certP`; `certQ_eval` records that once, so
the certificates never see the coefficient table or the factorials again.
-/

public section

namespace Falcon.Concrete.FPRBridge

open Falcon.Concrete.FPR

/-- The exact real Horner sequence on the FACCT coefficients at the argument `ζ`: the value
`expm_p63`'s loop would compute if `mulHi64` did not truncate. -/
noncomputable def hornerExact (ζ : ℝ) : ℕ → ℝ
  | 0 => ((facctCoeffs[0]!).toNat : ℝ)
  | (i + 1) => ((facctCoeffs[i + 1]!).toNat : ℝ) - ζ * hornerExact ζ i

/-- The degree-`n` Taylor truncation of `exp (-x)`. -/
noncomputable def taylorExpNeg (n : ℕ) (x : ℝ) : ℝ :=
  ∑ i ∈ Finset.range (n + 1), (-x) ^ i / (i.factorial : ℝ)

/-- The certification target, in units of `2 ^ (-63)`. -/
noncomputable def certQ (x : ℝ) : ℝ :=
  hornerExact x 12 - 2 ^ 63 * taylorExpNeg 18 x

/-- The Horner value splits as the certification target plus the scaled Taylor truncation. -/
theorem hornerExact_eq_certQ_add (x : ℝ) :
    hornerExact x 12 = certQ x + 2 ^ 63 * taylorExpNeg 18 x := by
  unfold certQ; ring

private theorem facctVal0 : (facctCoeffs[0]!).toNat = 19127174051 := by decide
private theorem facctVal1 : (facctCoeffs[1]!).toNat = 233346759686 := by decide
private theorem facctVal2 : (facctCoeffs[2]!).toNat = 2542029181962 := by decide
private theorem facctVal3 : (facctCoeffs[3]!).toNat = 25415798087749 := by decide
private theorem facctVal4 : (facctCoeffs[4]!).toNat = 228754078003076 := by decide
private theorem facctVal5 : (facctCoeffs[5]!).toNat = 1830034511206115 := by decide
private theorem facctVal6 : (facctCoeffs[6]!).toNat = 12810238987800554 := by decide
private theorem facctVal7 : (facctCoeffs[7]!).toNat = 76861433589428176 := by decide
private theorem facctVal8 : (facctCoeffs[8]!).toNat = 384307168197152512 := by decide
private theorem facctVal9 : (facctCoeffs[9]!).toNat = 1537228672812056320 := by decide
private theorem facctVal10 : (facctCoeffs[10]!).toNat = 4611686018427565056 := by decide
private theorem facctVal11 : (facctCoeffs[11]!).toNat = 9223372036854728704 := by decide
private theorem facctVal12 : (facctCoeffs[12]!).toNat = 9223372036854775808 := by decide

/-- `18! * certQ` has integer coefficients. -/
private theorem certQ_expand (x : ℝ) :
    (6402373705728000 : ℝ) * certQ x = 0 + 301577411034611712000 * x + 1134193306717126656000 * x
      ^ 2 + (-18739867347641696256000) * x ^ 3 + (-32842982000626237440000) * x ^ 4 +
      326702176168714253107200 * x ^ 5 + 305549933392096365772800 * x ^ 6 +
      (-2413115680306070554214400) * x ^ 7 + (-1208665697255858877235200) * x ^ 8 +
      8596251864142770040012800 * x ^ 9 + 2017429890733951881707520 * x ^ 10 +
      (-14609216358110315699896320) * x ^ 11 + (-821012305358570167664640) * x ^ 12 +
      9483102193412606294753280 * x ^ 13 + (-677364442386614735339520) * x ^ 14 +
      45157629492440982355968 * x ^ 15 + (-2822351843277561397248) * x ^ 16 +
      166020696663385964544 * x ^ 17 + (-9223372036854775808) * x ^ 18 := by
  unfold certQ taylorExpNeg
  simp only [hornerExact, Nat.reduceAdd, Finset.sum_range_succ, Finset.sum_range_zero, facctVal0,
    facctVal1, facctVal2, facctVal3, facctVal4, facctVal5, facctVal6, facctVal7, facctVal8,
    facctVal9, facctVal10, facctVal11, facctVal12]
  norm_num [Nat.factorial]
  ring

/-- `18! * certQ` as an integer coefficient list, lowest degree first. -/
@[expose] def certP : IntPoly :=
  [0, 301577411034611712000, 1134193306717126656000, -18739867347641696256000,
    -32842982000626237440000, 326702176168714253107200, 305549933392096365772800,
    -2413115680306070554214400, -1208665697255858877235200, 8596251864142770040012800,
    2017429890733951881707520, -14609216358110315699896320, -821012305358570167664640,
    9483102193412606294753280, -677364442386614735339520, 45157629492440982355968,
    -2822351843277561397248, 166020696663385964544, -9223372036854775808]

/-- `certP` evaluates to `18! * certQ`. -/
theorem certQ_eval (x : ℝ) : ((6402373705728000 : ℤ) : ℝ) * certQ x = IntPoly.eval x certP := by
  rw [Int.cast_ofNat, certQ_expand]
  simp only [certP, IntPoly.eval_cons, IntPoly.eval_nil]
  push_cast
  ring

/-- The degree-18 truncation against `Real.exp`, from `Real.exp_bound` at `n = 19`. -/
theorem abs_taylorExpNeg_sub_exp_le (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    |taylorExpNeg 18 t - Real.exp (-t)| ≤ 20 / 2311256907767808000 := by
  have hx : |(-t)| ≤ 1 := by rw [abs_neg, abs_of_nonneg ht0]; exact ht1
  have h := Real.exp_bound hx (n := 19) (by norm_num)
  have hp : |(-t)| ^ 19 ≤ 1 := pow_le_one₀ (abs_nonneg _) hx
  have heq : taylorExpNeg 18 t = ∑ m ∈ Finset.range 19, (-t) ^ m / (m.factorial : ℝ) := by
    unfold taylorExpNeg
    norm_num
  rw [heq, abs_sub_comm]
  refine le_trans h ?_
  have hc : ((Nat.succ 19 : ℕ) : ℝ) / (((Nat.factorial 19 : ℕ) : ℝ) * ((19 : ℕ) : ℝ))
      = 20 / 2311256907767808000 := by norm_num [Nat.factorial]
  rw [hc]
  nlinarith [abs_nonneg (-t)]

end Falcon.Concrete.FPRBridge
