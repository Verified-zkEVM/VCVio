/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module

public import HashSig.SLHDSA.Security.BoundEval
public import HashSig.SLHDSA.Security.RangeBound

/-!
# Kernel-checked numerical security certificates

The table fixes both budgets at `2^64`. Each decimal coefficient is certified by exact
rational power inequalities: a displayed value `b/100` lies within `0.005` bits of the
negative base-two logarithm precisely when its coefficient's 200th power lies between
`2^(-(2b+1))` and `2^(-(2b-1))`. No floating point or native proof axiom is used.
These table certificates are point evaluations; range certificates require budget monotonicity.
-/

public section

namespace SLHDSA.Security

/-- An exact rational bracket for the displayed coefficient in hundredths of a bit. -/
@[expose] def RoundedCoefficient (coefficient : ℚ≥0) (hundredths : ℕ) : Prop :=
  (2 : ℚ≥0) ^ (2 * hundredths + 1) * coefficient ^ 200 ≥ 1 ∧
    (2 : ℚ≥0) ^ (2 * hundredths - 1) * coefficient ^ 200 ≤ 1

instance (coefficient : ℚ≥0) (hundredths : ℕ) :
    Decidable (RoundedCoefficient coefficient hundredths) := by
  unfold RoundedCoefficient
  infer_instance

/-- The published three-oracle, deterministic byte, and hedged byte coefficients. -/
@[expose] def boundTable : List (FipsParameterSet × ℕ × ℕ × ℕ) :=
  [(.SLHDSA_SHAKE_128s, 12699, 12641, 12699),
   (.SLHDSA_SHAKE_128f, 12654, 12609, 12654),
   (.SLHDSA_SHAKE_192s, 19082, 19029, 19082),
   (.SLHDSA_SHAKE_192f, 19087, 19033, 19087),
   (.SLHDSA_SHAKE_256s, 25441, 25400, 25441),
   (.SLHDSA_SHAKE_256f, 25427, 25389, 25427)]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
-- Kernel reduction certifies eighteen large exact rational powers in one finite table.
/-- Every displayed entry is certified against the exact evaluators linked to the
security theorems. At 256 bits the weak-seed factor is included before rounding. -/
theorem boundTable_certified :
    ∀ entry ∈ boundTable,
      let p := entry.1.validatedParams.params
      let q : ℕ := 2 ^ 64
      RoundedCoefficient (securityBoundEval p (256 ^ p.n) 2 1 q q / q) entry.2.1 ∧
      RoundedCoefficient (averagedByteBoundEval p q q / q) entry.2.2.1 ∧
      RoundedCoefficient (averagedByteBoundHedgedEval p q q / q) entry.2.2.2 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
-- Each lifetime is checked at six parameter sets using the executable coefficient recurrence.
/-- Uniform structured-ROM floors of `8n - 2` bits for `2^32 ≤ qh ≤ 2^64`,
at signing lifetimes `2^20`, `2^32`, and `2^64`. Apply
`securityBound_le_div_pow_of_coefficient` for any budgets inside the certified rectangle. -/
theorem rangeCoefficients_certified :
    ∀ entry ∈ boundTable, ∀ lifetime ∈ ([2 ^ 20, 2 ^ 32, 2 ^ 64] : List ℕ),
      let p := entry.1.validatedParams.params
      securityCoefficientEval p (256 ^ p.n) (2 ^ 32) (2 ^ 64) lifetime ≤
        1 / (2 : ℚ≥0) ^ (8 * p.n - 2) := by
  decide +kernel

end SLHDSA.Security
