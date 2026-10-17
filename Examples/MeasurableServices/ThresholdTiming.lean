/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module
public import VCVio.OracleComp.Coinductive.UniformThreshold.Cost
public import ToMathlib.Probability.FairBit

/-!
# Timing of an exact threshold sampler

For threshold `1/3`, finishing within one bit reveals that the answer is false. The
one-bit run finishes with probability one half, while two zero bits return true. Exact
output correctness and an expected-bit bound therefore do not assert constant-time behavior.
-/

public section

open MeasureTheory ProbabilityTheory UniformThreshold
open scoped ENNReal

namespace ThresholdTiming

/-- The first query at one third initially needs a bit. -/
theorem third_unresolved : classify (1 / 3) Prefix.empty = none := by
  norm_num [classify, Prefix.empty, Prefix.push, Prefix.lower, Prefix.upper]

/-- The lower half still straddles one third. -/
theorem third_lower_unresolved : classify (1 / 3) (Prefix.empty.push false) = none := by
  norm_num [classify, Prefix.empty, Prefix.push, Prefix.lower, Prefix.upper]

/-- The upper half is entirely above one third. -/
theorem third_upper_false : classify (1 / 3) (Prefix.empty.push true) = some false := by
  norm_num [classify, Prefix.empty, Prefix.push, Prefix.lower, Prefix.upper]

/-- Two zero bits put the whole represented interval below one third. -/
theorem third_lower_lower_true :
    classify (1 / 3) ((Prefix.empty.push false).push false) = some true := by
  norm_num [classify, Prefix.empty, Prefix.push, Prefix.lower, Prefix.upper]

/-- A one-bit execution is exactly the mixture of cutoff and a false answer. -/
theorem one_bit_law : boundedLaw (1 / 3) Prefix.empty 1 =
    (2 : ℝ≥0∞)⁻¹ •
      (Measure.dirac none + Measure.dirac (some (false, Prefix.empty.push true))) := by
  rw [boundedLaw_succ _ _ 0 third_unresolved,
    Measure.bind_uniformOn_bool, boundedLaw_zero_of_unresolved _ _ third_lower_unresolved,
    boundedLaw_of_resolved _ _ _ third_upper_false]

/-- One half of the executions need more than one bit. -/
theorem one_bit_cutoff : boundedLaw (1 / 3) Prefix.empty 1 {none} = (2 : ℝ≥0∞)⁻¹ := by
  rw [one_bit_law]
  simp

/-- No execution can return true within one bit, so the completion observation leaks answer
information. This is an exact event calculation, not a timing-security certificate. -/
theorem one_bit_true :
    boundedLaw (1 / 3) Prefix.empty 1 {out | ∃ p, out = some (true, p)} = 0 := by
  rw [one_bit_law]
  simp

end ThresholdTiming
