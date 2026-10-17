/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module
public import Examples.ResumptionRejection
public import ToMathlib.Probability.UniformOn

/-!
# A rejection sampler whose retry cutoff does not bias the returned value

The four-outcome sampler accepts three values and retries on the fourth. At every finite
budget its successful law is a scalar multiple of the eventual uniform output law. Thus
learning whether it finished by any particular attempt does not change the distribution of
the value on successful runs. This contrasts with the persistent threshold sampler.

The theorem is a cumulative joint timing/output assertion through the actual resumption's
finite successful measures. It does not assume that a correct output marginal alone makes
execution time independent of the output.
-/

public section

open MeasureTheory ProbabilityTheory PFunctor
open scoped ENNReal

namespace ResumptionRejection

/-- Finite successful output is a scalar multiple of the uniform result law. -/
theorem outputMeasure_eq_scaled_uniform (fuel : ℕ) :
    Resumption.outputMeasure fuel sample =
      ((3 : ℝ≥0∞) * ∑ j ∈ Finset.range fuel, (4 : ℝ≥0∞)⁻¹ ^ (j + 1)) •
        uniformOn (Set.univ : Set (Fin 3)) := by
  apply Measure.ext_of_singleton
  intro x
  rw [returned_singleton_finite, Measure.smul_apply, smul_eq_mul,
    uniformOn_univ_apply_singleton]
  simp only [Fintype.card_fin, Nat.cast_ofNat]
  rw [mul_comm (3 : ℝ≥0∞), mul_assoc, ENNReal.mul_inv_cancel (by norm_num) (by norm_num), mul_one]

/-- Every finite-time successful event factors as completion mass times its eventual-output
probability. In particular, the cutoff does not favor one accepted value over another. -/
theorem outputMeasure_eq_completion_smul_returned (fuel : ℕ) :
    Resumption.outputMeasure fuel sample =
      Resumption.outputMeasure fuel sample Set.univ • Resumption.returnedMeasure sample := by
  rw [outputMeasure_eq_scaled_uniform, returned_uniform]
  simp only [Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]

/-- Event-level cumulative timing/output factorization for the concrete rejection process. -/
theorem completion_output_factorization (fuel : ℕ) (event : Set (Fin 3)) :
    Resumption.outputMeasure fuel sample event =
      Resumption.outputMeasure fuel sample Set.univ * Resumption.returnedMeasure sample event := by
  conv_lhs => rw [outputMeasure_eq_completion_smul_returned]
  rw [Measure.smul_apply, smul_eq_mul]

end ResumptionRejection
