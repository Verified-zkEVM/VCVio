/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module
public import VCVio.ProgramLogic.Relational.ApproxReconstruction

/-!
# A summable adaptive precision budget

A service records the number of completed queries in its state. Charging at most half the
remaining geometric budget and incrementing that counter pays for arbitrarily many adaptive
queries. The bound is uniform over finite clients; a separate trajectory construction can
then use a uniform finite-prefix bound for full-path events.
-/

public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace PFunctor.KernelHandler

variable {P : PFunctor} {S : Type*} [∀ a, MeasurableSpace (P.B a)] [MeasurableSpace S]

/-- Geometrically increasing precision pays for every adaptive query from one initial budget. -/
theorem expectedCharge_le_geometric {α : Type*} (concrete : KernelHandler P S)
    [∀ a, IsSubprobabilityKernel (concrete a)] (charge : P.A → S → ℝ≥0∞)
    (index : S → ℕ)
    (hnext : ∀ a s, ∀ᵐ out ∂concrete a s, index out.2 = index s + 1)
    (hcharge : ∀ a s, charge a s ≤ (2 : ℝ≥0∞)⁻¹ ^ (index s + 1))
    (program : FreeM P α) (s : S) :
    expectedCharge concrete charge program s ≤ (2 : ℝ≥0∞)⁻¹ ^ index s := by
  apply expectedCharge_le_potential concrete charge (fun s => (2 : ℝ≥0∞)⁻¹ ^ index s)
  intro a state
  calc
    _ ≤ (2 : ℝ≥0∞)⁻¹ ^ (index state + 1) +
        ∫⁻ out, (2 : ℝ≥0∞)⁻¹ ^ index out.2 ∂concrete a state :=
      add_le_add (hcharge a state) le_rfl
    _ = (2 : ℝ≥0∞)⁻¹ ^ (index state + 1) +
        ∫⁻ _ : P.B a × S, (2 : ℝ≥0∞)⁻¹ ^ (index state + 1) ∂concrete a state := by
      congr 1
      apply lintegral_congr_ae
      filter_upwards [hnext a state] with out ho
      rw [ho]
    _ ≤ (2 : ℝ≥0∞)⁻¹ ^ (index state + 1) + (2 : ℝ≥0∞)⁻¹ ^ (index state + 1) := by
      rw [lintegral_const]
      exact add_le_add le_rfl (mul_le_of_le_one_right' (measure_univ_le _))
    _ = (2 : ℝ≥0∞)⁻¹ ^ index state := by
      rw [pow_succ, ← mul_add, ENNReal.inv_two_add_inv_two, mul_one]

end PFunctor.KernelHandler
