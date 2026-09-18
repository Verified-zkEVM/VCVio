/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module
public import VCVio.ProgramLogic.Unary.WP.Measure
public import VCVio.OracleComp.EvalDist.Measure

/-!
# Quantitative correctness from possible oracle outputs

Structural postcondition bounds imply almost-everywhere bounds under the chosen response
measures. Discrete answers suffice; uniformity and positive answer masses are unnecessary.
-/

public section

open MeasureTheory
open scoped ENNReal MeasureProgramLogic.Quantitative

universe u

namespace MeasureProgramLogic.Quantitative

variable {ι : Type u} {spec : OracleSpec.{u, 0} ι}
  [∀ t, MeasurableSpace (spec.Range t)] [∀ t, DiscreteMeasurableSpace (spec.Range t)]
  [OracleSpec.IsMeasureSpec spec]
  {α : Type} [MeasurableSpace α] [DiscreteMeasurableSpace α]

/-- Structural postcondition comparison controls native expectation WP. -/
@[gcongr]
theorem wp_mono_of_support (mx : OracleComp spec α) {f g : α → ENNReal}
    (hfg : ∀ x ∈ support mx, f x ≤ g x) : MAlgOrdered.wp mx f ≤ MAlgOrdered.wp mx g :=
  wp_mono_ae mx (OracleComp.ae_of_forall_mem_support mx _ hfg)

/-- A pathwise bound controls native quantitative correctness. -/
theorem wp_le_const_of_support (mx : OracleComp spec α) {f : α → ENNReal} {c : ENNReal}
    (hf : ∀ x ∈ support mx, f x ≤ c) : MAlgOrdered.wp mx f ≤ c :=
  wp_le_const mx (OracleComp.ae_of_forall_mem_support mx _ hf)

/-- A pathwise additive allowance controls native quantitative correctness. -/
theorem wp_le_const_add_of_support (mx : OracleComp spec α) {f g : α → ENNReal} {c : ENNReal}
    (hfg : ∀ x ∈ support mx, f x ≤ c + g x) :
    MAlgOrdered.wp mx f ≤ c + MAlgOrdered.wp mx g := by
  simpa using wp_le_const_mul_mass_add mx (OracleComp.ae_of_forall_mem_support mx _ hfg)

end MeasureProgramLogic.Quantitative
