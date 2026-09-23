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
  {α : Type}

/-- Structural postcondition comparison controls native expectation WP. -/
@[gcongr]
theorem wp_mono_of_support (mx : OracleComp spec α) {f g : α → ENNReal}
    (hfg : ∀ x ∈ support mx, f x ≤ g x) : MAlgOrdered.wp mx f ≤ MAlgOrdered.wp mx g := by
  rw [MAlgOrdered.wp, MAlgOrdered.wp, μ_eq_lintegral, μ_eq_lintegral]
  apply OracleComp.lintegral_evalDist_bind_mono_of_support mx _ _ measurable_id measurable_id
  intro a ha
  simpa only [evalDist_pure, lintegral_dirac, id_eq] using hfg a ha

/-- Constant assertions on lossless oracle programs evaluate to that constant. -/
@[simp]
theorem wp_const_of_oracle (mx : OracleComp spec α) (c : ENNReal) :
    MAlgOrdered.wp mx (fun _ ↦ c) = c := by
  rw [wp_eq_lintegral_map]
  simp

/-- Oracle expectations are additive for arbitrary assertion-valued observations. -/
theorem wp_add_of_oracle (mx : OracleComp spec α) (f g : α → ENNReal) :
    MAlgOrdered.wp mx (fun x ↦ f x + g x) = MAlgOrdered.wp mx f + MAlgOrdered.wp mx g := by
  let obs : α → ENNReal × ENNReal := fun x ↦ (f x, g x)
  let : MeasurableSpace α := MeasurableSpace.comap obs inferInstance
  have hobs : Measurable obs := comap_measurable obs
  exact wp_add mx f g (measurable_fst.comp hobs) (measurable_snd.comp hobs)

/-- Scaling an arbitrary oracle assertion scales its expectation. -/
theorem wp_const_mul_of_oracle (mx : OracleComp spec α) (c : ENNReal) (f : α → ENNReal) :
    MAlgOrdered.wp mx (fun x ↦ c * f x) = c * MAlgOrdered.wp mx f := by
  let : MeasurableSpace α := MeasurableSpace.comap f inferInstance
  exact wp_const_mul mx c f (comap_measurable f)

/-- Finite sums of oracle assertions commute with expectation. -/
theorem wp_finsetSum_of_oracle {κ : Type*} (mx : OracleComp spec α) (s : Finset κ)
    (f : κ → α → ENNReal) :
    MAlgOrdered.wp mx (fun x ↦ ∑ i ∈ s, f i x) = ∑ i ∈ s, MAlgOrdered.wp mx (f i) := by
  let obs : α → (κ → ENNReal) := fun x i ↦ f i x
  let : MeasurableSpace α := MeasurableSpace.comap obs inferInstance
  have hobs : Measurable obs := comap_measurable obs
  exact wp_finsetSum mx s f fun i _ ↦ (measurable_pi_apply i).comp hobs

/-- A pathwise bound controls native quantitative correctness. -/
theorem wp_le_const_of_support (mx : OracleComp spec α) {f : α → ENNReal} {c : ENNReal}
    (hf : ∀ x ∈ support mx, f x ≤ c) : MAlgOrdered.wp mx f ≤ c :=
  (wp_mono_of_support mx hf).trans_eq (wp_const_of_oracle mx c)

/-- A pathwise additive allowance controls oracle expectation. -/
theorem wp_le_const_add_of_support (mx : OracleComp spec α) {f g : α → ENNReal} {c : ENNReal}
    (hfg : ∀ x ∈ support mx, f x ≤ c + g x) :
    MAlgOrdered.wp mx f ≤ c + MAlgOrdered.wp mx g := by
  refine (wp_mono_of_support mx hfg).trans_eq ?_
  rw [wp_add_of_oracle, wp_const_of_oracle]

end MeasureProgramLogic.Quantitative
