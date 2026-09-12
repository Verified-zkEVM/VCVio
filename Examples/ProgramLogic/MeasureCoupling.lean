/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module
public import VCVio.ProgramLogic.Relational.Measure.Bind
public import ToMathlib.MeasureTheory.Measure.Coupling.Residual
public import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# Continuous transitions and unequal successful-output mass

Shared Gaussian noise preserves an offset between arbitrary random initial states. The proof
uses a measurable joint transition family and the generic sequential relational rule; it does
not enumerate outcomes. A second example isolates a terminating branch from a missing-mass
computation and propagates its residual through the same sequential composition machinery.
-/

public section

open MeasureTheory ProbabilityTheory MeasureProgramLogic
open scoped NNReal

namespace Examples.MeasureCoupling

/-- The two coordinates receive the same centered Gaussian noise. -/
noncomputable def sharedGaussian (variance : ℝ≥0) (z : ℝ × ℝ) : Measure (ℝ × ℝ) :=
  (gaussianReal 0 variance).map fun noise => (z.1 + noise, z.2 + noise)

/-- Shared noise is a measurable joint transition even on continuous state spaces. -/
theorem measurable_sharedGaussian (variance : ℝ≥0) : Measurable (sharedGaussian variance) := by
  exact Measure.measurable_map_parameter (gaussianReal 0 variance)
    ((measurable_fst.fst.add measurable_snd).prodMk (measurable_fst.snd.add measurable_snd))

/-- Each coordinate of the shared-noise transition has the prescribed Gaussian law. -/
theorem sharedGaussian_isCoupling (variance : ℝ≥0) (z : ℝ × ℝ) :
    Measure.IsCoupling (sharedGaussian variance z)
      (gaussianReal z.1 variance) (gaussianReal z.2 variance) := by
  constructor
  · rw [sharedGaussian, Measure.fst, Measure.map_map measurable_fst (by fun_prop)]
    simpa only [Function.comp_def, zero_add] using
      gaussianReal_map_const_add (μ := 0) (v := variance) z.1
  · rw [sharedGaussian, Measure.snd, Measure.map_map measurable_snd (by fun_prop)]
    simpa only [Function.comp_def, zero_add] using
      gaussianReal_map_const_add (μ := 0) (v := variance) z.2

/-- Shared Gaussian noise preserves the offset of a pair of initial states almost everywhere. -/
theorem sharedGaussian_ae_offset (variance : ℝ≥0) (offset : ℝ) (z : ℝ × ℝ)
    (hz : z.2 = z.1 + offset) :
    ∀ᵐ out ∂sharedGaussian variance z, out.2 = out.1 + offset := by
  rw [sharedGaussian]
  apply (ae_map_iff (by fun_prop) (by measurability)).2
  exact Filter.Eventually.of_forall fun noise => by dsimp; rw [hz]; ring

/-- Adding Gaussian noise to both sides preserves an offset under arbitrary initial state laws.
Positive variance gives genuinely continuous transitions; zero variance is included as well. -/
theorem gaussian_bind_preserves_offset (μ ν : Measure ℝ) (offset : ℝ) (variance : ℝ≥0)
    (hinit : CouplingPost μ ν (fun a b => b = a + offset)) :
    CouplingPost (μ.bind fun a => gaussianReal a variance)
      (ν.bind fun b => gaussianReal b variance) (fun a b => b = a + offset) := by
  have hm : Measurable fun a : ℝ => gaussianReal a variance :=
    measurable_gaussianReal.comp (measurable_id.prodMk measurable_const)
  have hrel : MeasurableSet {z : ℝ × ℝ | z.2 = z.1 + offset} := by measurability
  apply hinit.bind hm hm (measurable_sharedGaussian variance) hrel
  intro z hz
  exact ⟨sharedGaussian_isCoupling variance z, sharedGaussian_ae_offset variance offset z hz⟩

/-- An entirely unmatched left law is an admissible residual, even when the right computation
has no successful outputs. Exact coupling cannot express this comparison for nonzero left mass. -/
theorem unmatched_law (μ : Measure ℝ) :
    Measure.IsSubcouplingWithResidual (0 : Measure (ℝ × ℝ)) μ μ 0 := by
  constructor <;> simp [Measure.fst, Measure.snd]

/-- Missing initial mass is propagated through the left continuation, without assuming that
the continuation is lossless. -/
theorem unmatched_bind (μ : Measure ℝ) (k : ℝ → Measure ℝ) (hk : Measurable k) :
    Measure.IsSubcouplingWithResidual (0 : Measure (ℝ × ℝ)) (μ.bind k) (μ.bind k) 0 := by
  have h := (unmatched_law μ).bind hk (measurable_const (a := (0 : Measure ℝ)))
    (measurable_const (a := (0 : Measure (ℝ × ℝ))))
    (measurable_const (a := (0 : Measure ℝ))) (by simp)
  simpa using h

end Examples.MeasureCoupling
