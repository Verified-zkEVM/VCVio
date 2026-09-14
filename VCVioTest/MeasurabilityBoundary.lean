/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import VCVio.EvalDist.PFunctorMeasure.Core

/-!
# Measurable continuations are necessary for lossless interpretation

A two-point answer space with only trivial measurable sets cannot reveal its hidden bit as a
discrete output. Every individual continuation is a Dirac probability measure, but the family
of continuations is not almost everywhere measurable. The direct fold assigns zero measure to
that invalid composition. A constant continuation over the same interface remains lossless.
-/

public section

open MeasureTheory PFunctor
open scoped ENNReal

namespace VCVioTest.MeasurabilityBoundary

/-- A bit whose measurable structure does not distinguish its two values. -/
structure CoarseBit where
  /-- The underlying value, which the measurable structure does not expose. -/
  down : Bool

instance : MeasurableSpace CoarseBit := ⊥

theorem coarse_dirac_eq (a b : CoarseBit) : Measure.dirac a = Measure.dirac b := by
  ext s hs
  rcases MeasurableSpace.measurableSet_bot_iff.mp hs with rfl | rfl <;> simp

instance : (Measure.dirac (⟨false⟩ : CoarseBit)).IsComplete := by
  constructor
  intro s hs
  have hempty : s = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro x hx
    have hone : Measure.dirac (⟨false⟩ : CoarseBit) s = 1 := by
      rw [coarse_dirac_eq _ x]
      exact Measure.dirac_apply_of_mem hx
    simp_all
  rw [hempty]
  exact MeasurableSet.empty

/-- The constant total mass of each continuation does not establish measurability of its law. -/
theorem reveal_not_aemeasurable :
    ¬AEMeasurable (fun bit : CoarseBit => (Measure.dirac bit.down : Measure Bool))
      (Measure.dirac (⟨false⟩ : CoarseBit)) := by
  intro h
  have hm := aemeasurable_iff_measurable.mp h
  have heval := (Measure.measurable_coe (measurableSet_singleton true)).comp hm
  have hs := heval (measurableSet_singleton (1 : ℝ≥0∞))
  rcases MeasurableSpace.measurableSet_bot_iff.mp hs with hempty | huniv
  · have := congrArg (fun s => (⟨true⟩ : CoarseBit) ∈ s) hempty
    simp at this
  · have := congrArg (fun s => (⟨false⟩ : CoarseBit) ∈ s) huniv
    simp at this

/-- One operation with the coarse two-point answer space. -/
@[expose, reducible] def coarseSpec : PFunctor.{0, 0} := ⟨Unit, fun _ => CoarseBit⟩

noncomputable instance : coarseSpec.IsMeasureSpec where
  toMeasure _ := Measure.dirac ⟨false⟩
  isProbabilityMeasure _ := inferInstance

/-- A syntactically valid continuation that attempts to expose the unmeasurable bit. -/
@[expose] def reveal : FreeM coarseSpec Bool := FreeM.liftBind () fun bit => pure bit.down

theorem reveal_continuations_lossless (bit : CoarseBit) :
    IsProbabilityMeasure (FreeM.denote (pure bit.down : FreeM coarseSpec Bool)) := by
  rw [FreeM.denote_pure (P := coarseSpec)]
  infer_instance

theorem denote_reveal : FreeM.denote reveal = 0 :=
  FreeM.denote_liftBind_of_not_aemeasurable _ _ reveal_not_aemeasurable

theorem reveal_not_lossless : ¬IsProbabilityMeasure (FreeM.denote reveal) := by
  rw [denote_reveal]
  intro h
  have := h.measure_univ
  simp at this

/-- Ignoring the coarse answer is measurable and retains probability mass one. -/
theorem constant_continuation_lossless :
    FreeM.denote (FreeM.liftBind (P := coarseSpec) () fun _ => pure true) =
      Measure.dirac true := by
  rw [FreeM.denote_liftBind (P := coarseSpec) _ _ measurable_const.aemeasurable]
  simp only [FreeM.denote_pure, Measure.bind_const,
    (IsMeasureSpec.isProbabilityMeasure (P := coarseSpec) ()).measure_univ, one_smul]

end VCVioTest.MeasurabilityBoundary
