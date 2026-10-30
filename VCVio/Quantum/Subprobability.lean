/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import ToMathlib.MeasureTheory.Measure.Subprobability
public import QuantumFoundations.Observe

/-!
# Outcome measures are subprobability measures

Registers the outcome measure `Quantum.DSubInstrument.outcomeMeasure` of a dependent
subinstrument as an instance of VCVio's `MeasureTheory.IsSubprobabilityMeasure` class. The bound
itself is `Quantum.DSubInstrument.outcomeMeasure_apply_univ_le_one`.
-/

public section

namespace Quantum

namespace DSubInstrument

variable {A : Type*} [Fintype A] {ι : Type*} [MeasurableSpace ι] {B : ι → Type*}
  [∀ i, Fintype (B i)]

/-- Outcome measures of dependent subinstruments are subprobability measures. -/
instance outcomeMeasure.instIsSubprobabilityMeasure (p : DSubInstrument A ι B)
    (ρ : SubState A) : MeasureTheory.IsSubprobabilityMeasure (p.outcomeMeasure ρ) :=
  ⟨p.outcomeMeasure_apply_univ_le_one ρ⟩

end DSubInstrument

end Quantum
