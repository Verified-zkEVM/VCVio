/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module
public import QuantumFoundations.DSubInstrument.Observe

/-!
# Classical observations as physical instruments

A classical observation of an instrument's outcome can be implemented by retaining that
observation and discarding the final quantum register. The resulting instrument has the
observed classical outcome type and one fixed trivial output register. Its outcome law is
exactly the pushforward of the original outcome law, including lost mass.
-/

public section

open MeasureTheory
open scoped ENNReal

namespace Quantum.DSubInstrument

variable {A ι α : Type*} [Fintype A]
  {B : ι → Type*} [∀ i, Fintype (B i)]

/-- Relabelling dependent outcomes pushes their law forward whenever the output-register
family is compatible with the relabelling. -/
theorem outcomeMeasure_map_eq_map {κ : Type*} [MeasurableSpace ι] [MeasurableSpace κ]
    {C : κ → Type*} [∀ c, Fintype (C c)] (f : ι → κ) (hf : Measurable f)
    (p : DSubInstrument A ι (fun i ↦ C (f i))) (ρ : SubState A) :
    (DSubInstrument.map f p).outcomeMeasure ρ = (p.outcomeMeasure ρ).map f := by
  rw [outcomeMeasure_map, outcomeMeasure_eq_sum, Measure.map_sum hf.aemeasurable]
  refine congrArg Measure.sum (funext fun i ↦ ?_)
  rw [Measure.map_smul _ hf.aemeasurable, Measure.map_dirac' hf]

/-- Discard a quantum register, returning the unique trivial output. -/
@[expose]
noncomputable def discard (A : Type*) [Fintype A] : SubInstrument A Unit Unit := by
  classical
  exact DSubInstrument.classical (B := fun _ : Unit ↦ Unit) (fun _ : A ↦ ()) (fun _ ↦ ())

/-- Discarding a register preserves its trace. -/
theorem discard_lossless (A : Type*) [Fintype A] : (discard A).Lossless := by
  classical
  exact DSubInstrument.lossless_classical _ _

/-- The unique discard branch has the same trace on every input operator. -/
theorem trace_discard (ρ : Matrix A A ℂ) : ((discard A).branch () ρ).trace = ρ.trace := by
  have h := discard_lossless A ρ
  simpa only [MatrixMap.familyTrace_apply_univ, Fintype.sum_unique] using h

/-- Run an instrument, retain a classical observation of its branch, and discard its final
quantum output. The observed outcome type may lie in a smaller universe than the branch type. -/
@[expose]
noncomputable def observe (p : DSubInstrument A ι B) (f : ι → α) : SubInstrument A Unit α :=
  p.bind fun i ↦ DSubInstrument.bind (discard (B i)) fun _ ↦
    DSubInstrument.ret (fun _ : α ↦ Unit) (f i)

/-- Observing branches physically agrees with pushing their outcome measure forward. -/
theorem outcomeMeasure_observe [MeasurableSpace ι] [MeasurableSpace α]
    (p : DSubInstrument A ι B) (f : ι → α) (hf : Measurable f) (ρ : SubState A) :
    (observe p f).outcomeMeasure ρ = (p.outcomeMeasure ρ).map f := by
  rw [observe, outcomeMeasure_bind, outcomeMeasure_eq_sum, Measure.map_sum hf.aemeasurable]
  refine congrArg Measure.sum (funext fun i ↦ ?_)
  rw [outcomeMeasure_bind]
  simp only [Measure.sum_fintype, Fintype.sum_unique, outcomeMeasure_ret]
  rw [Measure.map_smul _ hf.aemeasurable, Measure.map_dirac' hf]
  congr 1
  rw [matrix_post, trace_discard, matrix_post]

end Quantum.DSubInstrument
