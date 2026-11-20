/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module
public import QuantumFoundations.SubInstrument.Relabel
public import VCVio.Quantum.Foundations.Observation

/-!
# Removing a trivial private register

A private register of dimension one contains no independent information. Relabelling away its
unit factor and framing it back leaves a dependent subinstrument unchanged, including every
classical branch and quantum output. These identities apply to arbitrary input operators.
-/

public section

open MeasureTheory

namespace Quantum.DSubInstrument

variable {A ι : Type*} [Fintype A] [DecidableEq A]
  {B : ι → Type*} [∀ i, Fintype (B i)]

/-- Relabel the input and every output of an instrument to remove their unit factor. -/
@[expose]
noncomputable def dropUnit (p : DSubInstrument (A × Unit) ι (fun i ↦ B i × Unit)) :
    DSubInstrument A ι B :=
  DSubInstrument.bind (SubInstrument.relabel (Equiv.prodPUnit A).symm) fun _ ↦
    p.relabelOut fun i ↦ Equiv.prodPUnit (B i)

/-- A branch of the relabelled instrument inserts and removes the unique unit basis value. -/
theorem branch_dropUnit (p : DSubInstrument (A × Unit) ι (fun i ↦ B i × Unit))
    (i : ι) (ρ : Matrix A A ℂ) :
    (dropUnit p).branch i ρ =
      (p.branch i (ρ.submatrix Prod.fst Prod.fst)).submatrix (fun b ↦ (b, ()))
        (fun b ↦ (b, ())) := by
  rw [dropUnit, DSubInstrument.branch_bind_unit, LinearMap.comp_apply,
    DSubInstrument.relabelOut_branch_apply, SubInstrument.relabel_branch_apply]
  rfl

/-- Restoring the trivial factor recovers the full original instrument. -/
theorem frame_dropUnit (p : DSubInstrument (A × Unit) ι (fun i ↦ B i × Unit)) :
    (dropUnit p).frame Unit = p := by
  apply DSubInstrument.ext
  funext i
  apply LinearMap.ext
  intro ρ
  ext a b
  rw [DSubInstrument.branch_frame_apply, MatrixMap.amplify_apply]
  simp only [branch_dropUnit]
  have he : (ρ.submatrix (fun x ↦ (x, a.2)) (fun y ↦ (y, b.2))).submatrix
      Prod.fst Prod.fst = ρ := by
    ext x y
    rcases x with ⟨x, ⟨⟩⟩
    rcases y with ⟨y, ⟨⟩⟩
    cases a.2
    cases b.2
    rfl
  change (p.branch i _).submatrix (fun x ↦ (x, ())) (fun y ↦ (y, ())) a.1 b.1 = _
  rw [he]
  cases a.2
  cases b.2
  rfl

/-- A classical observation after removing and restoring unit memory has the original joint
outcome law. Only the final quantum output is discarded. -/
theorem outcomeMeasure_frame_dropUnit_observe {α : Type*}
    [MeasurableSpace ι] [MeasurableSpace α]
    (p : DSubInstrument (A × Unit) ι (fun i ↦ B i × Unit)) (f : ι → α)
    (hf : Measurable f) (ρ : SubState (A × Unit)) :
    ((p.dropUnit.observe f).frame Unit).outcomeMeasure ρ = (p.outcomeMeasure ρ).map f := by
  rw [outcomeMeasure_frame, outcomeMeasure_observe _ _ hf,
    ← outcomeMeasure_frame p.dropUnit Unit ρ, frame_dropUnit]

end Quantum.DSubInstrument
