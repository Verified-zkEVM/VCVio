/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module
public import VCVio.Quantum.Comp.Combinators
public import VCVio.Quantum.Foundations.Parallel

/-!
# Ordered batches of quantum oracle calls

A batch exposes one copy of a port's register for each slot and applies the port to the
slots in increasing order. All slots share the runtime's private memory. This construction
is defined for ports with identical input and output registers and a trivial classical
result; the steps may be arbitrary subinstruments.

Ordered batching does not assert that the steps commute. A simultaneous oracle law requires
an additional theorem about the particular runtime, as in VCVio.Quantum.Oracle.Parallel.
-/

public section

open Matrix

universe u v w z

namespace Quantum

/-- Ports indexed by a base port and a batch width; each call acts on that many copies
of the base port's register and has no classical result. -/
@[expose, reducible]
def uBatchSpec (P : Type u) (In : P → QReg) : QuantumOracleSpec.{u, 0} :=
  uSpec (P × ℕ) fun ik ↦ QReg.of (Fin ik.2 → In ik.1)

namespace QuantumRuntime

private theorem intertwines_relabel_queryEquivIn_symm {A I E D D' : QReg}
    (V : MatrixMap D D') (ℓ : A ≃ I × E) :
    DSubInstrument.Intertwines ((V.amplifyLeft I).amplify E)
      (fun _ ↦ V.amplifyLeft A)
      (SubInstrument.relabel (queryEquivIn ℓ D).symm)
      (SubInstrument.relabel (queryEquivIn ℓ D').symm) := fun _ ↦ by
  refine LinearMap.ext fun ρ ↦ ?_
  ext x y
  simp only [LinearMap.comp_apply, SubInstrument.relabel_branch_apply, Equiv.symm_symm]
  rfl

private theorem intertwines_lift_piWithMemory {ι : Type} [Fintype ι] [DecidableEq ι]
    {A D D' : QReg} (i : ι) (V : MatrixMap D D')
    {p : SubInstrument (A × D) (A × D) Unit}
    {q : SubInstrument (A × D') (A × D') Unit}
    (h : DSubInstrument.Intertwines (V.amplifyLeft A) (fun _ ↦ V.amplifyLeft A) p q) :
    DSubInstrument.Intertwines (V.amplifyLeft (ι → A)) (fun _ ↦ V.amplifyLeft (ι → A))
      (p.lift (Subsystem.piWithMemory i A D))
      (q.lift (Subsystem.piWithMemory i A D')) := by
  intro r
  apply LinearMap.ext
  intro ρ
  let E := QReg.of ({j : ι // j ≠ i} → A)
  let ℓ := Equiv.funSplitAt i A
  have hin := LinearMap.congr_fun (intertwines_relabel_queryEquivIn V ℓ ()) ρ
  have hmid := LinearMap.congr_fun ((h.frame E) r)
    (ρ.submatrix (queryEquivIn ℓ D).symm (queryEquivIn ℓ D).symm)
  have hout := LinearMap.congr_fun
    (intertwines_relabel_queryEquivIn_symm (A := QReg.of (ι → A)) (I := A)
      (E := E) V ℓ ())
    ((p.branch r).amplify E
      (ρ.submatrix (queryEquivIn ℓ D).symm (queryEquivIn ℓ D).symm))
  simp only [LinearMap.comp_apply, SubInstrument.relabel_branch_apply,
    DSubInstrument.branch_frame_apply, Equiv.symm_symm] at hin hmid hout
  simp only [LinearMap.comp_apply]
  rw [SubInstrument.lift_branch_apply (Subsystem.piWithMemory i A D') q r,
    SubInstrument.lift_branch_apply (Subsystem.piWithMemory i A D) p r]
  change ((q.branch r).amplify E
    ((V.amplifyLeft (ι → A) ρ).submatrix
      (queryEquivIn ℓ D').symm (queryEquivIn ℓ D').symm)).submatrix
        (queryEquivIn ℓ D') (queryEquivIn ℓ D') =
    V.amplifyLeft (ι → A) (((p.branch r).amplify E
      (ρ.submatrix (queryEquivIn ℓ D).symm (queryEquivIn ℓ D).symm)).submatrix
        (queryEquivIn ℓ D) (queryEquivIn ℓ D))
  rw [hin, hmid, hout]

/-- Batch the one-result endomorphism ports of a runtime in increasing slot order.
The private register and its initial state are shared by all slots and calls. -/
@[expose]
noncomputable def batch {P : Type u} {In : P → QReg}
    (R : QuantumRuntime (uSpec P In)) : QuantumRuntime (uBatchSpec P In) where
  D := R.D
  init := R.init
  step ik := SubInstrument.batch (In ik.1) R.D (R.step ik.1) ik.2

/-- The private register of a batched runtime is the original runtime's private register. -/
@[simp]
theorem batch_D {P : Type u} {In : P → QReg} (R : QuantumRuntime (uSpec P In)) :
    R.batch.D = R.D :=
  rfl

/-- Batching preserves the initial state of the private register. -/
@[simp]
theorem batch_init {P : Type u} {In : P → QReg} (R : QuantumRuntime (uSpec P In)) :
    R.batch.init = R.init :=
  rfl

/-- Batched steps are lossless when all base steps are lossless. -/
theorem lossless_batch_step {P : Type u} {In : P → QReg}
    (R : QuantumRuntime (uSpec P In)) (hR : ∀ i, (R.step i).Lossless) (ik : P × ℕ) :
    (R.batch.step ik).Lossless :=
  SubInstrument.lossless_batch (In ik.1) R.D (hR ik.1) ik.2

/-- Simulations through private memory are preserved by ordered batching. -/
theorem intertwines_batch_step {P : Type u} {In : P → QReg}
    {R S : QuantumRuntime (uSpec P In)} (V : MatrixMap R.D S.D)
    (h : ∀ i, DSubInstrument.Intertwines (V.amplifyLeft (In i))
      (fun _ ↦ V.amplifyLeft (In i)) (R.step i) (S.step i)) (ik : P × ℕ) :
    DSubInstrument.Intertwines (V.amplifyLeft (Fin ik.2 → In ik.1))
      (fun _ ↦ V.amplifyLeft (Fin ik.2 → In ik.1))
      (R.batch.step ik) (S.batch.step ik) :=
  SubInstrument.intertwines_sequenceUnit _ _ _ _ fun i _ ↦
    intertwines_lift_piWithMemory i V (h ik.1)

/-- A trace-preserving simulation of base runtimes also equates the output laws of all
adaptive programs using their batches. -/
theorem evalDist_batch_eq_of_simulation {P : Type u} {In : P → QReg}
    {R S : QuantumRuntime (uSpec P In)} (V : MatrixMap R.D S.D)
    (h : ∀ i, DSubInstrument.Intertwines (V.amplifyLeft (In i))
      (fun _ ↦ V.amplifyLeft (In i)) (R.step i) (S.step i))
    (hV : V.IsTP) (hinit : V R.init.matrix = S.init.matrix)
    {L : LocalSig.{v, w}} {W : QReg → Type z} {A : QReg}
    [MeasurableSpace (Σ a, W a)] (I : L.Interp)
    (x : QuantumComp L (uBatchSpec P In) W A) (ρ : SubState A) :
    S.batch.evalDist I x ρ = R.batch.evalDist I x ρ :=
  evalDist_eq_of_simulation (R₁ := R.batch) (R₂ := S.batch) (V := V) I
    (fun ik ↦ intertwines_batch_step V h ik) hV hinit x ρ

end QuantumRuntime

end Quantum
