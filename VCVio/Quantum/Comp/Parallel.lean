/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module
public import VCVio.Quantum.Comp.Combinators
public import QuantumFoundations.SubInstrument.Subsystem
public import Mathlib.Data.List.FinRange

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

/-- Apply a basis permutation to one coordinate of a family of registers. -/
@[expose]
def piSlotEquiv {ι A : Type} [DecidableEq ι] (i : ι) (e : A ≃ A) :
    (ι → A) ≃ (ι → A) :=
  Equiv.piCongrRight fun j ↦ if j = i then e else Equiv.refl A

/-- A coordinate permutation changes only its selected coordinate. -/
@[simp]
theorem piSlotEquiv_apply {ι A : Type} [DecidableEq ι] (i : ι) (e : A ≃ A)
    (x : ι → A) (j : ι) :
    piSlotEquiv i e x j = if j = i then e (x j) else x j := by
  by_cases h : j = i <;> simp [piSlotEquiv, h]

namespace Subsystem

/-- One coordinate of a finite family of registers. -/
@[expose]
def pi {ι : Type} [Fintype ι] [DecidableEq ι] (i : ι) (A : QReg) :
    Subsystem A (QReg.of (ι → A)) :=
  ⟨QReg.of ({j : ι // j ≠ i} → A), Equiv.funSplitAt i A⟩

/-- A coordinate together with shared private memory, leaving all other coordinates alone. -/
@[expose]
def piWithMemory {ι : Type} [Fintype ι] [DecidableEq ι] (i : ι) (A D : QReg) :
    Subsystem (QReg.of (A × D)) (QReg.of ((ι → A) × D)) :=
  ⟨QReg.of ({j : ι // j ≠ i} → A),
    QuantumRuntime.queryEquivIn (Equiv.funSplitAt i A) D⟩

/-- Selecting a coordinate exposes its value and the restriction to the other coordinates. -/
@[simp]
theorem pi_equiv_apply {ι : Type} [Fintype ι] [DecidableEq ι] (i : ι) (A : QReg)
    (x : ι → A) :
    (pi i A).equiv x = (x i, fun j : {j : ι // j ≠ i} ↦ x j.1) :=
  rfl

/-- Selecting a coordinate with memory keeps the same private memory in the selected part. -/
@[simp]
theorem piWithMemory_equiv_apply {ι : Type} [Fintype ι] [DecidableEq ι] (i : ι)
    (A D : QReg) (x : (ι → A) × D) :
    (piWithMemory i A D).equiv x =
      ((x.1 i, x.2), fun j : {j : ι // j ≠ i} ↦ x.1 j.1) :=
  rfl

end Subsystem

namespace SubInstrument

variable {ι : Type u} {A : Type v}

section instruments

variable [Fintype A]

/-- Apply one-result operations in the order given by a list. -/
@[expose]
noncomputable def sequenceUnit (p : ι → SubInstrument A A Unit) :
    List ι → SubInstrument A A Unit
  | [] => SubInstrument.pure ()
  | i :: is => (p i).bind fun _ ↦ sequenceUnit p is

/-- An empty sequence leaves the state unchanged. -/
@[simp]
theorem sequenceUnit_nil (p : ι → SubInstrument A A Unit) :
    sequenceUnit p [] = SubInstrument.pure () :=
  rfl

/-- A sequence starts with its first operation and continues with its tail. -/
theorem sequenceUnit_cons (p : ι → SubInstrument A A Unit) (i : ι) (is : List ι) :
    sequenceUnit p (i :: is) = (p i).bind fun _ ↦ sequenceUnit p is :=
  rfl

/-- A sequence of lossless operations is lossless. -/
theorem lossless_sequenceUnit (p : ι → SubInstrument A A Unit) (is : List ι)
    (hp : ∀ i ∈ is, (p i).Lossless) : (sequenceUnit p is).Lossless := by
  induction is with
  | nil => exact DSubInstrument.lossless_ret _ _
  | cons i is ih =>
    exact (hp i (by simp)).bind fun _ ↦ ih fun j hj ↦ hp j (by simp [hj])

/-- Concatenating operation lists sequences their interpretations. -/
theorem sequenceUnit_append (p : ι → SubInstrument A A Unit) (is js : List ι) :
    sequenceUnit p (is ++ js) =
      (sequenceUnit p is).bind fun _ ↦ sequenceUnit p js := by
  induction is with
  | nil => simp
  | cons i is ih =>
    simp only [List.cons_append, sequenceUnit_cons, ih, SubInstrument.bind_assoc]

/-- Intertwining through a fixed map is preserved by an ordered sequence. -/
theorem intertwines_sequenceUnit {B : Type*} [Fintype B]
    (V : MatrixMap A B) (p : ι → SubInstrument A A Unit)
    (q : ι → SubInstrument B B Unit) (is : List ι)
    (h : ∀ i ∈ is, DSubInstrument.Intertwines V (fun _ ↦ V) (p i) (q i)) :
    DSubInstrument.Intertwines V (fun _ ↦ V) (sequenceUnit p is) (sequenceUnit q is) := by
  induction is with
  | nil => exact DSubInstrument.Intertwines.ret (fun _ : Unit ↦ V) ()
  | cons i is ih =>
    exact (h i (by simp)).bind fun _ ↦ ih fun j hj ↦ h j (by simp [hj])

end instruments

/-- The equivalence obtained by applying a list of basis permutations in order. -/
@[expose]
def sequenceEquiv (e : ι → A ≃ A) : List ι → A ≃ A
  | [] => Equiv.refl A
  | i :: is => (e i).trans (sequenceEquiv e is)

/-- Sequencing basis relabellings applies their composed equivalence. -/
theorem sequenceUnit_relabel [Fintype A] [DecidableEq A] (e : ι → A ≃ A) (is : List ι) :
    sequenceUnit (fun i ↦ relabel (e i)) is = relabel (sequenceEquiv e is) := by
  induction is with
  | nil => exact relabel_refl.symm
  | cons i is ih =>
    rw [sequenceUnit_cons, ih, relabel_bind_relabel]
    rfl

/-- Composing permutations that leave a second register alone still leaves it alone. -/
theorem sequenceEquiv_prodCongr (e : ι → A ≃ A) (is : List ι) (D : Type*) :
    sequenceEquiv (fun i ↦ (e i).prodCongr (Equiv.refl D)) is =
      (sequenceEquiv e is).prodCongr (Equiv.refl D) := by
  induction is with
  | nil => rfl
  | cons i is ih =>
    simp only [sequenceEquiv, ih]
    rfl

end SubInstrument

namespace SubInstrument

/-- Lifting a basis relabelling conjugates its permutation by the subsystem factorization. -/
theorem lift_relabel {A M : QReg} (S : Subsystem A M) (e : A ≃ A) :
    (relabel e).lift S =
      relabel (S.equiv.trans ((e.prodCongr (Equiv.refl S.rest)).trans S.equiv.symm)) := by
  apply DSubInstrument.ext
  funext u
  apply LinearMap.ext
  intro ρ
  rw [lift_branch_apply]
  change (((relabel e).frame S.rest).branch u
    (ρ.submatrix S.equiv.symm S.equiv.symm)).submatrix S.equiv S.equiv = _
  rw [frame_relabel, relabel_branch_apply, relabel_branch_apply]
  rfl

/-- A permutation on one coordinate and the shared memory lifts to that coordinate's
permutation when the memory is untouched. -/
theorem lift_relabel_piWithMemory {ι : Type} [Fintype ι] [DecidableEq ι]
    (i : ι) (A D : QReg) (e : A ≃ A) :
    ((relabel e).frame D).lift (Subsystem.piWithMemory i A D) =
      relabel ((piSlotEquiv i e).prodCongr (Equiv.refl D)) := by
  rw [frame_relabel, lift_relabel]
  congr 1
  apply Equiv.ext
  intro x
  apply (Subsystem.piWithMemory i A D).equiv.injective
  simp only [Equiv.trans_apply, Equiv.apply_symm_apply, Equiv.prodCongr_apply]
  change ((e (x.1 i), x.2), fun j : {j : ι // j ≠ i} ↦ x.1 j.1) =
    (((piSlotEquiv i e x.1) i, x.2),
      fun j : {j : ι // j ≠ i} ↦ piSlotEquiv i e x.1 j.1)
  apply Prod.ext
  · simp
  · funext j
    simp [j.property]

/-- Applying a permutation once to each index of a duplicate-free list changes exactly
the coordinates in that list. -/
theorem sequenceEquiv_piSlot_apply {ι A : Type} [DecidableEq ι]
    (e : A ≃ A) (is : List ι) (hi : is.Nodup) (x : ι → A) (j : ι) :
    sequenceEquiv (fun i ↦ piSlotEquiv i e) is x j =
      if j ∈ is then e (x j) else x j := by
  induction is generalizing x with
  | nil => simp [sequenceEquiv]
  | cons i is ih =>
    obtain ⟨hnot, hnodup⟩ := List.nodup_cons.mp hi
    simp only [sequenceEquiv, Equiv.trans_apply, ih hnodup, piSlotEquiv_apply]
    by_cases hji : j = i
    · subst j
      simp [hnot]
    · by_cases hj : j ∈ is <;> simp [hji, hj]

/-- Visiting every slot once composes to the pointwise permutation. -/
theorem sequenceEquiv_piSlot_finRange (A : QReg) (e : A ≃ A) (k : ℕ) :
    sequenceEquiv (fun i : Fin k ↦ piSlotEquiv i e) (List.finRange k) =
      Equiv.piCongrRight (fun _ : Fin k ↦ e) := by
  apply Equiv.ext
  intro x
  funext j
  simp [sequenceEquiv_piSlot_apply e _ (List.nodup_finRange k)]

/-- Apply a step to each slot in increasing order, sharing the same private memory. -/
@[expose]
noncomputable def batch (A D : QReg) (p : SubInstrument (A × D) (A × D) Unit) (k : ℕ) :
    SubInstrument ((Fin k → A) × D) ((Fin k → A) × D) Unit :=
  sequenceUnit (fun i ↦ p.lift (Subsystem.piWithMemory i A D)) (List.finRange k)

/-- A batch of width zero is the identity on its public and private registers. -/
@[simp]
theorem batch_zero (A D : QReg) (p : SubInstrument (A × D) (A × D) Unit) :
    batch A D p 0 = SubInstrument.pure () :=
  rfl

/-- A batch is lossless when the step applied to each slot is lossless. -/
theorem lossless_batch (A D : QReg) {p : SubInstrument (A × D) (A × D) Unit}
    (hp : p.Lossless) (k : ℕ) : (batch A D p k).Lossless :=
  lossless_sequenceUnit _ _ fun i _ ↦ hp.lift (Subsystem.piWithMemory i A D)

/-- For a basis permutation with untouched private memory, ordered batching agrees with
applying the permutation to every slot at once. -/
theorem batch_relabel_frame (A D : QReg) (e : A ≃ A) (k : ℕ) :
    batch A D ((relabel e).frame D) k =
      (relabel (Equiv.piCongrRight (fun _ : Fin k ↦ e))).frame D := by
  unfold batch
  simp_rw [lift_relabel_piWithMemory]
  rw [sequenceUnit_relabel, sequenceEquiv_prodCongr, sequenceEquiv_piSlot_finRange,
    frame_relabel]

end SubInstrument

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
