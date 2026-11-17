/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module
public import QuantumFoundations.SubInstrument.Subsystem
public import Mathlib.Data.List.FinRange

/-!
# Ordered operations on finite families of quantum registers

Coordinate subsystems select one register together with shared private memory. Ordered
sequences and batches of subinstruments act on these coordinates, and batches of basis
permutations that leave memory untouched agree with their pointwise action.

This foundational layer depends only on QuantumFoundations and Mathlib.
-/

public section

open Matrix

universe u v

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
    ((Equiv.funSplitAt i A).prodCongr (Equiv.refl D)).trans
      ((Equiv.prodAssoc A ({j : ι // j ≠ i} → A) D).trans
        ((Equiv.prodCongr (Equiv.refl A)
          (Equiv.prodComm ({j : ι // j ≠ i} → A) D)).trans
            (Equiv.prodAssoc A D ({j : ι // j ≠ i} → A)).symm))⟩

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

end Quantum
