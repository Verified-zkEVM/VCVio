/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.Quantum.Comp.Simulation

/-!
# Subsystems of a register

A subsystem `A` of a register `M` (`Quantum.Subsystem A M`) is a factorization of the basis of
`M` as `A × rest`: a register `rest`, the complement, and a bijection `M ≃ A × rest`. It is the
finite-dimensional, constructive form of a quantum reference in the sense of Unruh (*Quantum
references*, [arXiv:2105.10914](https://arxiv.org/abs/2105.10914)): the reference
`X ↦ e⁻¹ (X ⊗ 1) e` of a subsystem with bijection `e` is a unital `*`-homomorphism, and every
such homomorphism on finite-dimensional systems has this form up to a unitary on `M`
(Unruh's `register_decomposition`). Keeping the complement as data is what lets a program act on
a subsystem: framing needs the complement as a register.

Subsystems compose like lenses. `Subsystem.fst` and `Subsystem.snd` are the factors of a product,
`Subsystem.comp` is a subsystem of a subsystem, `Subsystem.complement` is the complement, and
`Subsystem.pair` joins a subsystem and a subsystem of its complement. Disjointness is by
construction: the second subsystem of a pair lives in the complement of the first.

## Main definitions

* `Quantum.Subsystem A M`, with `whole`, `fst`, `snd`, `comp`, `complement` and `pair`.
* `Quantum.DSubInstrument.relabelOut p e`: relabel the output system of each branch of `p` along
  `e i`.
* `Quantum.SubInstrument.lift S p`: the subinstrument `p` on `A`, applied to the subsystem `S`
  of `M` and leaving its complement alone.

## Main statements

* `Quantum.SubInstrument.frame_relabel`: framing a relabelling relabels the product.
* `Quantum.DSubInstrument.outcomeMeasure_frame`: framing leaves the outcome distribution as on
  the reduced input state.
* `Quantum.SubInstrument.lift_branch_apply`: the branches of `p.lift S` are the branches of
  `p ⊗ id` conjugated by the factorization.
* `Quantum.SubInstrument.lift_comp`: lifting along a subsystem of a subsystem is lifting twice.
* `Quantum.SubInstrument.branch_lift_comm_complement`: branches acting on a subsystem and on its
  complement commute, the defining property of compatible references.
-/

public section

open Matrix

namespace Quantum

/-- A subsystem `A` of the register `M`: a register `rest`, the complement of `A`, and a
factorization `equiv : M ≃ A × rest` of the basis of `M`. -/
structure Subsystem (A M : QReg) where
  /-- The complement of the subsystem. -/
  rest : QReg
  /-- The factorization of the basis of `M` into the subsystem and its complement. -/
  equiv : M ≃ A × rest

namespace Subsystem

variable {A B M N : QReg}

/-- The whole register as a subsystem of itself, with a one-dimensional complement. -/
@[expose]
def whole (A : QReg) : Subsystem A A :=
  ⟨QReg.of Unit, (Equiv.prodPUnit A).symm⟩

/-- The left factor of a product register. -/
@[expose]
def fst (A B : QReg) : Subsystem A (QReg.of (A × B)) :=
  ⟨B, Equiv.refl _⟩

/-- The right factor of a product register. -/
@[expose]
def snd (A B : QReg) : Subsystem B (QReg.of (A × B)) :=
  ⟨A, Equiv.prodComm A B⟩

/-- The complement of a subsystem, as a subsystem whose complement is the original one. -/
@[expose]
def complement (S : Subsystem A M) : Subsystem S.rest M :=
  ⟨A, S.equiv.trans (Equiv.prodComm A S.rest)⟩

/-- A subsystem `S` of a subsystem `T` of `M` is a subsystem of `M`, whose complement collects
both complements. -/
@[expose]
def comp (T : Subsystem B M) (S : Subsystem A B) : Subsystem A M :=
  ⟨QReg.of (S.rest × T.rest),
    T.equiv.trans ((S.equiv.prodCongr (Equiv.refl T.rest)).trans
      (Equiv.prodAssoc A S.rest T.rest))⟩

/-- The pair of a subsystem `S` and a subsystem `T` of its complement: the two are disjoint by
construction, and together form the subsystem `A × B`. -/
@[expose]
def pair (S : Subsystem A M) (T : Subsystem B S.rest) : Subsystem (QReg.of (A × B)) M :=
  ⟨T.rest, S.equiv.trans (((Equiv.refl A).prodCongr T.equiv).trans
    (Equiv.prodAssoc A B T.rest).symm)⟩

/-- The whole register pairs each basis element with the unit. -/
@[simp]
theorem whole_equiv_apply (a : A) : (whole A).equiv a = (a, ()) :=
  rfl

/-- The left factor of a product is factored by the identity. -/
@[simp]
theorem fst_equiv_apply (x : A × B) : (fst A B).equiv x = x :=
  rfl

/-- The right factor of a product is factored by the swap. -/
@[simp]
theorem snd_equiv_apply (x : A × B) : (snd A B).equiv x = (x.2, x.1) :=
  rfl

/-- The complement swaps the factorization. -/
@[simp]
theorem complement_equiv_apply (S : Subsystem A M) (m : M) :
    S.complement.equiv m = ((S.equiv m).2, (S.equiv m).1) :=
  rfl

/-- A subsystem of a subsystem factors through both factorizations. -/
@[simp]
theorem comp_equiv_apply (T : Subsystem B M) (S : Subsystem A B) (m : M) :
    (T.comp S).equiv m = ((S.equiv (T.equiv m).1).1, (S.equiv (T.equiv m).1).2, (T.equiv m).2) :=
  rfl

/-- A pair factors through the first subsystem and then its complement. -/
@[simp]
theorem pair_equiv_apply (S : Subsystem A M) (T : Subsystem B S.rest) (m : M) :
    (S.pair T).equiv m = (((S.equiv m).1, (T.equiv (S.equiv m).2).1), (T.equiv (S.equiv m).2).2) :=
  rfl

/-- The complement of the complement factors `M` as the original subsystem does. -/
@[simp]
theorem complement_complement_equiv (S : Subsystem A M) :
    S.complement.complement.equiv = S.equiv :=
  Equiv.ext fun _ ↦ rfl

end Subsystem

/-! ## Relabelling the output of each branch -/

namespace DSubInstrument

variable {A ι : Type*} [Fintype A] {B C : ι → Type*} [∀ i, Fintype (B i)] [∀ i, Fintype (C i)]
  [∀ i, DecidableEq (B i)] [∀ i, DecidableEq (C i)]

/-- Relabel the output system of the branch at `i` along `e i : B i ≃ C i`. -/
@[expose]
noncomputable def relabelOut (p : DSubInstrument A ι B) (e : ∀ i, B i ≃ C i) :
    DSubInstrument A ι C :=
  p.bind fun i ↦ DSubInstrument.bind (SubInstrument.relabel (e i)) fun _ ↦ ret C i

/-- The branch at `i` of a relabelled subinstrument relabels the branch of `p` at `i`. -/
@[simp]
theorem relabelOut_branch_apply (p : DSubInstrument A ι B) (e : ∀ i, B i ≃ C i) (i : ι)
    (ρ : Matrix A A ℂ) :
    (p.relabelOut e).branch i ρ = (p.branch i ρ).submatrix (e i).symm (e i).symm := by
  rw [relabelOut, branch_bind_bind_unit_ret, LinearMap.comp_apply,
    SubInstrument.relabel_branch_apply]

/-- Relabelling the outputs preserves losslessness. -/
theorem Lossless.relabelOut {p : DSubInstrument A ι B} (hp : p.Lossless) (e : ∀ i, B i ≃ C i) :
    (p.relabelOut e).Lossless :=
  hp.bind fun i ↦ Lossless.bind (SubInstrument.lossless_relabel (e i)) fun _ ↦ lossless_ret _ _

/-- Sequencing after relabelled outputs relabels before each continuation. -/
theorem relabelOut_bind {κ : Type*} {D : κ → Type*} [∀ k, Fintype (D k)]
    (p : DSubInstrument A ι B) (e : ∀ i, B i ≃ C i) (k : (i : ι) → DSubInstrument (C i) κ D) :
    (p.relabelOut e).bind k =
      p.bind fun i ↦ DSubInstrument.bind (SubInstrument.relabel (e i)) fun _ ↦ k i := by
  rw [relabelOut, bind_assoc]
  congr 1
  funext i
  rw [bind_assoc]
  simp only [ret_bind]

end DSubInstrument

/-! ## The outcome distribution of a framed step -/

namespace DSubInstrument

/-- Framing does not change the outcome distribution, which depends only on the reduced input
state. -/
theorem outcomeMeasure_frame {A ι : Type*} [Fintype A] [MeasurableSpace ι] {B : ι → Type*}
    [∀ i, Fintype (B i)] (p : DSubInstrument A ι B) (R : Type*) [Fintype R]
    (σ : SubState (A × R)) :
    (p.frame R).outcomeMeasure σ = p.outcomeMeasure σ.traceRight := by
  simp only [outcomeMeasure_eq_sum, branch_frame_apply, MatrixMap.trace_amplify_apply,
    SubState.matrix_traceRight, MatrixMap.traceRight_eq_sum_submatrix, map_sum, Matrix.trace_sum]

end DSubInstrument

/-! ## Instruments on a subsystem -/

namespace SubInstrument

open DSubInstrument

variable {A B M : QReg} {α : Type*}

/-- A relabelling gate preserves the trace. -/
theorem trace_relabel_branch_apply {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq X]
    [DecidableEq Y] (e : X ≃ Y) (ρ : Matrix X X ℂ) :
    ((relabel e).branch () ρ).trace = ρ.trace := by
  rw [relabel_branch_apply]
  exact e.symm.sum_comp fun x ↦ ρ x x

/-- Framing a relabelling gate relabels the product along the bijection and the identity. -/
theorem frame_relabel {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]
    (e : X ≃ Y) (R : Type*) [Fintype R] [DecidableEq R] :
    (relabel e).frame R = relabel (e.prodCongr (Equiv.refl R)) :=
  DSubInstrument.ext <| funext fun u ↦ LinearMap.ext fun ρ ↦ by
    ext x y
    rw [branch_frame_apply, MatrixMap.amplify_apply, relabel_branch_apply, relabel_branch_apply]
    rfl

/-- **An instrument on a subsystem.** Apply `p` to the subsystem `S` of `M`: factor `M` as
`A × S.rest`, apply `p ⊗ id`, and undo the factorization. -/
@[expose]
noncomputable def lift (S : Subsystem A M) (p : SubInstrument A A α) : SubInstrument M M α :=
  (relabel S.equiv).bind fun _ ↦ (p.frame S.rest).relabelOut fun _ ↦ S.equiv.symm

/-- The branches of `p.lift S` are those of `p ⊗ id` conjugated by the factorization. -/
theorem lift_branch_apply (S : Subsystem A M) (p : SubInstrument A A α) (a : α)
    (ρ : Matrix M M ℂ) :
    (p.lift S).branch a ρ =
      ((p.branch a).amplify S.rest (ρ.submatrix S.equiv.symm S.equiv.symm)).submatrix
        S.equiv S.equiv := by
  rw [lift, SubInstrument.bind, branch_bind_unit, LinearMap.comp_apply, relabel_branch_apply,
    relabelOut_branch_apply, branch_frame_apply, Equiv.symm_symm]

/-- A subinstrument on a subsystem is lossless when the subinstrument is. -/
theorem Lossless.lift {p : SubInstrument A A α} (hp : p.Lossless) (S : Subsystem A M) :
    (p.lift S).Lossless :=
  (lossless_relabel _).bind fun _ ↦ DSubInstrument.Lossless.relabelOut (hp.frame _) _

/-- Lifting along a subsystem of a subsystem is lifting twice. -/
theorem lift_comp (T : Subsystem B M) (S : Subsystem A B) (p : SubInstrument A A α) :
    p.lift (T.comp S) = (p.lift S).lift T :=
  DSubInstrument.ext <| funext fun a ↦ LinearMap.ext fun ρ ↦ by
    ext m m'
    rw [lift_branch_apply, lift_branch_apply, submatrix_apply, submatrix_apply,
      MatrixMap.amplify_apply, MatrixMap.amplify_apply, lift_branch_apply, submatrix_apply,
      MatrixMap.amplify_apply]
    rfl

/-- On the whole register, the lift is the subinstrument itself. -/
@[simp]
theorem lift_whole (p : SubInstrument A A α) : p.lift (Subsystem.whole A) = p :=
  DSubInstrument.ext <| funext fun a ↦ LinearMap.ext fun ρ ↦ by
    ext m m'
    rw [lift_branch_apply, submatrix_apply, MatrixMap.amplify_apply]
    rfl

/-- The branches of a subinstrument on the complement of `S` act as `id ⊗ q` in the
factorization of `S`. -/
theorem lift_complement_branch_apply (S : Subsystem A M) {β : Type*}
    (q : SubInstrument S.rest S.rest β) (b : β) (ρ : Matrix M M ℂ) :
    (q.lift S.complement).branch b ρ =
      ((q.branch b).amplifyLeft A (ρ.submatrix S.equiv.symm S.equiv.symm)).submatrix
        S.equiv S.equiv := by
  ext m m'
  rw [lift_branch_apply, submatrix_apply, submatrix_apply, MatrixMap.amplify_apply,
    MatrixMap.amplifyLeft_apply]
  rfl

/-- **Compatibility.** A branch acting on a subsystem commutes with a branch acting on its
complement, as compatible references do. -/
theorem branch_lift_comm_complement (S : Subsystem A M) {β : Type*} (p : SubInstrument A A α)
    (q : SubInstrument S.rest S.rest β) (a : α) (b : β) :
    (p.lift S).branch a ∘ₗ (q.lift S.complement).branch b =
      (q.lift S.complement).branch b ∘ₗ (p.lift S).branch a := by
  refine LinearMap.ext fun ρ ↦ ?_
  rw [LinearMap.comp_apply, LinearMap.comp_apply, lift_complement_branch_apply,
    lift_complement_branch_apply, lift_branch_apply, lift_branch_apply, submatrix_submatrix,
    submatrix_submatrix, Equiv.self_comp_symm, submatrix_id_id, submatrix_id_id]
  exact congrArg (fun σ ↦ σ.submatrix S.equiv S.equiv) (LinearMap.congr_fun
    (MatrixMap.amplify_comp_amplifyLeft (p.branch a) (q.branch b)) _)

end SubInstrument

end Quantum
