/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.Quantum.Comp.QueryBound
public import VCVio.Quantum.Comp.Subsystem
public import PolyFun.IPFunctor.Free.Bound.Traversal

/-!
# Lifting programs along subsystems

A program `x` on the register `A` can run inside a larger register `M` that holds `A` as a
subsystem `S`, for instance when a reduction runs an adversary as a subroutine and keeps its own
workspace in the complement. `x.lift S` is that program: each local operation `o` of `x` acts on
the subsystem of `M` where `x`'s register now sits, each call exposes the same port register with
the complement carried in its remainder, and the complement is never touched.

The local operations of the lifted program are operations of `x`'s signature `L` applied to a
subsystem. They form the signature `L.framed` (`Quantum.LocalSig.framed`), interpreted by
`Quantum.LocalSig.Interp.framed`: relabel along the subsystem's factorization and apply the
operation framed by the complement. A program over `L.framed` may also apply its own operations
to named subsystems (`Quantum.QuantumComp.primAt`), without relabelling by hand.

A lifted leaf records where the original leaf sits: the leaf `y : X u` of `x` becomes the leaf
`⟨u, view, y⟩` on a register `v`, with `view : v ≃ u × S.rest`. The factorization is data, not an
equation between registers, so no statement here transports along an equality of registers.

This is the counterpart of `lift_program` in Unruh's AFP entry *Compressed Oracles*
(`Oracle_Programs.thy`), for adaptive programs with classical control and outcome-dependent
registers.

## Main definitions

* `Quantum.LocalSig.framed L`, `Quantum.LocalSig.Interp.framed I`.
* `Quantum.QuantumComp.LiftLeaf X F`: the leaves of a lifted program.
* `Quantum.QuantumComp.lift S x`, and `Quantum.QuantumComp.liftAux`, its recursion along a
  factorization `M ≃ A × F`.
* `Quantum.QuantumRuntime.unlift`: relabel each leaf of a lifted run back along its
  factorization.

## Main statements

* `Quantum.QuantumRuntime.run_lift`: running `x.lift S` and relabelling each leaf back along its
  factorization is relabelling along `S` and running `x` framed by the complement.
* `Quantum.QuantumComp.isQueryBound_lift_iff` and `isCostBound_lift_iff`: lifting preserves query
  budgets and operation costs exactly.
* `Quantum.QuantumRuntime.outcomeMeasure_unlift_run_lift`: started from `ρ` on the subsystem and
  a state of trace one on its complement, the lifted program's leaves are distributed as those of
  `x` from `ρ`.
* `Quantum.QuantumComp.Lossless.lift`: lifting preserves losslessness.
-/

public section

open IPFunctor MeasureTheory

universe u v u₁ v₁ w

namespace Quantum

/-! ## Operations on subsystems -/

namespace LocalSig

variable (L : LocalSig.{u, v})

/-- An operation of `L` on a subsystem of the register `M`. -/
structure FramedOp (M : QReg) : Type (max 1 u) where
  /-- The register of the subsystem. -/
  reg : QReg
  /-- The subsystem of `M` on which the operation acts. -/
  sub : Subsystem reg M
  /-- The operation. -/
  op : L.Op reg

/-- The signature whose operations on `M` are the operations of `L` on subsystems of `M`. An
operation keeps its outcomes, and on outcome `b` leaves the register `next op b × rest`. -/
@[expose, reducible]
def framed : LocalSig.{max 1 u, v} where
  Op := L.FramedOp
  Outcome o := L.Outcome o.op
  next o b := QReg.of (L.next o.op b × o.sub.rest)

variable {L}

/-- The operation `o` on the subsystem `S`. -/
abbrev FramedOp.mk' {A M : QReg} (S : Subsystem A M) (o : L.Op A) : L.framed.Op M :=
  ⟨A, S, o⟩

/-- The interpretation of `L.framed`: factor the register along the subsystem and apply the
interpretation of the operation, framed by the complement. -/
@[expose]
noncomputable def Interp.framed (I : L.Interp) : L.framed.Interp :=
  fun _ o ↦ DSubInstrument.bind (SubInstrument.relabel o.sub.equiv) fun _ ↦
    (I o.op).frame o.sub.rest

/-- The interpretation of an operation on a subsystem. -/
theorem Interp.framed_apply (I : L.Interp) {M : QReg} (o : L.framed.Op M) :
    I.framed o = DSubInstrument.bind (SubInstrument.relabel o.sub.equiv) fun _ ↦
      (I o.op).frame o.sub.rest :=
  rfl

/-- A lossless interpretation stays lossless on subsystems. -/
theorem Interp.Lossless.framed {I : L.Interp} (hI : I.Lossless) : I.framed.Lossless :=
  fun _ o ↦ DSubInstrument.Lossless.bind (SubInstrument.lossless_relabel _) fun _ ↦
    (hI o.op).frame _

end LocalSig

namespace QuantumComp

variable {L : LocalSig.{u, v}} {spec : QuantumOracleSpec.{u₁, v₁}} {X : QReg → Type w}
  {A M : QReg}

/-- Apply the operation `o` of `L` to the subsystem `S` of the register, and stop with its
outcome. -/
@[expose]
def primAt (S : Subsystem A M) (o : L.Op A) :
    QuantumComp L.framed spec (L.framed.OutcomeAt (LocalSig.FramedOp.mk' S o)) M :=
  prim (LocalSig.FramedOp.mk' S o)

/-! ## Lifting -/

/-- A leaf of a program lifted with the spectator `F`, on the register `v`: a leaf `leaf` of the
original program on its register `reg`, and the factorization `view : v ≃ reg × F`. -/
structure LiftLeaf (X : QReg → Type w) (F : QReg) (v : QReg) : Type (max 1 w) where
  /-- The register of the original leaf. -/
  reg : QReg
  /-- The factorization of the lifted register into the original register and the spectator. -/
  view : v ≃ reg × F
  /-- The original leaf. -/
  leaf : X reg

/-- Frame commands by `F`, carrying the factorization of the current register as state. -/
@[expose]
def liftTraversal (F : QReg) : Traversal (toIPFunctor L spec) (toIPFunctor L.framed spec)
    (fun A M ↦ M ≃ A × F) where
  op e
    | .prim o => .prim ⟨_, ⟨F, e⟩, o⟩
    | .query i E ℓ => .query i (QReg.of (E × F))
        (e.trans ((ℓ.prodCongr (Equiv.refl F)).trans (Equiv.prodAssoc _ _ _)))
  arg _ a b := by cases a <;> exact b
  next _ a _ := by
    cases a with
    | prim o => exact Equiv.refl _
    | query i E _ => exact (Equiv.prodAssoc (spec.Out i) E F).symm

/-- Lift a program on `A` into the register `M ≃ A × F`. A call keeps its port and moves the
spectator `F` into its remainder, so that the register after it is `Out i × (E × F)`, factored
back as `(Out i × E) × F`. -/
@[expose]
def liftAux (F : QReg) :
    {A : QReg} → IFreeM (toIPFunctor L spec) X A → (M : QReg) → (M ≃ A × F) →
      QuantumComp L.framed spec (LiftLeaf X F) M :=
  fun x _ e ↦ x.traverse (liftTraversal F) (fun e y ↦ .pure ⟨_, e, y⟩) e

/-- **Lifting a program along a subsystem.** Run `x` on the subsystem `S` of `M`, leaving the
complement of `S` untouched. -/
@[expose]
def lift (S : Subsystem A M) (x : QuantumComp L spec X A) :
    QuantumComp L.framed spec (LiftLeaf X S.rest) M :=
  liftAux S.rest x M S.equiv

variable (F : QReg)

/-- A lifted leaf records its factorization. -/
@[simp]
theorem liftAux_pure (x : X A) (e : M ≃ A × F) :
    liftAux (L := L) (spec := spec) F (QuantumComp.pure x) M e = QuantumComp.pure ⟨A, e, x⟩ :=
  rfl

/-- A lifted local operation acts on the subsystem given by the current factorization. -/
@[simp]
theorem liftAux_primBind (o : L.Op A)
    (k : (b : L.Outcome o) → QuantumComp L spec X (L.next o b)) (e : M ≃ A × F) :
    liftAux F (primBind o k) M e =
      primBind (L := L.framed) ⟨_, ⟨F, e⟩, o⟩ fun b ↦
        liftAux F (k b) (QReg.of (L.next o b × F)) (Equiv.refl _) :=
  rfl

/-- A lifted call moves the spectator into the remainder of the call. -/
@[simp]
theorem liftAux_queryBind (i : spec.Port) (E : QReg) (ℓ : A ≃ spec.In i × E)
    (k : spec.Result i → QuantumComp L spec X (QReg.of (spec.Out i × E))) (e : M ≃ A × F) :
    liftAux F (queryBind i E ℓ k) M e =
      queryBind i (QReg.of (E × F))
        (e.trans ((ℓ.prodCongr (Equiv.refl F)).trans (Equiv.prodAssoc _ _ _))) fun r ↦
        liftAux F (k r) _ (Equiv.prodAssoc (spec.Out i) E F).symm :=
  rfl

/-! ### Budgets and costs -/

/-- Lifting preserves the budget of every port exactly. -/
theorem isQueryBoundAt_liftAux_iff (x : QuantumComp L spec X A) (e : M ≃ A × F)
    (i : spec.Port) (n : ℕ) :
    (liftAux F x M e).IsQueryBoundAt i n ↔ x.IsQueryBoundAt i n := by
  refine IFreeM.isChargeBound_traverse_iff (liftTraversal F) _ ?_ ?_ ?_ e x n
  · intro A M e a; cases a <;> exact Function.surjective_id
  · intro A M e a; cases a <;> rfl
  · intro A M e y; trivial

/-- Lifting along a subsystem preserves query budgets exactly. -/
theorem isQueryBound_lift_iff (S : Subsystem A M) (x : QuantumComp L spec X A)
    (b : spec.Port → ℕ) : (x.lift S).IsQueryBound b ↔ x.IsQueryBound b :=
  forall_congr' fun i ↦ isQueryBoundAt_liftAux_iff _ x _ i (b i)

/-- Lifting preserves operation costs exactly, when an operation on a subsystem costs what the
operation costs. -/
theorem isCostBound_liftAux_iff (c : ∀ ⦃A : QReg⦄, L.Op A → ℕ) (x : QuantumComp L spec X A)
    (e : M ≃ A × F) (n : ℕ) :
    (liftAux F x M e).IsCostBound (fun _ (o : L.FramedOp _) ↦ c o.op) n ↔ x.IsCostBound c n := by
  refine IFreeM.isChargeBound_traverse_iff (liftTraversal F) _ ?_ ?_ ?_ e x n
  · intro A M e a; cases a <;> exact Function.surjective_id
  · intro A M e a; cases a <;> rfl
  · intro A M e y; trivial

/-- Lifting along a subsystem preserves operation costs exactly. -/
theorem isCostBound_lift_iff (c : ∀ ⦃A : QReg⦄, L.Op A → ℕ) (S : Subsystem A M)
    (x : QuantumComp L spec X A) (n : ℕ) :
    (x.lift S).IsCostBound (fun _ (o : L.FramedOp _) ↦ c o.op) n ↔ x.IsCostBound c n :=
  isCostBound_liftAux_iff _ c x _ n

/-- Lifting preserves losslessness. -/
theorem Lossless.liftAux {I : L.Interp} {x : QuantumComp L spec X A} (hx : x.Lossless I)
    (e : M ≃ A × F) : (liftAux F x M e).Lossless I.framed := by
  refine IFreeM.IsRollBound.traverse (liftTraversal F) _
    (fun _ _ _ ↦ True) ?_ ?_ ?_ hx trivial
  · intro A M e a _ _ _ ha
    cases a with
    | prim o =>
      exact DSubInstrument.Lossless.bind (SubInstrument.lossless_relabel _) fun _ ↦ ha.frame _
    | query => trivial
  · intros; trivial
  · intros; trivial

/-- Lifting along a subsystem preserves losslessness. -/
theorem Lossless.lift {I : L.Interp} {x : QuantumComp L spec X A} (hx : x.Lossless I)
    (S : Subsystem A M) : (x.lift S).Lossless I.framed :=
  hx.liftAux _ _

end QuantumComp

/-! ## Running a lifted program -/

namespace QuantumRuntime

open DSubInstrument SubInstrument QuantumComp

/-- The factorization `M × D ≃ (A × D) × F` that a factorization `M ≃ A × F` induces after the
runtime register `D` is adjoined. -/
@[expose]
def liftEquiv {M A F : Type*} (e : M ≃ A × F) (D : Type*) : M × D ≃ (A × D) × F :=
  (e.prodCongr (Equiv.refl D)).trans ((Equiv.prodAssoc A F D).trans
    (((Equiv.refl A).prodCongr (Equiv.prodComm F D)).trans (Equiv.prodAssoc A D F).symm))

/-- `liftEquiv` on a basis element. -/
@[simp]
theorem liftEquiv_apply {M A F : Type*} (e : M ≃ A × F) (D : Type*) (x : M × D) :
    liftEquiv e D x = (((e x.1).1, x.2), (e x.1).2) :=
  rfl

/-- The inverse of `liftEquiv` on a basis element. -/
@[simp]
theorem liftEquiv_symm_apply {M A F : Type*} (e : M ≃ A × F) (D : Type*) (x : (A × D) × F) :
    (liftEquiv e D).symm x = (e.symm (x.1.1, x.2), x.1.2) :=
  rfl

variable {spec : QuantumOracleSpec.{u₁, v₁}} (R : QuantumRuntime spec) {L : LocalSig.{u, v}}
  (I : L.Interp) {X : QReg → Type w} {A M : QReg}

/-- Relabel each leaf of a run of a lifted program back along its factorization, and keep only
the original leaf. -/
@[expose]
noncomputable def unlift {N : Type*} [Fintype N] {F : QReg}
    (p : DSubInstrument N (Σ v, LiftLeaf X F v) fun q ↦ q.1 × R.D) :
    DSubInstrument N (Σ u, X u) fun q ↦ (q.1 × R.D) × F :=
  p.bind fun q ↦ DSubInstrument.bind (relabel (liftEquiv q.2.view R.D)) fun _ ↦
    ret (fun q : Σ u, X u ↦ (q.1 × R.D) × F) ⟨q.2.reg, q.2.leaf⟩

/-- `unlift` after a step relabels the leaves of each continuation. -/
theorem unlift_bind {N : Type*} [Fintype N] {F : QReg} {ι : Type*} {B : ι → Type*}
    [∀ i, Fintype (B i)] (p : DSubInstrument N ι B)
    (k : (i : ι) → DSubInstrument (B i) (Σ v, LiftLeaf X F v) fun q ↦ q.1 × R.D) :
    R.unlift (p.bind k) = p.bind fun i ↦ R.unlift (k i) :=
  DSubInstrument.bind_assoc ..

/-- Swapping two frames commutes with a step, up to the relabelling of the inputs and of each
output. -/
theorem frame_frame_comm {ι : Type*} {Y : QReg} {B : ι → QReg} (F : QReg) (e : Y ≃ A × F)
    (p : DSubInstrument A ι fun i ↦ B i) :
    ((DSubInstrument.bind (relabel e) fun _ ↦ p.frame F).frame R.D).relabelOut
        (fun i ↦ liftEquiv (Equiv.refl (B i × F)) R.D) =
      DSubInstrument.bind (relabel (liftEquiv e R.D)) fun _ ↦ (p.frame R.D).frame F :=
  DSubInstrument.ext <| funext fun i ↦ LinearMap.ext fun ρ ↦ by
    ext x y
    simp only [relabelOut_branch_apply, branch_frame_apply, branch_bind_unit,
      MatrixMap.amplify_comp, LinearMap.comp_apply, relabel_branch_apply, Matrix.submatrix_apply,
      MatrixMap.amplify_apply, MatrixMap.amplify_apply_submatrix]
    rfl

/-- A call with the spectator moved into its remainder is the framed call, up to the
relabellings of the inputs and of the output. -/
theorem queryStep_liftAux (F : QReg) (i : spec.Port) (E : QReg) (ℓ : A ≃ spec.In i × E)
    (e : M ≃ A × F) :
    (R.queryStep i (QReg.of (E × F))
        (e.trans ((ℓ.prodCongr (Equiv.refl F)).trans (Equiv.prodAssoc _ _ _)))).relabelOut
        (fun _ ↦ liftEquiv (Equiv.prodAssoc (spec.Out i) E F).symm R.D) =
      DSubInstrument.bind (relabel (liftEquiv e R.D)) fun _ ↦ (R.queryStep i E ℓ).frame F :=
  DSubInstrument.ext <| funext fun r ↦ LinearMap.ext fun ρ ↦ by
    rw [relabelOut_branch_apply, queryStep_branch_apply]
    ext x y
    simp only [branch_frame_apply, branch_bind_unit, LinearMap.comp_apply, relabel_branch_apply,
      Matrix.submatrix_apply, MatrixMap.amplify_apply, queryStep_branch_apply]
    rfl

/-- **Running a lifted program.** Run `liftAux F x M e` and relabel each leaf back along its
factorization: this is relabelling `M × D` along `e` and running `x` framed by the spectator
`F`. -/
theorem unlift_run_liftAux (F : QReg) (x : QuantumComp L spec X A) (e : M ≃ A × F) :
    R.unlift (R.run I.framed (liftAux F x M e)) =
      DSubInstrument.bind (relabel (liftEquiv e R.D)) fun _ ↦ (R.run I x).frame F := by
  induction x using QuantumComp.inductionOn generalizing M with
  | pure _ y =>
    rw [liftAux_pure, run_pure, unlift, ret_bind, run_pure, frame_ret]
  | primBind _ o k ih =>
    rw [liftAux_primBind, run_primBind, unlift_bind]
    simp only [ih]
    rw [run_primBind, DSubInstrument.frame_bind, ← DSubInstrument.bind_assoc,
      ← frame_frame_comm R F e (I o), relabelOut_bind, LocalSig.Interp.framed_apply]
  | queryBind _ i E ℓ k ih =>
    rw [liftAux_queryBind, run_queryBind, unlift_bind]
    simp only [ih]
    rw [run_queryBind, DSubInstrument.frame_bind, ← DSubInstrument.bind_assoc,
      ← queryStep_liftAux R F i E ℓ e, relabelOut_bind]

/-- **Running a program lifted along a subsystem.** Running `x.lift S` and relabelling each leaf
back along its factorization is relabelling along `S` and running `x` with the complement of
`S` as a spectator. -/
theorem run_lift (S : Subsystem A M) (x : QuantumComp L spec X A) :
    R.unlift (R.run I.framed (x.lift S)) =
      DSubInstrument.bind (relabel (liftEquiv S.equiv R.D)) fun _ ↦ (R.run I x).frame S.rest :=
  R.unlift_run_liftAux I S.rest x S.equiv

/-- The outcome distribution after `unlift` forgets the factorization of each leaf. -/
theorem outcomeMeasure_unlift [MeasurableSpace (Σ u, X u)] {N : Type*} [Fintype N] {F : QReg}
    (p : DSubInstrument N (Σ v, LiftLeaf X F v) fun q ↦ q.1 × R.D) (σ : SubState N) :
    (R.unlift p).outcomeMeasure σ =
      Measure.sum fun q ↦ ENNReal.ofReal (p.branch q σ.matrix).trace.re •
        Measure.dirac (⟨q.2.reg, q.2.leaf⟩ : Σ u, X u) := by
  rw [unlift, outcomeMeasure_bind]
  congr 1
  funext q
  rw [outcomeMeasure_bind_unit, outcomeMeasure_ret, matrix_post, trace_relabel_branch_apply,
    matrix_post]

/-- **A subroutine with a spectator.** Run `x.lift S` from the state that is `ρ` on the subsystem
and `τ`, of trace one, on its complement. Forgetting the factorizations of the leaves, the leaves
are distributed as when `x` runs from `ρ`. -/
theorem outcomeMeasure_unlift_run_lift [MeasurableSpace (Σ u, X u)] (S : Subsystem A M)
    (x : QuantumComp L spec X A) (ρ : SubState A) (τ : SubState S.rest)
    (hτ : τ.matrix.trace = 1) :
    (R.unlift (R.run I.framed (x.lift S))).outcomeMeasure
        (((relabel S.equiv.symm).post (ρ.prod τ) ()).prod R.init) = R.evalDist I x ρ := by
  rw [run_lift, outcomeMeasure_bind_unit, outcomeMeasure_frame, evalDist]
  congr 1
  refine SubState.ext ?_
  ext ⟨a, d⟩ ⟨a', d'⟩
  simp only [SubState.matrix_traceRight, MatrixMap.traceRight_apply, matrix_post,
    relabel_branch_apply, Matrix.submatrix_apply, SubState.matrix_prod, Matrix.kroneckerMap_apply,
    liftEquiv_symm_apply, Equiv.symm_symm, Equiv.apply_symm_apply]
  rw [← Finset.sum_mul, ← Finset.mul_sum, show ∑ r, τ.matrix r r = 1 from hτ, mul_one]

end QuantumRuntime

end Quantum
