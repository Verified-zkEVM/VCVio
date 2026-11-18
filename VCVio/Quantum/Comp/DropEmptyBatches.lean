/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module
public import VCVio.Quantum.Comp.Sequentialize

/-!
# Removing empty oracle rounds

A width-zero batch is a local register relabelling. Removing such calls preserves the complete
run, including runtime-private memory, and the point budget. Every retained call spends at least
one point, so the resulting round count is bounded by the original point budget. This permits
point-only corollaries without assuming that syntactic round counts are bounded by points.
-/

public section

open IPFunctor Matrix

namespace Quantum.QuantumComp

universe u v w uL vL
variable {P : Type u} {In : P → QReg}

/-- Interpret local operations, remove empty calls and retain positive-width batches. -/
@[expose]
noncomputable def dropEmptyBatchHandler {L : LocalSig.{uL, vL}} (I : L.Interp) :
    CommandSubstitution (toIPFunctor L (uBatchSpec P In))
      (toIPFunctor LocalSig.instruments.{vL} (uBatchSpec P In))
  | _, .prim o =>
      primBind (L := LocalSig.instruments.{vL}) (spec := uBatchSpec P In)
        ⟨L.Outcome o, fun b ↦ L.next o b, I o⟩ fun b ↦ QuantumComp.pure ⟨ULift.up b, rfl⟩
  | _, .query (_p, 0) _E e => relabelThen e (QuantumComp.pure ⟨ULift.up (), rfl⟩)
  | _, .query (p, k + 1) E e =>
      queryBind (p, k + 1) E e fun _ ↦ QuantumComp.pure ⟨ULift.up (), rfl⟩

/-- Remove width-zero calls without changing any returned register or classical outcome. -/
@[expose]
noncomputable def dropEmptyBatches {L : LocalSig.{uL, vL}} {W : QReg → Type w} {A : QReg}
    (I : L.Interp) (x : QuantumComp L (uBatchSpec P In) W A) :
    QuantumComp LocalSig.instruments.{vL} (uBatchSpec P In) W A :=
  IFreeM.substitute (dropEmptyBatchHandler I) x

variable {L : LocalSig.{uL, vL}} {W : QReg → Type w} {A : QReg}

/-- Returns are unchanged by empty-round removal. -/
@[simp]
theorem dropEmptyBatches_pure (I : L.Interp) (a : W A) :
    (QuantumComp.pure (L := L) (spec := uBatchSpec P In) a).dropEmptyBatches I =
      QuantumComp.pure a := rfl

/-- Local operations retain their outcome-dependent continuations. -/
@[simp]
theorem dropEmptyBatches_primBind (I : L.Interp) (o : L.Op A)
    (next : (b : L.Outcome o) → QuantumComp L (uBatchSpec P In) W (L.next o b)) :
    (primBind o next).dropEmptyBatches I =
      primBind (L := LocalSig.instruments.{vL}) (spec := uBatchSpec P In)
        ⟨L.Outcome o, fun b ↦ L.next o b, I o⟩ fun b ↦ (next b).dropEmptyBatches I := rfl

/-- An empty call becomes its public basis relabelling. -/
@[simp]
theorem dropEmptyBatches_queryBind_zero (I : L.Interp) (p : P) (E : QReg)
    (e : A ≃ (Fin 0 → In p) × E)
    (next : Unit → QuantumComp L (uBatchSpec P In) W (QReg.of ((Fin 0 → In p) × E))) :
    (queryBind (p, 0) E e next).dropEmptyBatches I =
      relabelThen e ((next ()).dropEmptyBatches I) := rfl

/-- Every positive-width call retains its original width and order. -/
@[simp]
theorem dropEmptyBatches_queryBind_succ (I : L.Interp) (p : P) (k : ℕ) (E : QReg)
    (e : A ≃ (Fin (k + 1) → In p) × E)
    (next : Unit → QuantumComp L (uBatchSpec P In) W
      (QReg.of ((Fin (k + 1) → In p) × E))) :
    (queryBind (p, k + 1) E e next).dropEmptyBatches I =
      queryBind (p, k + 1) E e fun r ↦ (next r).dropEmptyBatches I := rfl

/-- Each command replacement fits its original point charge. -/
theorem isPointBound_dropEmptyBatchHandler (I : L.Interp) (B : QReg)
    (c : Cmd L (uBatchSpec P In) B) :
    IsPointBound (dropEmptyBatchHandler I B c) c.pointCharge := by
  cases c with
  | prim o => simp [dropEmptyBatchHandler, Cmd.pointCharge]
  | query ik E e =>
    rcases ik with ⟨p, k⟩
    cases k <;> simp [dropEmptyBatchHandler, relabelThen, Cmd.pointCharge]

/-- A retained call costs one round and at least one point. -/
theorem isTotalQueryBound_dropEmptyBatchHandler_of_pointCharge (I : L.Interp) (B : QReg)
    (c : Cmd L (uBatchSpec P In) B) :
    IsTotalQueryBound (dropEmptyBatchHandler I B c) c.pointCharge := by
  cases c with
  | prim o => simp [dropEmptyBatchHandler, Cmd.pointCharge]
  | query ik E e =>
    rcases ik with ⟨p, k⟩
    cases k <;> simp [dropEmptyBatchHandler, relabelThen, Cmd.pointCharge]

/-- Empty-round removal preserves a total-call bound. -/
theorem isTotalQueryBound_dropEmptyBatchHandler (I : L.Interp) (B : QReg)
    (c : Cmd L (uBatchSpec P In) B) :
    IsTotalQueryBound (dropEmptyBatchHandler I B c) c.queryCharge := by
  cases c with
  | prim o => simp [dropEmptyBatchHandler, Cmd.queryCharge]
  | query ik E e =>
    rcases ik with ⟨p, k⟩
    cases k <;> simp [dropEmptyBatchHandler, relabelThen, Cmd.queryCharge]

/-- Removing empty calls preserves a point bound on every branch. -/
theorem IsPointBound.dropEmptyBatches (I : L.Interp)
    {x : QuantumComp L (uBatchSpec P In) W A} {n : ℕ} (hx : x.IsPointBound n) :
    (x.dropEmptyBatches I).IsPointBound n :=
  IFreeM.IsChargeBound.substitute (dropEmptyBatchHandler I)
    (isPointBound_dropEmptyBatchHandler I) hx

/-- After removing empty calls, points also bound rounds. -/
theorem IsPointBound.isTotalQueryBound_dropEmptyBatches (I : L.Interp)
    {x : QuantumComp L (uBatchSpec P In) W A} {n : ℕ} (hx : x.IsPointBound n) :
    (x.dropEmptyBatches I).IsTotalQueryBound n :=
  IFreeM.IsChargeBound.substitute (dropEmptyBatchHandler I)
    (isTotalQueryBound_dropEmptyBatchHandler_of_pointCharge I) hx

/-- Removing calls preserves an existing round bound. -/
theorem IsTotalQueryBound.dropEmptyBatches (I : L.Interp)
    {x : QuantumComp L (uBatchSpec P In) W A} {n : ℕ} (hx : x.IsTotalQueryBound n) :
    (x.dropEmptyBatches I).IsTotalQueryBound n :=
  IFreeM.IsChargeBound.substitute (dropEmptyBatchHandler I)
    (isTotalQueryBound_dropEmptyBatchHandler I) hx

end Quantum.QuantumComp

namespace Quantum.QuantumRuntime

universe u v w uL vL
variable {P : Type u} {In : P → QReg}
  (R : QuantumRuntime (uBatchSpec P In)) {L : LocalSig.{uL, vL}} (I : L.Interp)
  {W : QReg → Type w} {A : QReg}

/-- An empty port answered by the identity only relabels the public register. -/
theorem queryStep_zero_width (hzero : ∀ p, R.step (p, 0) = SubInstrument.pure ())
    (p : P) (E : QReg) (e : A ≃ (Fin 0 → In p) × E) :
    R.queryStep (p, 0) E e = (SubInstrument.relabel e).frame R.D := by
  apply DSubInstrument.ext
  funext r
  cases r
  apply LinearMap.ext
  intro ρ
  rw [queryStep_branch_apply, hzero, SubInstrument.frame_pure,
    SubInstrument.branch_pure_self, LinearMap.id_apply,
    SubInstrument.frame_relabel, SubInstrument.relabel_branch_apply,
    SubInstrument.relabel_branch_apply, SubInstrument.relabel_branch_apply]
  ext a b
  rfl

/-- Empty-round removal preserves the complete run whenever empty ports act as identity.
The same private register is retained at every step. -/
theorem run_dropEmptyBatches (hzero : ∀ p, R.step (p, 0) = SubInstrument.pure ())
    (x : QuantumComp L (uBatchSpec P In) W A) :
    R.run .instruments (x.dropEmptyBatches I) = R.run I x := by
  induction x using QuantumComp.inductionOn with
  | pure _ a => rw [QuantumComp.dropEmptyBatches_pure, run_pure, run_pure]
  | primBind _ o next ih =>
    rw [QuantumComp.dropEmptyBatches_primBind, run_primBind, run_primBind]
    exact congrArg _ (funext fun b ↦ ih b)
  | queryBind _ ik E e next ih =>
    rcases ik with ⟨p, k⟩
    cases k with
    | zero =>
      rw [QuantumComp.dropEmptyBatches_queryBind_zero, run_relabelThen, run_queryBind,
        queryStep_zero_width R hzero]
      exact congrArg _ (funext fun r ↦ by cases r; exact ih ())
    | succ k =>
      rw [QuantumComp.dropEmptyBatches_queryBind_succ, run_queryBind, run_queryBind]
      exact congrArg _ (funext fun r ↦ ih r)

end Quantum.QuantumRuntime
