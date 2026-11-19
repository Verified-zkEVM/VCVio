/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module
public import VCVio.Quantum.Comp.RoundBound

/-!
# Sequential execution of ordered quantum batches

The translation replaces each batch command by its ordered single-slot calls. Local basis
relabellings restore the public register after each slot. The oracle's private register remains
shared throughout the translation, including between adaptive branches and successive rounds.
-/

public section

open Matrix IPFunctor

universe u v w uL vL

namespace Quantum
namespace QuantumComp

variable {P : Type u} {In : P → QReg}

/-- Expose a slot of a batch, carrying its other slots and the caller's remainder together. -/
@[expose]
def batchSlotEquiv (p : P) (k : ℕ) (F : QReg) (i : Fin k) :
    (Fin k → In p) × F ≃ In p × (({j : Fin k // j ≠ i} → In p) × F) :=
  ((Equiv.funSplitAt i (In p)).prodCongr (Equiv.refl F)).trans (Equiv.prodAssoc _ _ _)

/-- A local basis relabelling followed by a continuation. -/
@[expose]
noncomputable def relabelThen {A B : QReg} {W : QReg → Type w} (e : A ≃ B)
    (x : QuantumComp LocalSig.instruments.{v} (uSpec P In) W B) :
    QuantumComp LocalSig.instruments.{v} (uSpec P In) W A :=
  primBind ⟨PUnit, fun _ ↦ B, SubInstrument.ofMap ((SubInstrument.relabel e).branch ())
    ((SubInstrument.relabel e).isCP_branch ())
    ((SubInstrument.relabel e).isCPTNIFamily.isTNI ())⟩ fun _ ↦ x

/-- Ordered calls on a list of slots, restoring the full public register after every call. -/
@[expose]
noncomputable def sequentializeSlots {W : QReg → Type w} (p : P) (k : ℕ) (F : QReg)
    (is : List (Fin k))
    (x : QuantumComp LocalSig.instruments.{v} (uSpec P In) W
      (QReg.of ((Fin k → In p) × F))) :
    QuantumComp LocalSig.instruments.{v} (uSpec P In) W
      (QReg.of ((Fin k → In p) × F)) :=
  match is with
  | [] => x
  | i :: is =>
      queryBind p (QReg.of (({j : Fin k // j ≠ i} → In p) × F))
        (batchSlotEquiv p k F i) fun _ ↦
          relabelThen (batchSlotEquiv p k F i).symm (sequentializeSlots p k F is x)

/-- The command handler implementing ordered batches through single-point ports. -/
@[expose]
noncomputable def sequentializeHandler {L : LocalSig.{uL, vL}} (I : L.Interp) :
    CommandSubstitution (toIPFunctor L (uBatchSpec P In))
      (toIPFunctor LocalSig.instruments.{vL} (uSpec P In))
  | _, .prim o =>
      primBind (L := LocalSig.instruments.{vL}) (spec := uSpec P In)
        ⟨L.Outcome o, fun b ↦ L.next o b, I o⟩ fun b ↦ QuantumComp.pure ⟨ULift.up b, rfl⟩
  | _, .query (p, k) F ℓ =>
      relabelThen ℓ (sequentializeSlots p k F (List.finRange k)
        (QuantumComp.pure ⟨ULift.up (), rfl⟩))

/-- Replace every ordered batch by single-point calls in increasing slot order. -/
@[expose]
noncomputable def sequentialize {L : LocalSig.{uL, vL}} {W : QReg → Type w} {A : QReg}
    (I : L.Interp) (x : QuantumComp L (uBatchSpec P In) W A) :
    QuantumComp LocalSig.instruments.{vL} (uSpec P In) W A :=
  IFreeM.substitute (sequentializeHandler I) x

variable {W : QReg → Type w} {A : QReg}

/-- Returning a value is unchanged by sequentialization. -/
@[simp]
theorem sequentialize_pure {L : LocalSig.{uL, vL}} (I : L.Interp) (x : W A) :
    (QuantumComp.pure (L := L) (spec := uBatchSpec P In) x).sequentialize I =
      QuantumComp.pure x := rfl

/-- Sequentialization interprets local operations and retains their adaptive outcomes. -/
@[simp]
theorem sequentialize_primBind {L : LocalSig.{uL, vL}} (I : L.Interp) (o : L.Op A)
    (next : (b : L.Outcome o) → QuantumComp L (uBatchSpec P In) W (L.next o b)) :
    (primBind o next).sequentialize I =
      primBind (L := LocalSig.instruments.{vL}) (spec := uSpec P In)
        ⟨L.Outcome o, fun b ↦ L.next o b, I o⟩ fun b ↦ (next b).sequentialize I := rfl

/-- Relabelling only affects the starting register of a continuation. -/
theorem relabelThen_bind {B : QReg} (e : A ≃ B)
    (x : QuantumComp LocalSig.instruments.{v} (uSpec P In) W B)
    {Z : QReg → Type*} (next : ∀ a, W a → QuantumComp LocalSig.instruments.{v} (uSpec P In) Z a) :
    (relabelThen e x).bind next = relabelThen e (x.bind next) := rfl

/-- Sequencing after a slot list sequences its continuation. -/
theorem sequentializeSlots_bind (p : P) (k : ℕ) (F : QReg) (is : List (Fin k))
    (x : QuantumComp LocalSig.instruments.{v} (uSpec P In) W
      (QReg.of ((Fin k → In p) × F)))
    {Z : QReg → Type*} (next : ∀ a, W a → QuantumComp LocalSig.instruments.{v} (uSpec P In) Z a) :
    (sequentializeSlots p k F is x).bind next = sequentializeSlots p k F is (x.bind next) := by
  induction is with
  | nil => rfl
  | cons i is ih =>
    simp only [sequentializeSlots, queryBind_bind, relabelThen_bind, ih]

/-- A batch call becomes the ordered list of calls, with its original continuation. -/
theorem sequentialize_queryBind {L : LocalSig.{uL, vL}} (I : L.Interp) (p : P) (k : ℕ) (F : QReg)
    (ℓ : A ≃ (Fin k → In p) × F)
    (next : Unit → QuantumComp L (uBatchSpec P In) W
      (QReg.of ((Fin k → In p) × F))) :
    (queryBind (spec := uBatchSpec P In) (p, k) F ℓ next).sequentialize I =
      relabelThen ℓ (sequentializeSlots p k F (List.finRange k) ((next ()).sequentialize I)) := by
  change (relabelThen (P := P) (In := In) ℓ (sequentializeSlots p k F (List.finRange k)
    (QuantumComp.pure (X := fun B ↦ {b : ULift.{vL} Unit //
      QReg.of ((Fin k → In p) × F) = B}) ⟨ULift.up (), rfl⟩))).bind
    (fun B (answer : {b : ULift.{vL} Unit // QReg.of ((Fin k → In p) × F) = B}) ↦
      answer.2 ▸ (next answer.1.down).sequentialize I) = _
  rw [relabelThen_bind, sequentializeSlots_bind]
  rfl

/-- A width-zero batch performs only the public basis relabelling and its continuation. -/
@[simp]
theorem sequentialize_queryBind_zero {L : LocalSig.{uL, vL}} (I : L.Interp) (p : P) (F : QReg)
    (ℓ : A ≃ (Fin 0 → In p) × F)
    (next : Unit → QuantumComp L (uBatchSpec P In) W
      (QReg.of ((Fin 0 → In p) × F))) :
    (queryBind (spec := uBatchSpec P In) (p, 0) F ℓ next).sequentialize I =
      relabelThen ℓ ((next ()).sequentialize I) := by
  rw [sequentialize_queryBind]
  rfl

/-- Sequentialization commutes with dependent program sequencing. -/
theorem sequentialize_bind {L : LocalSig.{uL, vL}} (I : L.Interp)
    (x : QuantumComp L (uBatchSpec P In) W A) {Z : QReg → Type*}
    (next : ∀ a, W a → QuantumComp L (uBatchSpec P In) Z a) :
    (x.bind next).sequentialize I =
      (x.sequentialize I).bind fun a b ↦ (next a b).sequentialize I :=
  IFreeM.substitute_bind (sequentializeHandler I) x next

/-- The ordered calls consume exactly one unit of available budget per listed slot. -/
theorem isTotalQueryBound_sequentializeSlots (p : P) (k : ℕ) (F : QReg)
    (is : List (Fin k)) {x : QuantumComp LocalSig.instruments.{v} (uSpec P In) W
      (QReg.of ((Fin k → In p) × F))} {n : ℕ} (hx : x.IsTotalQueryBound n) :
    (sequentializeSlots p k F is x).IsTotalQueryBound (is.length + n) := by
  induction is with
  | nil => simpa [sequentializeSlots] using hx
  | cons i is ih =>
    simp only [sequentializeSlots, isTotalQueryBound_queryBind_iff, relabelThen,
      isTotalQueryBound_primBind_iff, List.length_cons]
    exact ⟨by omega, fun _ _ ↦ by simpa using ih⟩

/-- The replacement of one batch command fits its point charge. -/
theorem isTotalQueryBound_sequentializeHandler {L : LocalSig.{uL, vL}} (I : L.Interp)
    (B : QReg) (c : Cmd L (uBatchSpec P In) B) :
    IsTotalQueryBound (L := LocalSig.instruments.{vL}) (s := uSpec P In)
      (sequentializeHandler I B c) c.pointCharge := by
  cases c with
  | prim o =>
    change (primBind (L := LocalSig.instruments.{vL}) (spec := uSpec P In)
        ⟨L.Outcome o, fun b ↦ L.next o b, I o⟩
      fun b ↦ QuantumComp.pure (X := fun C ↦ {b : ULift (L.Outcome o) //
        L.next o b.down = C}) ⟨ULift.up b, rfl⟩).IsTotalQueryBound 0
    exact (isTotalQueryBound_primBind_iff _ _ _).mpr fun _ ↦ isTotalQueryBound_pure _ _
  | query ik F ℓ =>
    rcases ik with ⟨p, k⟩
    dsimp only [sequentializeHandler, Cmd.pointCharge]
    simp only [relabelThen, isTotalQueryBound_primBind_iff]
    intro _
    simpa only [List.length_finRange, Nat.add_zero, toIPFunctor, Cmd.next, Cmd.Resp,
      uBatchSpec, uSpec] using
      isTotalQueryBound_sequentializeSlots p k F (List.finRange k)
        (isTotalQueryBound_pure (L := LocalSig.instruments.{vL}) (s := uSpec P In)
          (X := fun C ↦ {b : ULift.{vL} Unit // QReg.of ((Fin k → In p) × F) = C})
          ⟨ULift.up (), rfl⟩ 0)

/-- A path-wise point budget becomes the same total sequential query budget. -/
theorem IsPointBound.sequentialize {L : LocalSig.{uL, vL}} (I : L.Interp)
    {x : QuantumComp L (uBatchSpec P In) W A} {n : ℕ} (hx : x.IsPointBound n) :
    (x.sequentialize I).IsTotalQueryBound n :=
  IFreeM.IsChargeBound.substitute (sequentializeHandler I)
    (isTotalQueryBound_sequentializeHandler I) hx

/-- A round budget and a per-call width cap give the product bound after sequentialization. -/
theorem IsTotalQueryBound.sequentialize {L : LocalSig.{uL, vL}} (I : L.Interp)
    {x : QuantumComp L (uBatchSpec P In) W A} {r k : ℕ}
    (hr : x.IsTotalQueryBound r) (hw : x.IsWidthBound k) :
    (x.sequentialize I).IsTotalQueryBound (k * r) :=
  (hr.isPointBound hw).sequentialize I

/-- Relabelling the public basis preserves syntactic losslessness. -/
theorem lossless_relabelThen {B : QReg} (e : A ≃ B)
    {x : QuantumComp LocalSig.instruments.{v} (uSpec P In) W B}
    (hx : x.Lossless .instruments) : (relabelThen e x).Lossless .instruments := by
  rw [relabelThen, lossless_primBind_iff]
  refine ⟨?_, fun _ ↦ hx⟩
  change (SubInstrument.ofMap ((SubInstrument.relabel e).branch ())
    ((SubInstrument.relabel e).isCP_branch ())
    ((SubInstrument.relabel e).isCPTNIFamily.isTNI ())).Lossless
  apply (DSubInstrument.lossless_iff_isTP_total _).mpr
  rw [DSubInstrument.total_ofMap]
  intro ρ
  exact SubInstrument.trace_relabel_branch_apply e ρ

/-- The inserted slot calls and basis relabellings preserve syntactic losslessness. -/
theorem lossless_sequentializeSlots (p : P) (k : ℕ) (F : QReg) (is : List (Fin k))
    {x : QuantumComp LocalSig.instruments.{v} (uSpec P In) W
      (QReg.of ((Fin k → In p) × F))} (hx : x.Lossless .instruments) :
    (sequentializeSlots p k F is x).Lossless .instruments := by
  induction is with
  | nil => exact hx
  | cons i is ih =>
    rw [sequentializeSlots, lossless_queryBind_iff]
    exact fun _ ↦ lossless_relabelThen _ ih

/-- Sequentialization preserves syntactic losslessness under the supplied local interpretation. -/
theorem Lossless.sequentialize {L : LocalSig.{uL, vL}} {I : L.Interp}
    {x : QuantumComp L (uBatchSpec P In) W A} (hx : x.Lossless I) :
    (x.sequentialize I).Lossless .instruments := by
  induction x using QuantumComp.inductionOn with
  | pure _ _ => trivial
  | primBind _ o next ih =>
    rw [sequentialize_primBind, lossless_primBind_iff]
    exact ⟨hx.1, fun b ↦ ih b (hx.2 (ULift.up b))⟩
  | queryBind _ ik F ℓ next ih =>
    rcases ik with ⟨p, k⟩
    rw [sequentialize_queryBind]
    exact lossless_relabelThen _ (lossless_sequentializeSlots _ _ _ _ (ih () (hx.2 (ULift.up ()))))

end QuantumComp
namespace QuantumRuntime

variable {P : Type u} {In : P → QReg} (R : QuantumRuntime (uSpec P In))

/-- Calling a port and restoring the public basis applies its step on the exposed subsystem. -/
theorem queryStep_bind_relabel_symm {A : QReg} (p : P) (E : QReg) (ℓ : A ≃ In p × E) :
    (R.queryStep p E ℓ).bind (fun _ ↦ (SubInstrument.relabel ℓ.symm).frame R.D) =
      (R.step p).lift (⟨E, queryEquivIn ℓ R.D⟩ :
        Subsystem (QReg.of (In p × R.D)) (QReg.of (A × R.D))) := by
  apply DSubInstrument.ext
  funext r
  cases r
  apply LinearMap.ext
  intro ρ
  rw [DSubInstrument.branch_bind_apply_univ]
  simp only [Fintype.sum_unique, LinearMap.comp_apply]
  change ((SubInstrument.relabel ℓ.symm).frame R.D).branch ()
      ((R.queryStep p E ℓ).branch () ρ) = _
  rw [DSubInstrument.branch_frame_apply, queryStep_branch_apply,
    SubInstrument.lift_branch_apply]
  ext x y
  simp only [MatrixMap.amplify_apply, SubInstrument.relabel_branch_apply,
    Matrix.submatrix_apply]
  rfl

/-- A restored slot call carries the caller's remainder as an untouched frame. -/
theorem lift_batchSlotEquiv (p : P) (k : ℕ) (F : QReg) (i : Fin k) :
    (R.step p).lift (⟨QReg.of (({j : Fin k // j ≠ i} → In p) × F),
        queryEquivIn (QuantumComp.batchSlotEquiv p k F i) R.D⟩ :
      Subsystem (QReg.of (In p × R.D)) (QReg.of (((Fin k → In p) × F) × R.D))) =
      (((R.step p).lift (Subsystem.piWithMemory i (In p) R.D)).frame F).reindex
        (queryEquivIn (Equiv.refl ((Fin k → In p) × F)) R.D).symm
        (queryEquivIn (Equiv.refl ((Fin k → In p) × F)) R.D).symm := by
  apply DSubInstrument.ext
  funext r
  apply LinearMap.ext
  intro ρ
  rw [SubInstrument.lift_branch_apply, SubInstrument.branch_reindex_apply,
    DSubInstrument.branch_frame_apply]
  ext x y
  simp only [MatrixMap.amplify_apply, Matrix.submatrix_apply]
  rw [SubInstrument.lift_branch_apply (Subsystem.piWithMemory i (In p) R.D) (R.step p) r]
  simp only [MatrixMap.amplify_apply, Matrix.submatrix_apply]
  rfl

variable {W : QReg → Type w}

/-- Relabelling a public register commutes with adjoining the runtime memory. -/
theorem run_relabelThen {A B : QReg} (e : A ≃ B)
    (x : QuantumComp LocalSig.instruments.{v} (uSpec P In) W B) :
    R.run .instruments (QuantumComp.relabelThen e x) =
      DSubInstrument.bind ((SubInstrument.relabel e).frame R.D) fun _ ↦ R.run .instruments x := by
  rw [QuantumComp.relabelThen, run_primBind]
  apply DSubInstrument.ext
  funext p
  simp only [DSubInstrument.branch_bind_apply_univ, Fintype.sum_unique,
    LocalSig.Interp.instruments_apply, DSubInstrument.branch_frame_apply,
    SubInstrument.branch_ofMap]

/-- A translated slot list executes the ordered lifted steps on one shared private register. -/
theorem run_sequentializeSlots (p : P) (k : ℕ) (F : QReg) (is : List (Fin k))
    (x : QuantumComp LocalSig.instruments.{v} (uSpec P In) W
      (QReg.of ((Fin k → In p) × F))) :
    R.run .instruments (QuantumComp.sequentializeSlots p k F is x) =
      DSubInstrument.bind (SubInstrument.sequenceUnit (fun i ↦
        (R.step p).lift (⟨QReg.of (({j : Fin k // j ≠ i} → In p) × F),
          queryEquivIn (QuantumComp.batchSlotEquiv p k F i) R.D⟩ :
          Subsystem (QReg.of (In p × R.D)) (QReg.of (((Fin k → In p) × F) × R.D)))) is)
        fun _ ↦ R.run .instruments x := by
  induction is with
  | nil => simp [QuantumComp.sequentializeSlots, SubInstrument.sequenceUnit_nil]
  | cons i is ih =>
    rw [QuantumComp.sequentializeSlots, run_queryBind]
    simp only [run_relabelThen, ih]
    rw [← DSubInstrument.bind_assoc]
    have h := R.queryStep_bind_relabel_symm (A := QReg.of ((Fin k → In p) × F)) p
      (QReg.of (({j : Fin k // j ≠ i} → In p) × F)) (QuantumComp.batchSlotEquiv (In := In) p k F i)
    exact (congrArg (fun z ↦ DSubInstrument.bind z fun _ ↦
      DSubInstrument.bind (SubInstrument.sequenceUnit (fun i ↦
        (R.step p).lift (⟨QReg.of (({j : Fin k // j ≠ i} → In p) × F),
          queryEquivIn (QuantumComp.batchSlotEquiv p k F i) R.D⟩ :
          Subsystem (QReg.of (In p × R.D)) (QReg.of (((Fin k → In p) × F) × R.D)))) is)
        fun _ ↦ R.run .instruments x) h).trans (DSubInstrument.bind_assoc ..).symm

/-- Query steps on endomorphism ports are basis transports of their framed runtime steps. -/
theorem queryStep_eq_reindex {A : QReg} (p : P) (F : QReg) (ℓ : A ≃ In p × F) :
    R.queryStep p F ℓ = ((R.step p).frame F).reindex
      (queryEquivIn ℓ R.D).symm (queryEquivOut (In p) R.D F) := by
  apply DSubInstrument.ext
  funext r
  apply LinearMap.ext
  intro ρ
  rw [queryStep_branch_apply, SubInstrument.branch_reindex_apply,
    SubInstrument.relabel_branch_apply, SubInstrument.relabel_branch_apply]

/-- A complete list of slots executes the corresponding ordered batch query. -/
theorem run_sequentializeSlots_finRange (p : P) (k : ℕ) (F : QReg)
    (x : QuantumComp LocalSig.instruments.{v} (uSpec P In) W
      (QReg.of ((Fin k → In p) × F))) :
    R.run .instruments (QuantumComp.sequentializeSlots p k F (List.finRange k) x) =
      DSubInstrument.bind (R.batch.queryStep (A := QReg.of ((Fin k → In p) × F))
        (p, k) F (Equiv.refl _)) fun _ ↦ R.run .instruments x := by
  dsimp +instances only [batch, uBatchSpec, uSpec]
  rw [run_sequentializeSlots]
  simp_rw [R.lift_batchSlotEquiv p k F]
  rw [SubInstrument.sequenceUnit_reindex, SubInstrument.sequenceUnit_frame]
  rw [queryStep_eq_reindex]
  rfl

/-- Relabelling the initial public register gives the same batch query in that layout. -/
theorem relabel_bind_batch_queryStep {A : QReg} (p : P) (k : ℕ) (F : QReg)
    (ℓ : A ≃ (Fin k → In p) × F) :
    ((SubInstrument.relabel ℓ).frame R.D).bind
        (fun _ ↦ R.batch.queryStep (A := QReg.of ((Fin k → In p) × F)) (p, k) F (Equiv.refl _)) =
      R.batch.queryStep (p, k) F ℓ := by
  dsimp +instances only [batch, uBatchSpec, uSpec]
  rw [SubInstrument.frame_relabel]
  apply DSubInstrument.ext
  funext r
  apply LinearMap.ext
  intro ρ
  rw [DSubInstrument.branch_bind_apply_univ]
  simp only [Fintype.sum_unique, LinearMap.comp_apply]
  rw [queryStep_branch_apply, queryStep_branch_apply]
  simp only [DSubInstrument.branch_frame_apply, SubInstrument.relabel_branch_apply]
  ext x y
  simp only [MatrixMap.amplify_apply, Matrix.submatrix_apply]
  rfl

/-- Sequentialization preserves the full dependent output instrument for arbitrary stateful
runtimes. The equality includes the private memory and every final register. -/
theorem run_sequentialize {L : LocalSig.{uL, vL}} (I : L.Interp) {A : QReg}
    (x : QuantumComp L (uBatchSpec P In) W A) :
    R.run .instruments (x.sequentialize I) = R.batch.run I x := by
  induction x using QuantumComp.inductionOn with
  | pure _ _ => rfl
  | primBind _ o next ih =>
    rw [QuantumComp.sequentialize_primBind, run_primBind, run_primBind]
    exact congrArg (((I o).frame R.D).bind) (funext ih)
  | queryBind _ ik F ℓ next ih =>
    rcases ik with ⟨p, k⟩
    rw [QuantumComp.sequentialize_queryBind, run_relabelThen, run_sequentializeSlots_finRange]
    dsimp +instances only [batch, uBatchSpec, uSpec]
    rw [← DSubInstrument.bind_assoc]
    have h := R.relabel_bind_batch_queryStep p k F ℓ
    dsimp +instances only [batch, uBatchSpec, uSpec] at h
    dsimp only [SubInstrument.bind] at h
    rw [h, run_queryBind]
    exact congrArg (DSubInstrument.bind (R.batch.queryStep (p, k) F ℓ)) (funext fun _ ↦ ih ())

/-- The complete joint post-state is preserved, including the oracle's private register. -/
theorem jointPost_sequentialize {L : LocalSig.{uL, vL}} (I : L.Interp) {A : QReg}
    (x : QuantumComp L (uBatchSpec P In) W A) (ρ : SubState A) (p : Σ a, W a) :
    R.jointPost .instruments (x.sequentialize I) ρ p = R.batch.jointPost I x ρ p := by
  simp only [jointPost, run_sequentialize, batch_init]
  rfl

/-- Sequentialization preserves the complete output law. -/
theorem evalDist_sequentialize {L : LocalSig.{uL, vL}} (I : L.Interp) {A : QReg}
    [MeasurableSpace (Σ a, W a)] (x : QuantumComp L (uBatchSpec P In) W A)
    (ρ : SubState A) :
    R.evalDist .instruments (x.sequentialize I) ρ = R.batch.evalDist I x ρ := by
  simp only [evalDist, run_sequentialize, batch_init]
  rfl

/-- Every classical observation of the output has the same law after sequentialization. -/
theorem evalDistMap_sequentialize {L : LocalSig.{uL, vL}} (I : L.Interp) {A : QReg}
    (x : QuantumComp L (uBatchSpec P In) W A) {γ : Type*} [MeasurableSpace γ]
    (ρ : SubState A) (f : (Σ a, W a) → γ) :
    R.evalDistMap .instruments (x.sequentialize I) ρ f = R.batch.evalDistMap I x ρ f := by
  simp only [evalDistMap, jointPost_sequentialize]
  rfl

end QuantumRuntime

end Quantum
