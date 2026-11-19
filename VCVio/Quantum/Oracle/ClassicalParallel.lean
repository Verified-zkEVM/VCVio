/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module
public import VCVio.OracleComp.QueryTracking.QueryBound.Batch
public import VCVio.Quantum.Oracle.ClassicalCalls
public import VCVio.Quantum.Oracle.Sequentialize

/-!
# Classical rounds in the parallel quantum random-oracle model

Each classical round prepares one register pair per list position, makes one call of that
width, and measures all response slots. Local uniform samples use quantum local coins and
make no oracle call. A single function supplies every slot and every adaptive round.
The classical source and result types lie in `Type`, following the classical simulation API.
-/

public section

open MeasureTheory OracleSpec OracleComp
open scoped ENNReal Kronecker

namespace Quantum

variable {X Y α : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] [AddCommGroup Y]

/-- A classical round as one parallel oracle call, with slot `j` holding `ts[j]`. -/
@[expose]
noncomputable def classicalBatchQuery (ts : List X) :
    QComp (qromBatchSpec X Y) (QReg.of Unit) (QReg.of Unit) (Fin ts.length → Y) :=
  (QComp.act (B := QReg.of (Fin ts.length → X × Y))
    (DSubInstrument.classical (B := fun _ ↦ Fin ts.length → X × Y)
      (fun _ : Unit ↦ ()) (fun _ j ↦ (ts[j], (0 : Y))))).bind fun _ ↦
    (QuantumComp₂.query (L := LocalSig.instruments) (spec := qromBatchSpec X Y)
      ((), ts.length) (QReg.of Unit) (Equiv.prodPUnit _).symm).bind fun _ ↦
      QComp.act (A := QReg.of ((Fin ts.length → X × Y) × Unit))
        (DSubInstrument.classical (B := fun _ ↦ Unit)
          (fun m ↦ fun j ↦ (m.1 j).2) (fun _ ↦ ()))

/-- Local coins together with one parallel basis call for each classical round. -/
@[expose]
noncomputable def classicalBatchImpl :
    QueryImpl (unifSpec + (X →ₒ Y).batch)
      (QComp (qromBatchSpec X Y) (QReg.of Unit) (QReg.of Unit)) :=
  fun t ↦ match t with
    | .inl n => QComp.coinImpl (qromBatchSpec X Y) (QReg.of Unit) n
    | .inr ts => classicalBatchQuery (Y := Y) ts

/-- A classical round is lossless, including empty rounds and repeated inputs. -/
theorem lossless_classicalBatchQuery (ts : List X) :
    (classicalBatchQuery (Y := Y) ts).Lossless .instruments :=
  QuantumComp₂.lossless_bind (QComp.lossless_act (DSubInstrument.lossless_classical _ _)) fun _ ↦
    QuantumComp₂.lossless_bind (QuantumComp₂.lossless_query _ _ _) fun _ ↦
      QComp.lossless_act (DSubInstrument.lossless_classical _ _)

/-- The fixed-function parallel runtime applies the same function to every basis slot. -/
theorem parallelOracleRuntime_step_branch_single (H : X → Y) (k : ℕ) (m : Fin k → X × Y)
    (d : (parallelOracleRuntime H).D) :
    ((parallelOracleRuntime H).step ((),k)).branch () (Matrix.single (m,d) (m,d) 1) =
    Matrix.single ((parallelOracleEquiv H k) m,d) ((parallelOracleEquiv H k) m,d) 1 := by
  change Unit at d
  rw [parallelOracleRuntime_step]
  change (((parallelOracleQuery H k).frame Unit).branch ()) (Matrix.single (m,d) (m,d) (1 : ℂ)) = _
  rw [DSubInstrument.branch_frame_single, branch_parallelOracleQuery]
  unfold parallelOracleUnitary
  rw [conj_basisMatrix_equiv_single, Matrix.single_kronecker_single, one_mul]
  rfl

/-- A basis round returns the function value at every list position with certainty. -/
theorem run_classicalBatchQuery_branch (H : X → Y) (ts : List X) (d : (parallelOracleRuntime H).D)
    (ys : Fin ts.length → Y) :
    ((parallelOracleRuntime H).run₂ .instruments (classicalBatchQuery ts)).branch ys
      (Matrix.single ((),d) ((),d) 1) =
      if (fun j : Fin ts.length ↦ H ts[j]) = ys then Matrix.single ((),d) ((),d) 1 else 0 := by
  classical
  rw [classicalBatchQuery, QuantumRuntime.run₂_act_bind, DSubInstrument.branch_bind_unit,
    LinearMap.comp_apply, DSubInstrument.branch_frame_single, DSubInstrument.branch_classical_basis]
  simp only [↓reduceDIte, cast_eq]
  rw [Matrix.single_kronecker_single, one_mul, QuantumRuntime.run₂_query_bind,
    DSubInstrument.branch_bind_unit, LinearMap.comp_apply, QuantumRuntime.queryStep_branch_apply,
    SubInstrument.branch_relabel, SubInstrument.branch_relabel, conj_basisMatrix_equiv_single]
  simp only [QuantumRuntime.queryEquivIn_apply, Equiv.prodPUnit_symm_apply]
  rw [DSubInstrument.branch_frame_single, parallelOracleRuntime_step_branch_single,
    Matrix.single_kronecker_single, one_mul,
    conj_basisMatrix_equiv_single, QuantumRuntime.run₂_act, SubInstrument.bind_pure]
  simp only [QuantumRuntime.queryEquivOut_apply]
  rw [DSubInstrument.branch_frame_single, DSubInstrument.branch_classical_basis]
  have hzero : (fun j : Fin ts.length ↦
      ((parallelOracleEquiv H ts.length) (fun j ↦ (ts[j], 0)) j).2) =
      (fun j : Fin ts.length ↦ H ts[j]) := by funext j; simp
  simp only [hzero]
  split_ifs <;> simp [Matrix.single_kronecker_single]

end Quantum

namespace OracleComp

open Quantum

variable {X Y α : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] [AddCommGroup Y]

/-- Run a classical randomized algorithm with genuinely parallel quantum basis calls.
Every round becomes one call whose width is the length of its list. -/
@[expose]
noncomputable def toQuantumBatch (oa : OracleComp (unifSpec + (X →ₒ Y).batch) α) :
    QComp (qromBatchSpec X Y) (QReg.of Unit) (QReg.of Unit) α :=
  oa.toQuantumAt classicalBatchImpl

@[simp]
theorem toQuantumBatch_pure (a : α) :
    (pure a : OracleComp (unifSpec + (X →ₒ Y).batch) α).toQuantumBatch =
      QuantumComp₂.pure a := rfl

@[simp]
theorem toQuantumBatch_query_bind (t : ℕ ⊕ List X)
    (k : (unifSpec + (X →ₒ Y).batch).Range t →
      OracleComp (unifSpec + (X →ₒ Y).batch) α) :
    (liftM ((unifSpec + (X →ₒ Y).batch).query t) >>= k).toQuantumBatch =
      (classicalBatchImpl t).bind fun y ↦ (k y).toQuantumBatch :=
  toQuantumAt_query_bind classicalBatchImpl t k

/-- Classical randomized round programs give lossless quantum programs. -/
theorem lossless_toQuantumBatch (oa : OracleComp (unifSpec + (X →ₒ Y).batch) α) :
    oa.toQuantumBatch.Lossless .instruments := by
  apply lossless_toQuantumAt
  intro t
  rcases t with n | ts
  · exact QComp.lossless_coinImpl (spec := qromBatchSpec X Y) (B := QReg.of Unit) n
  · exact lossless_classicalBatchQuery (Y := Y) ts

end OracleComp

namespace Quantum

variable {X Y α : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] [AddCommGroup Y]

/-- Running a classical round against a fixed function is the deterministic tuple of table
answers, as a subinstrument on the trivial program and runtime registers. -/
theorem run_classicalBatchQuery (H : X → Y) (ts : List X) :
    (parallelOracleRuntime H).run₂ .instruments (classicalBatchQuery ts) =
      SubInstrument.pure (fun j : Fin ts.length ↦ H ts[j]) := by
  classical
  apply DSubInstrument.ext
  funext ys
  apply LinearMap.ext
  intro ρ
  let : Subsingleton (parallelOracleRuntime H).D := inferInstanceAs (Subsingleton Unit)
  let e : (QReg.of Unit) × (parallelOracleRuntime H).D := ((), ())
  have hρ : ρ = ρ e e • Matrix.single e e 1 := by
    ext a b
    have ha : a = e := Subsingleton.elim _ _
    have hb : b = e := Subsingleton.elim _ _
    subst a b
    simp
  rw [hρ, map_smul, map_smul]
  change ρ e e • _ = ρ e e • _
  congr 1
  dsimp only [e]
  trans (if (fun j : Fin ts.length ↦ H ts[j]) = ys then
    Matrix.single ((), ((): (parallelOracleRuntime H).D)) ((), ()) 1 else 0)
  · exact run_classicalBatchQuery_branch H ts () ys
  split_ifs with h
  · have hy : ys = (fun j : Fin ts.length ↦ H ts[j]) := h.symm
    subst ys
    exact (LinearMap.congr_fun (SubInstrument.branch_pure_self _) _).symm
  · exact (LinearMap.congr_fun
      (SubInstrument.branch_pure_of_ne
        (A := (QReg.of Unit) × (parallelOracleRuntime H).D) (Ne.symm h))
      (Matrix.single e e 1)).symm

/-- The complete fixed-function run is the coin-only execution of the corresponding classical
fixed-table program. In particular, adaptive rounds retain all their classical continuations. -/
theorem run_toQuantumBatch (H : X → Y)
    (oa : OracleComp (unifSpec + (X →ₒ Y).batch) α) :
    (parallelOracleRuntime H).run₂ .instruments oa.toQuantumBatch =
      (parallelOracleRuntime H).run₂ .instruments
        ((simulateQ (unifFwdAnswerImpl (QueryImpl.ofFn H)).batch' oa).toQuantumAt
          (QComp.coinImpl (qromBatchSpec X Y) (QReg.of Unit))) := by
  induction oa using OracleComp.inductionOn with
  | pure a => simp
  | query_bind t k ih =>
    rcases t with n | ts
    · rw [toQuantumBatch_query_bind, simulateQ_bind, simulateQ_spec_query]
      change (parallelOracleRuntime H).run₂ .instruments
        ((QComp.coinImpl (qromBatchSpec X Y) (QReg.of Unit) n).bind
          fun y ↦ (k y).toQuantumBatch) =
        (parallelOracleRuntime H).run₂ .instruments
          ((liftM (unifSpec.query n) >>= fun y ↦
            simulateQ (unifFwdAnswerImpl (QueryImpl.ofFn H)).batch' (k y)).toQuantumAt
            (QComp.coinImpl (qromBatchSpec X Y) (QReg.of Unit)))
      rw [toQuantumAt_query_bind, QuantumRuntime.run₂_bind, QuantumRuntime.run₂_bind]
      congr 1
      funext y
      exact ih y
    · rw [toQuantumBatch_query_bind, simulateQ_bind, simulateQ_spec_query,
        QueryImpl.batch'_apply_inr, QueryImpl.batch_unifFwdAnswerImpl]
      change (parallelOracleRuntime H).run₂ .instruments
        ((classicalBatchQuery ts).bind fun y ↦ (k y).toQuantumBatch) =
        (parallelOracleRuntime H).run₂ .instruments
          ((pure (fun j : Fin ts.length ↦ H ts[j]) >>= fun y ↦
            simulateQ (unifFwdAnswerImpl (QueryImpl.ofFn H)).batch' (k y)).toQuantumAt
            (QComp.coinImpl (qromBatchSpec X Y) (QReg.of Unit)))
      rw [pure_bind, QuantumRuntime.run₂_bind, run_classicalBatchQuery, SubInstrument.pure_bind]
      exact ih _

/-- At each fixed function, the randomized classical parallel embedding has exactly the
classical fixed-table output measure. -/
theorem evalDist_parallelOracleRuntime_toQuantumBatch [MeasurableSpace α] (H : X → Y)
    (oa : OracleComp (unifSpec + (X →ₒ Y).batch) α) :
    (parallelOracleRuntime H).evalDist₂ .instruments oa.toQuantumBatch (SubState.basis ()) =
      𝒟[simulateQ (unifFwdAnswerImpl (QueryImpl.ofFn H)).batch' oa] := by
  rw [QuantumRuntime.evalDist₂, run_toQuantumBatch,
    outcomeMeasure_run₂_toQuantumAt_coinImpl]
  have htrace : ((SubState.basis ()).prod (parallelOracleRuntime H).init).matrix.trace.re = 1 := by
    rw [SubState.trace_re_prod, SubState.trace_basis]
    change (1 : ℂ).re * (SubState.basis ()).matrix.trace.re = 1
    rw [SubState.trace_basis]
    norm_num
  rw [htrace, ENNReal.ofReal_one, one_smul]

end Quantum

namespace Quantum

variable {X Y α : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  [AddCommGroup Y] [SampleableType (X → Y)]

/-- Averaging the parallel embedding samples one function and executes the classical algorithm
against that table, with its local uniform randomness intact. -/
theorem sampledEvalDist₂_toQuantumBatch [MeasurableSpace α]
    (oa : OracleComp (unifSpec + (X →ₒ Y).batch) α) :
    sampledEvalDist₂ parallelOracleRuntime .instruments oa.toQuantumBatch (SubState.basis ()) =
      𝒟[$ᵗ (X → Y) >>= fun H ↦
        simulateQ (unifFwdAnswerImpl (QueryImpl.ofFn H)).batch' oa] := by
  let : MeasurableSpace (X → Y) := ⊤
  rw [sampledEvalDist₂_eq_bind_uniformSample, evalDist_bind_of_discrete]
  congr 1
  funext H
  exact evalDist_parallelOracleRuntime_toQuantumBatch H oa

/-- The exact classical random-oracle law for randomized, adaptive parallel rounds. The cache is
shared by all slots and rounds; empty lists and duplicate inputs require no side conditions. -/
theorem sampledEvalDist₂_toQuantumBatch_eq_randomOracle [SampleableType Y] [MeasurableSpace α]
    (oa : OracleComp (unifSpec + (X →ₒ Y).batch) α) :
    sampledEvalDist₂ parallelOracleRuntime .instruments oa.toQuantumBatch (SubState.basis ()) =
      𝒟[(simulateQ (unifFwdImpl (X →ₒ Y) + (X →ₒ Y).randomOracle.batch) oa).run' ∅] := by
  rw [sampledEvalDist₂_toQuantumBatch,
    ← OracleSpec.simulateQ_romImpl_simulateQ_unbatch,
    OracleComp.evalDist_simulateQ_romImpl_run'_eq_completeTable]
  simp only [OracleComp.completeTable_empty, QueryImpl.simulateQ_simulateQ_unbatch]

/-- The sequentialization of the genuine parallel embedding has the same lazy classical
random-oracle output law. Sequentialization retains the increasing slot order of each round. -/
theorem qromEvalDistMap_sequentialize_toQuantumBatch_eq_randomOracle
    [SampleableType Y] [MeasurableSpace α]
    (oa : OracleComp (unifSpec + (X →ₒ Y).batch) α) :
    qromEvalDistMap .instruments (oa.toQuantumBatch.sequentialize .instruments)
      (SubState.basis ())
      (fun _ p ↦ (QuantumComp₂.leafEquiv (QReg.of Unit) α).symm p) =
      𝒟[(simulateQ (unifFwdImpl (X →ₒ Y) + (X →ₒ Y).randomOracle.batch) oa).run' ∅] := by
  exact (qromEvalDistMap_sequentialize (X := X) (Y := Y)
    .instruments oa.toQuantumBatch (SubState.basis ())
    (fun _ p ↦ (QuantumComp₂.leafEquiv (QReg.of Unit) α).symm p)).trans
      (sampledEvalDist₂_toQuantumBatch_eq_randomOracle oa)

/-- Sequentializing the parallel embedding agrees with classical list-order unbatching followed
by the lazy random oracle. This relates the quantum and classical sequentialization maps through
their observed laws. -/
theorem qromEvalDistMap_sequentialize_toQuantumBatch_eq_unbatch
    [SampleableType Y] [MeasurableSpace α]
    (oa : OracleComp (unifSpec + (X →ₒ Y).batch) α) :
    qromEvalDistMap .instruments (oa.toQuantumBatch.sequentialize .instruments)
      (SubState.basis ())
      (fun _ p ↦ (QuantumComp₂.leafEquiv (QReg.of Unit) α).symm p) =
      𝒟[(simulateQ (X →ₒ Y).romImpl (simulateQ (X →ₒ Y).unbatch oa)).run' ∅] := by
  conv_rhs => rw [OracleSpec.simulateQ_romImpl_simulateQ_unbatch]
  exact qromEvalDistMap_sequentialize_toQuantumBatch_eq_randomOracle oa

end Quantum

/-! ## Resource bounds -/

namespace Quantum.QComp

variable {spec : QuantumOracleSpec} {P : Type} {In : P → QReg}
  {A B C : QReg} {α β : Type}

@[simp]
private theorem isTotalQueryBound_act_bind_iff (p : SubInstrument A B β)
    (k : β → QComp spec B C α) (n : ℕ) :
    ((act p).bind k).IsTotalQueryBound n ↔ ∀ b, (k b).IsTotalQueryBound n := by
  rw [act_bind, QuantumComp₂.primBind]
  exact QuantumComp.isTotalQueryBound_primBind_iff _ _ _

@[simp]
private theorem isPointBound_act_bind_iff (p : SubInstrument A B β)
    (k : β → QComp (uBatchSpec P In) B C α) (n : ℕ) :
    ((act p).bind k).IsPointBound n ↔ ∀ b, (k b).IsPointBound n := by
  rw [act_bind, QuantumComp₂.primBind]
  exact QuantumComp.isPointBound_primBind_iff _ _ _

end Quantum.QComp

namespace Quantum.QuantumComp₂

variable {spec : QuantumOracleSpec} {P : Type} {In : P → QReg}
  {L : LocalSig} {A B : QReg} {α : Type}

@[simp]
private theorem isTotalQueryBound_query_bind_iff (p : spec.Port) (E : QReg)
    (e : A ≃ spec.In p × E)
    (k : spec.Result p → QuantumComp₂ L spec (QReg.of (spec.Out p × E)) B α) (n : ℕ) :
    ((query p E e).bind k).IsTotalQueryBound n ↔
      0 < n ∧ ∀ r, (k r).IsTotalQueryBound (n - 1) := by
  rw [query_bind, queryBind]
  exact QuantumComp.isTotalQueryBound_queryBind_iff _ _ _ _ _

@[simp]
private theorem isPointBound_query_bind_iff (ik : P × ℕ) (E : QReg)
    (e : A ≃ (uBatchSpec P In).In ik × E)
    (k : (uBatchSpec P In).Result ik →
      QuantumComp₂ L (uBatchSpec P In) (QReg.of ((uBatchSpec P In).Out ik × E)) B α) (n : ℕ) :
    ((query ik E e).bind k).IsPointBound n ↔
      ik.2 ≤ n ∧ ∀ r, (k r).IsPointBound (n - ik.2) := by
  rw [query_bind, queryBind]
  exact QuantumComp.isPointBound_queryBind_iff _ _ _ _ _

end Quantum.QuantumComp₂

namespace Quantum

variable {X Y α : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  [AddCommGroup Y]

/-- A classical round consumes one quantum round, including when its list is empty. -/
theorem isTotalQueryBound_classicalBatchQuery_bind_iff (ts : List X) (k : (Fin ts.length → Y) →
    QComp (qromBatchSpec X Y) (QReg.of Unit) (QReg.of Unit) α) (n : ℕ) :
    ((classicalBatchQuery ts).bind k).IsTotalQueryBound n ↔
      0 < n ∧ ∀ ys, (k ys).IsTotalQueryBound (n - 1) := by
  simp only [classicalBatchQuery, QuantumComp₂.bind_assoc, QComp.isTotalQueryBound_act_bind_iff]
  simpa using (QuantumComp₂.isTotalQueryBound_query_bind_iff (spec := qromBatchSpec X Y)
    (L := LocalSig.instruments) (A := QReg.of (Fin ts.length → X × Y))
    (B := QReg.of Unit) ((), ts.length) (QReg.of Unit)
    (Equiv.prodPUnit (Fin ts.length → X × Y)).symm
    (fun _ => (QComp.act (DSubInstrument.classical (B := fun _ ↦ Unit)
      (fun m : (Fin ts.length → X × Y) × Unit ↦ fun j ↦ (m.1 j).2) (fun _ ↦ ()))).bind k) n)

/-- A classical round consumes one quantum point per list position. -/
theorem isPointBound_classicalBatchQuery_bind_iff (ts : List X) (k : (Fin ts.length → Y) →
    QComp (qromBatchSpec X Y) (QReg.of Unit) (QReg.of Unit) α) (n : ℕ) :
    ((classicalBatchQuery ts).bind k).IsPointBound n ↔
      ts.length ≤ n ∧ ∀ ys, (k ys).IsPointBound (n - ts.length) := by
  simp only [classicalBatchQuery, QuantumComp₂.bind_assoc, QComp.isPointBound_act_bind_iff]
  simpa using (QuantumComp₂.isPointBound_query_bind_iff (P := Unit) (In := fun _ => QReg.of (X × Y))
    (L := LocalSig.instruments) (A := QReg.of (Fin ts.length → X × Y))
    (B := QReg.of Unit) ((), ts.length) (QReg.of Unit)
    (Equiv.prodPUnit (Fin ts.length → X × Y)).symm
    (fun _ => (QComp.act (DSubInstrument.classical (B := fun _ ↦ Unit)
      (fun m : (Fin ts.length → X × Y) × Unit ↦ fun j ↦ (m.1 j).2) (fun _ ↦ ()))).bind k) n)

end Quantum

namespace OracleComp

open Quantum

variable {X Y α : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  [AddCommGroup Y]

/-- The classical online round budget bounds the rounds of the quantum embedding. -/
theorem IsOnlineQueryBound.isTotalQueryBound_toQuantumBatch
    {oa : OracleComp (unifSpec + (X →ₒ Y).batch) α} {r q : ℕ}
    (h : IsOnlineQueryBound oa (r, q)) : oa.toQuantumBatch.IsTotalQueryBound r := by
  induction oa using OracleComp.inductionOn generalizing r q with
  | pure a => exact QuantumComp.isTotalQueryBound_pure _ _
  | query_bind t k ih =>
    rcases t with n | ts
    · rw [isOnlineQueryBound_query_bind_inl_iff] at h
      rw [toQuantumBatch_query_bind]
      change ((QComp.coinImpl _ _ n).bind _).IsTotalQueryBound r
      rw [QComp.coinImpl, QComp.isTotalQueryBound_act_bind_iff]
      exact fun y => ih y (h y)
    · rw [isOnlineQueryBound_query_bind_inr_iff] at h
      rw [toQuantumBatch_query_bind]
      change ((classicalBatchQuery ts).bind _).IsTotalQueryBound r
      exact (isTotalQueryBound_classicalBatchQuery_bind_iff ts
        (fun ys : Fin ts.length → Y => (k ys).toQuantumBatch) r).mpr
        ⟨h.1.1, fun ys => ih ys (h.2 ys)⟩

/-- The classical point budget bounds the points of the quantum embedding. -/
theorem IsPointQueryBound.isPointBound_toQuantumBatch
    {oa : OracleComp (unifSpec + (X →ₒ Y).batch) α} {q : ℕ}
    (h : IsPointQueryBound oa q) : oa.toQuantumBatch.IsPointBound q := by
  induction oa using OracleComp.inductionOn generalizing q with
  | pure a => exact QuantumComp.isPointBound_pure _ _
  | query_bind t k ih =>
    change pointCount t ≤ q ∧ ∀ u, IsPointQueryBound (k u) (q - pointCount t) at h
    rcases t with n | ts
    · simp only [pointCount_inl, Nat.zero_le, Nat.sub_zero, true_and] at h
      rw [toQuantumBatch_query_bind]
      change ((QComp.coinImpl _ _ n).bind _).IsPointBound q
      rw [QComp.coinImpl, QComp.isPointBound_act_bind_iff]
      exact fun y => ih y (h y)
    · simp only [pointCount_inr] at h
      rw [toQuantumBatch_query_bind]
      change ((classicalBatchQuery ts).bind _).IsPointBound q
      exact (isPointBound_classicalBatchQuery_bind_iff ts
        (fun ys : Fin ts.length → Y => (k ys).toQuantumBatch) q).mpr
        ⟨h.1, fun ys => ih ys (h.2 ys)⟩

/-- The classical online point budget also bounds the points of the quantum embedding. -/
theorem IsOnlineQueryBound.isPointBound_toQuantumBatch
    {oa : OracleComp (unifSpec + (X →ₒ Y).batch) α} {r q : ℕ}
    (h : IsOnlineQueryBound oa (r, q)) : oa.toQuantumBatch.IsPointBound q :=
  h.isPointQueryBound.isPointBound_toQuantumBatch

end OracleComp
