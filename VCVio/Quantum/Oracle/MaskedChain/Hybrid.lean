/-
Copyright (c) 2026 Quang Dao, Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Alexander Hicks
-/

module
public import VCVio.Quantum.Comp.NumberedHybrid
public import VCVio.Quantum.Oracle.ParallelHybrid
public import VCVio.Quantum.Oracle.MaskedChain.Coupling
public import VCVio.Quantum.Oracle.MaskedChain.Model

/-!
# Scheduled hybrids for masked-chain endpoint recovery

Numbered parallel calls permit successive oracle schedules while retaining the same private
memory. A change at one call is charged to that call's pre-query state and to the union of
slots hitting a disagreement set. Observations can include the challenger's hidden data.
-/

public section
open Matrix MeasureTheory
open scoped ENNReal Kronecker ComplexOrder
namespace Quantum
universe u v w
variable {X Y : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  [AddCommGroup Y]
/-- Parallel oracle calls dispatched by their syntactically assigned call positions.
The schedule has one persistent trivial private register. -/
@[reducible, expose]
noncomputable def parallelScheduledRuntime (H : ℕ → X → Y) :
    QuantumRuntime (qromBatchSpec X Y).numbered :=
  { D := QReg.of Unit
    init := SubState.basis ()
    step p := (parallelOracleQuery (H p.1) p.2.2).frame (QReg.of Unit) }

variable {L : LocalSig.{u, v}} {W : QReg → Type w} {A : QReg}
/-- A change at one schedule position is supported on the corresponding disagreement
inputs. The reference pre-query state is from the schedule `H`. -/
theorem rpow_inv_two_evalDistMap_parallelSchedule_le_support (I : L.Interp) (H H' : ℕ → X → Y)
    (x : QuantumComp L (qromBatchSpec X Y) W A) (h : ℕ)
    (hoff : ∀ j, j ≠ h → H j = H' j) (S : Set X)
    (hsupport : ∀ z ∉ S, H h z = H' h z)
    (ρ : SubState A) {γ : Type*} [MeasurableSpace γ]
    (f : (Σ B, W B) → γ) {s : Set γ} (hs : MeasurableSet s) :
    (parallelScheduledRuntime H').evalDistMap I (x.numberQueries 0) ρ f s ^ (2⁻¹ : ℝ) ≤
      (parallelScheduledRuntime H).evalDistMap I (x.numberQueries 0) ρ f s ^ (2⁻¹ : ℝ) +
        (4 * (parallelScheduledRuntime H).queryWeight I
          (fun p ↦ parallelInputWeight (D := QReg.of Unit) S p.2)
          (x.numberQueries 0) (ρ.matrix ⊗ₖ (SubState.basis ()).matrix) h) ^ (2⁻¹ : ℝ) := by
  have hb := QuantumRuntime.rpow_inv_two_evalDistMap_numberQueries_le_of_eq_off_tag
    (spec := qromBatchSpec X Y) (D := QReg.of Unit)
    (s₀ := fun p ↦ (parallelOracleQuery (H p.1) p.2.2).frame (QReg.of Unit))
    (s₁ := fun p ↦ (parallelOracleQuery (H' p.1) p.2.2).frame (QReg.of Unit))
    (U := fun p r ↦ parallelOracleKraus (D := QReg.of Unit) (H p.1) p.2 r)
    (V := fun p r ↦ parallelOracleKraus (D := QReg.of Unit) (H' p.1) p.2 r)
    I (SubState.basis ()) (fun p r ↦ by
      rw [DSubInstrument.branch_frame_apply, branch_parallelOracleQuery, MatrixMap.amplify_conj]
      rfl)
    (fun p r ↦ by
      rw [DSubInstrument.branch_frame_apply, branch_parallelOracleQuery, MatrixMap.amplify_conj]
      rfl) x 0 h
    (fun p r hp ↦ by simp only [hoff p.1 (by simpa using hp)]) ρ f hs
  refine hb.trans (add_le_add le_rfl (ENNReal.rpow_le_rpow ?_ (by norm_num)))
  rw [← QuantumRuntime.queryWeight_const_mul]
  apply QuantumRuntime.queryWeight_mono _ I _ _ (ρ.prod (SubState.basis ())).posSemidef h
  intro p σ hσ
  by_cases hp : p.1 = h
  · exact parallelDisagreementWeight_le (H p.1) (H' p.1) S (by simpa [hp] using hsupport) p.2 hσ
  · simp [QuantumRuntime.krausWeight, hoff p.1 hp]

/-- A change at one schedule position is supported on the corresponding disagreement
inputs. The reference pre-query state is from the schedule `H`. -/
theorem evalDistMap_parallelSchedule_le_support (I : L.Interp) (H H' : ℕ → X → Y)
    (x : QuantumComp L (qromBatchSpec X Y) W A) (h : ℕ)
    (hoff : ∀ j, j ≠ h → H j = H' j) (S : Set X)
    (hsupport : ∀ z ∉ S, H h z = H' h z)
    (ρ : SubState A) {γ : Type*} [MeasurableSpace γ]
    (f : (Σ B, W B) → γ) {s : Set γ} (hs : MeasurableSet s) :
    (parallelScheduledRuntime H').evalDistMap I (x.numberQueries 0) ρ f s ≤
      (parallelScheduledRuntime H).evalDistMap I (x.numberQueries 0) ρ f s +
        2 * (4 * (parallelScheduledRuntime H).queryWeight I
          (fun p ↦ parallelInputWeight (D := QReg.of Unit) S p.2)
          (x.numberQueries 0) (ρ.matrix ⊗ₖ (SubState.basis ()).matrix) h) ^ (2⁻¹ : ℝ) := by
  have hb := QuantumRuntime.evalDistMap_numberQueries_le_of_eq_off_tag
    (spec := qromBatchSpec X Y) (D := QReg.of Unit)
    (s₀ := fun p ↦ (parallelOracleQuery (H p.1) p.2.2).frame (QReg.of Unit))
    (s₁ := fun p ↦ (parallelOracleQuery (H' p.1) p.2.2).frame (QReg.of Unit))
    (U := fun p r ↦ parallelOracleKraus (D := QReg.of Unit) (H p.1) p.2 r)
    (V := fun p r ↦ parallelOracleKraus (D := QReg.of Unit) (H' p.1) p.2 r)
    I (SubState.basis ()) (fun p r ↦ by
      rw [DSubInstrument.branch_frame_apply, branch_parallelOracleQuery, MatrixMap.amplify_conj]
      rfl)
    (fun p r ↦ by
      rw [DSubInstrument.branch_frame_apply, branch_parallelOracleQuery, MatrixMap.amplify_conj]
      rfl) x 0 h
    (fun p r hp ↦ by simp only [hoff p.1 (by simpa using hp)]) ρ f hs
  refine hb.trans (add_le_add le_rfl
    (mul_le_mul le_rfl (ENNReal.rpow_le_rpow ?_ (by norm_num)) bot_le bot_le))
  rw [← QuantumRuntime.queryWeight_const_mul]
  apply QuantumRuntime.queryWeight_mono _ I _ _ (ρ.prod (SubState.basis ())).posSemidef h
  intro p σ hσ
  by_cases hp : p.1 = h
  · exact parallelDisagreementWeight_le (H p.1) (H' p.1) S (by simpa [hp] using hsupport) p.2 hσ
  · simp [QuantumRuntime.krausWeight, hoff p.1 hp]

/-- The pre-query weight at a scheduled call depends only on earlier oracle functions.
The weight itself may depend on externally fixed hidden challenge data. -/
theorem queryWeight_parallelScheduledRuntime_eq_of_prefix (I : L.Interp)
    (H H' : ℕ → X → Y)
    (weight : ∀ p, Matrix (((qromBatchSpec X Y).numbered.In p) × QReg.of Unit)
      (((qromBatchSpec X Y).numbered.In p) × QReg.of Unit) ℂ → ℝ≥0∞)
    (x : QuantumComp L (qromBatchSpec X Y) W A) (j : ℕ)
    (h : ∀ m < j, H m = H' m)
    (ρ : Matrix (A × QReg.of Unit) (A × QReg.of Unit) ℂ) :
    (parallelScheduledRuntime H).queryWeight I weight (x.numberQueries 0) ρ j =
      (parallelScheduledRuntime H').queryWeight I weight (x.numberQueries 0) ρ j := by
  let R : QuantumRuntime (qromBatchSpec X Y) :=
    { D := QReg.of Unit
      init := SubState.basis ()
      step p := (parallelOracleQuery (0 : X → Y) p.2).frame (QReg.of Unit) }
  exact QuantumRuntime.queryWeight_numberQueries_eq_of_prefix R I
    (fun m p ↦ (parallelOracleQuery (H m) p.2).frame (QReg.of Unit))
    (fun m p ↦ (parallelOracleQuery (H' m) p.2).frame (QReg.of Unit)) weight x 0 j
    (fun m _ hm ↦ by
      funext p
      simp only [h m (by simpa using hm)]) ρ

omit [AddCommGroup Y] in
/-- Averaging hidden disagreement sets before applying a width bound preserves the
single-call query budget. The reference execution is independent of the sampled set. -/
theorem sum_mul_queryWeight_parallelInputWeight_numberQueries_le {Ω : Type*} [Fintype Ω]
    (R : QuantumRuntime (qromBatchSpec X Y).numbered) (I : L.Interp)
    (w : Ω → ℝ) (hw : ∀ ω, 0 ≤ w ω) (S : Ω → Set X) (δ : ℝ) (hδ : 0 ≤ δ)
    (hS : ∀ z, ∑ ω, Set.indicator (S ω) (fun _ ↦ w ω) z ≤ δ)
    (k : ℕ) {x : QuantumComp L (qromBatchSpec X Y) W A} (hx : x.IsWidthBound k)
    (ρ : SubState (A × R.D)) (t j : ℕ) :
    ∑ ω, ENNReal.ofReal (w ω) * R.queryWeight I
      (fun p ↦ parallelInputWeight (D := R.D) (S ω) p.2)
      (x.numberQueries t) ρ.matrix j ≤ (k : ℝ≥0∞) * ENNReal.ofReal δ := by
  calc
    _ = R.queryWeight I (fun p σ ↦ ∑ ω, ENNReal.ofReal (w ω) *
        parallelInputWeight (D := R.D) (S ω) p.2 σ) (x.numberQueries t) ρ.matrix j := by
      simp only [← QuantumRuntime.queryWeight_const_mul]
      simpa only [tsum_fintype] using R.tsum_queryWeight I
        (fun ω p σ ↦ ENNReal.ofReal (w ω) *
          parallelInputWeight (D := R.D) (S ω) p.2 σ)
        (x.numberQueries t) ρ.matrix j
    _ ≤ ((k : ℝ≥0∞) * ENNReal.ofReal δ) * ENNReal.ofReal ρ.matrix.trace.re := by
      apply QuantumRuntime.queryWeight_numberQueries_le_mul_of_isWidthBound
        R I _ k _ hx ρ.posSemidef
      intro p hp σ hσ
      exact (sum_mul_parallelInputWeight_le w hw S δ hδ hS p.2 hσ).trans (by gcongr)
    _ ≤ _ := mul_le_of_le_one_right (by positivity)
      (ENNReal.ofReal_le_one.mpr ρ.trace_re_le_one)

namespace MaskedChain

variable {G : Type} [DecidableEq G] [AddCommGroup G]

/-- Oracle values obtained from public masks and the hidden successor vertices. -/
@[expose]
def maskValues {q : ℕ} (masks : Fin (q + 1) → G) (vertices : Fin (q + 2) → G) :
    Fin (q + 1) → G :=
  fun i ↦ masks i - vertices i.succ

/-- Program the first `m` input vertices, retaining the earliest value at a repeated input. -/
@[expose]
def prefixOracle {q : ℕ} (H : G → G) (vertices : Fin (q + 2) → G)
    (masks : Fin (q + 1) → G) (m : ℕ) : G → G :=
  patchPrefix H (fun i ↦ vertices i.castSucc) (maskValues masks vertices) m

/-- Program every chain input using the public-mask reparameterization. -/
@[expose]
def fullOracle {q : ℕ} (H : G → G) (vertices : Fin (q + 2) → G)
    (masks : Fin (q + 1) → G) : G → G :=
  patch (q + 1) (fun i ↦ vertices i.castSucc) H (maskValues masks vertices)

/-- Before the hybrid cutoff, round `j` sees only the first `j + 1` programmed cells.
At and after the cutoff, it sees the fully programmed oracle. -/
@[expose]
def hybridSchedule {q : ℕ} (H : G → G) (vertices : Fin (q + 2) → G)
    (masks : Fin (q + 1) → G) (cutoff round : ℕ) : G → G :=
  if round < cutoff then prefixOracle H vertices masks (round + 1)
  else fullOracle H vertices masks

/-- A prefix of `m` programmed cells depends only on vertices with index at most `m`. -/
theorem prefixOracle_congr {q : ℕ} (H : G → G) (masks : Fin (q + 1) → G)
    {vertices vertices' : Fin (q + 2) → G} (m : ℕ)
    (h : ∀ i, i.val ≤ m → vertices i = vertices' i) :
    prefixOracle H vertices masks m = prefixOracle H vertices' masks m := by
  unfold prefixOracle
  apply patchPrefix_congr H m
  · intro i hi
    exact h i.castSucc (by simpa using Nat.le_of_lt hi)
  · intro i hi
    simp only [maskValues]
    rw [h i.succ (by simpa using hi)]

/-- Adjacent chain hybrids differ only at the cutoff call. -/
theorem hybridSchedule_eq_off_cutoff {q : ℕ} (H : G → G)
    (vertices : Fin (q + 2) → G) (masks : Fin (q + 1) → G) (h j : ℕ) (hj : j ≠ h) :
    hybridSchedule H vertices masks (h + 1) j = hybridSchedule H vertices masks h j := by
  by_cases hjh : j < h
  · simp [hybridSchedule, hjh, show j < h + 1 by omega]
  · simp [hybridSchedule, hjh, show ¬ j < h + 1 by omega]

/-- The cutoff call can disagree only on the chain inputs after its known prefix. -/
theorem fullOracle_eq_prefixOracle_of_not_mem_tailInputs {q : ℕ} (H : G → G)
    (vertices : Fin (q + 2) → G) (masks : Fin (q + 1) → G) (m : ℕ)
    (z : G) (hz : z ∉ tailInputs (fun i : Fin (q + 1) ↦ vertices i.castSucc) m) :
    fullOracle H vertices masks z = prefixOracle H vertices masks m z :=
  patch_eq_patchPrefix_of_not_mem_tailInputs _ H _ _ m z hz

/-- Before call `h`, replacing vertices beyond index `h` leaves every earlier schedule
entry unchanged. This equality concerns the pre-query weight, regardless of the current
and later answers or the dependence of the weight on the full hidden challenge. -/
theorem queryWeight_hybridSchedule_eq_of_vertices_prefix [Fintype G] {q : ℕ}
    (I : L.Interp) (H : G → G) (masks : Fin (q + 1) → G)
    {vertices vertices' : Fin (q + 2) → G} (h : ℕ)
    (hvertices : ∀ i, i.val ≤ h → vertices i = vertices' i)
    (weight : ∀ p, Matrix (((qromBatchSpec G G).numbered.In p) × QReg.of Unit)
      (((qromBatchSpec G G).numbered.In p) × QReg.of Unit) ℂ → ℝ≥0∞)
    (x : QuantumComp L (qromBatchSpec G G) W A)
    (ρ : Matrix (A × QReg.of Unit) (A × QReg.of Unit) ℂ) :
    (parallelScheduledRuntime (hybridSchedule H vertices masks (h + 1))).queryWeight I weight
        (x.numberQueries 0) ρ h =
      (parallelScheduledRuntime (hybridSchedule H vertices' masks (h + 1))).queryWeight I weight
        (x.numberQueries 0) ρ h := by
  apply queryWeight_parallelScheduledRuntime_eq_of_prefix
  intro j hj
  simp only [hybridSchedule, show j < h + 1 by omega, ↓reduceIte]
  exact prefixOracle_congr H masks (j + 1) fun i hi ↦ hvertices i (by omega)

variable [Fintype G]

/-- Schedules agreeing before the round budget give the same complete run. -/
theorem run_parallelScheduledRuntime_eq_of_prefix (I : L.Interp)
    (H H' : ℕ → G → G) {x : QuantumComp L (qromBatchSpec G G) W A} {n : ℕ}
    (hx : x.IsTotalQueryBound n) (h : ∀ m < n, H m = H' m) :
    (parallelScheduledRuntime H).run I (x.numberQueries 0) =
      (parallelScheduledRuntime H').run I (x.numberQueries 0) := by
  let R : QuantumRuntime (qromBatchSpec G G) :=
    { D := QReg.of Unit
      init := SubState.basis ()
      step p := (parallelOracleQuery (0 : G → G) p.2).frame (QReg.of Unit) }
  exact QuantumRuntime.run_numberQueries_eq_of_prefix R I
    (fun m p ↦ (parallelOracleQuery (H m) p.2).frame (QReg.of Unit))
    (fun m p ↦ (parallelOracleQuery (H' m) p.2).frame (QReg.of Unit)) hx
    (fun m _ hm ↦ by
      funext p
      simp only [h m (by simpa using hm)])

/-- A constant schedule preserves the complete fixed-function oracle run. -/
theorem run_parallelScheduledRuntime_const (I : L.Interp) (H : G → G)
    (x : QuantumComp L (qromBatchSpec G G) W A) (t : ℕ) :
    (parallelScheduledRuntime (fun _ ↦ H)).run I (x.numberQueries t) =
      (parallelOracleRuntime H).run I x := by
  induction x using QuantumComp.inductionOn generalizing t with
  | pure _ a =>
    rw [QuantumComp.numberQueries_pure, QuantumRuntime.run_pure, QuantumRuntime.run_pure]
    rfl
  | primBind _ o next ih =>
    rw [QuantumComp.numberQueries_primBind, QuantumRuntime.run_primBind,
      QuantumRuntime.run_primBind]
    exact congrArg _ (funext fun b ↦ ih b t)
  | queryBind _ i E e next ih =>
    rw [QuantumComp.numberQueries_queryBind, QuantumRuntime.run_queryBind,
      QuantumRuntime.run_queryBind]
    have he : (parallelScheduledRuntime (fun _ ↦ H)).queryStep (t, i) E e =
        (parallelOracleRuntime H).queryStep i E e := by
      rcases i with ⟨⟨⟩, k⟩
      unfold QuantumRuntime.queryStep
      simp only [parallelScheduledRuntime, parallelOracleRuntime_step]
      rfl
    rw [he]
    exact congrArg _ (funext fun r ↦ ih r (t + 1))

/-- A constant schedule preserves every classical observation of the fixed-function run. -/
theorem evalDistMap_parallelScheduledRuntime_const (I : L.Interp) (H : G → G)
    (x : QuantumComp L (qromBatchSpec G G) W A) (t : ℕ) (ρ : SubState A)
    {γ : Type*} [MeasurableSpace γ] (f : (Σ B, W B) → γ) :
    (parallelScheduledRuntime (fun _ ↦ H)).evalDistMap I (x.numberQueries t) ρ f =
      (parallelOracleRuntime H).evalDistMap I x ρ f := by
  simp only [QuantumRuntime.evalDistMap, QuantumRuntime.matrix_jointPost,
    run_parallelScheduledRuntime_const]
  rfl

/-- The single-round square-root comparison for adjacent masked-chain hybrids.
The endpoint observer is common to both runs for each fixed full challenge. -/
theorem rpow_inv_two_evalDistMap_hybridSchedule_le {q : ℕ} (I : L.Interp)
    (H : G → G) (vertices : Fin (q + 2) → G) (masks : Fin (q + 1) → G)
    (x : QuantumComp L (qromBatchSpec G G) W A) (h : ℕ) (ρ : SubState A)
    {γ : Type*} [MeasurableSpace γ] (f : (Σ B, W B) → γ)
    {s : Set γ} (hs : MeasurableSet s) :
    (parallelScheduledRuntime (hybridSchedule H vertices masks h)).evalDistMap I
        (x.numberQueries 0) ρ f s ^ (2⁻¹ : ℝ) ≤
      (parallelScheduledRuntime (hybridSchedule H vertices masks (h + 1))).evalDistMap I
        (x.numberQueries 0) ρ f s ^ (2⁻¹ : ℝ) +
        (4 * (parallelScheduledRuntime (hybridSchedule H vertices masks (h + 1))).queryWeight I
          (fun p ↦ parallelInputWeight (D := QReg.of Unit)
            (tailInputs (fun i : Fin (q + 1) ↦ vertices i.castSucc) (h + 1)) p.2)
          (x.numberQueries 0) (ρ.matrix ⊗ₖ (SubState.basis ()).matrix) h) ^ (2⁻¹ : ℝ) := by
  apply rpow_inv_two_evalDistMap_parallelSchedule_le_support
  · exact hybridSchedule_eq_off_cutoff H vertices masks h
  · intro z hz
    simpa [hybridSchedule] using
      (fullOracle_eq_prefixOracle_of_not_mem_tailInputs H vertices masks (h + 1) z hz).symm
  · exact hs
/-- The single-round event comparison for adjacent masked-chain hybrids.
The endpoint observer is common to both runs for each fixed full challenge. -/
theorem evalDistMap_hybridSchedule_le {q : ℕ} (I : L.Interp)
    (H : G → G) (vertices : Fin (q + 2) → G) (masks : Fin (q + 1) → G)
    (x : QuantumComp L (qromBatchSpec G G) W A) (h : ℕ) (ρ : SubState A)
    {γ : Type*} [MeasurableSpace γ] (f : (Σ B, W B) → γ)
    {s : Set γ} (hs : MeasurableSet s) :
    (parallelScheduledRuntime (hybridSchedule H vertices masks h)).evalDistMap I
        (x.numberQueries 0) ρ f s ≤
      (parallelScheduledRuntime (hybridSchedule H vertices masks (h + 1))).evalDistMap I
        (x.numberQueries 0) ρ f s +
        2 * (4 * (parallelScheduledRuntime (hybridSchedule H vertices masks (h + 1))).queryWeight I
          (fun p ↦ parallelInputWeight (D := QReg.of Unit)
            (tailInputs (fun i : Fin (q + 1) ↦ vertices i.castSucc) (h + 1)) p.2)
          (x.numberQueries 0) (ρ.matrix ⊗ₖ (SubState.basis ()).matrix) h) ^ (2⁻¹ : ℝ) := by
  apply evalDistMap_parallelSchedule_le_support
  · exact hybridSchedule_eq_off_cutoff H vertices masks h
  · intro z hz
    simpa [hybridSchedule] using
      (fullOracle_eq_prefixOracle_of_not_mem_tailInputs H vertices masks (h + 1) z hz).symm
  · exact hs

/-- The final hybrid does not depend on the endpoint, even jointly with its final private state. -/
theorem run_hybridSchedule_last_update {q : ℕ} (I : L.Interp)
    (H : G → G) (masks : Fin (q + 1) → G) (vertices : Fin (q + 2) → G)
    (value : G) {x : QuantumComp L (qromBatchSpec G G) W A}
    (hx : x.IsTotalQueryBound q) :
    (parallelScheduledRuntime (hybridSchedule H vertices masks q)).run I (x.numberQueries 0) =
      (parallelScheduledRuntime (hybridSchedule H
        (Function.update vertices (Fin.last (q + 1)) value) masks q)).run I
          (x.numberQueries 0) := by
  apply run_parallelScheduledRuntime_eq_of_prefix I _ _ hx
  intro m hm
  simp only [hybridSchedule, hm, ↓reduceIte]
  apply prefixOracle_congr H masks (m + 1)
  intro i hi
  have hne : i ≠ Fin.last (q + 1) := by
    intro heq
    subst i
    simp only [Fin.val_last] at hi
    omega
  simp [Function.update_of_ne hne]

end MaskedChain

end Quantum
