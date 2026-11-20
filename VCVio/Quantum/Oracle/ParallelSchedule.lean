/-
Copyright (c) 2026 Quang Dao, Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Alexander Hicks
-/

module
public import VCVio.Quantum.Comp.NumberedHybrid
public import VCVio.Quantum.Oracle.ParallelHybrid

/-!
# Schedules of parallel oracle calls

A numbered parallel runtime selects its oracle function by call position. One-call hybrids
are controlled by the disagreement inputs in the reference pre-query state. Earlier schedule
entries determine that state; constant schedules reproduce the original fixed-function run.
The input and response types may differ, and the full private register persists throughout.
-/

public section

open Matrix MeasureTheory
open scoped ENNReal Kronecker ComplexOrder

namespace Quantum

universe u v w

variable {X Y : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  [AddCommGroup Y]
  {L : LocalSig.{u, v}} {W : QReg → Type w} {A : QReg}

/-- Parallel oracle calls dispatched by their syntactically assigned call positions.
The schedule has one persistent trivial private register. -/
@[reducible, expose]
noncomputable def parallelScheduledRuntime (H : ℕ → X → Y) :
    QuantumRuntime (qromBatchSpec X Y).numbered :=
  { D := QReg.of Unit
    init := SubState.basis ()
    step p := (parallelOracleQuery (H p.1) p.2.2).frame (QReg.of Unit) }

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

/-- Schedules agreeing before the round budget give the same complete run. -/
theorem run_parallelScheduledRuntime_eq_of_prefix (I : L.Interp)
    (H H' : ℕ → X → Y) {x : QuantumComp L (qromBatchSpec X Y) W A} {n : ℕ}
    (hx : x.IsTotalQueryBound n) (h : ∀ m < n, H m = H' m) :
    (parallelScheduledRuntime H).run I (x.numberQueries 0) =
      (parallelScheduledRuntime H').run I (x.numberQueries 0) := by
  let R : QuantumRuntime (qromBatchSpec X Y) :=
    { D := QReg.of Unit
      init := SubState.basis ()
      step p := (parallelOracleQuery (0 : X → Y) p.2).frame (QReg.of Unit) }
  exact QuantumRuntime.run_numberQueries_eq_of_prefix R I
    (fun m p ↦ (parallelOracleQuery (H m) p.2).frame (QReg.of Unit))
    (fun m p ↦ (parallelOracleQuery (H' m) p.2).frame (QReg.of Unit)) hx
    (fun m _ hm ↦ by
      funext p
      simp only [h m (by simpa using hm)])

/-- A constant schedule preserves the complete fixed-function oracle run. -/
theorem run_parallelScheduledRuntime_const (I : L.Interp) (H : X → Y)
    (x : QuantumComp L (qromBatchSpec X Y) W A) (t : ℕ) :
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
theorem evalDistMap_parallelScheduledRuntime_const (I : L.Interp) (H : X → Y)
    (x : QuantumComp L (qromBatchSpec X Y) W A) (t : ℕ) (ρ : SubState A)
    {γ : Type*} [MeasurableSpace γ] (f : (Σ B, W B) → γ) :
    (parallelScheduledRuntime (fun _ ↦ H)).evalDistMap I (x.numberQueries t) ρ f =
      (parallelOracleRuntime H).evalDistMap I x ρ f := by
  simp only [QuantumRuntime.evalDistMap, QuantumRuntime.matrix_jointPost,
    run_parallelScheduledRuntime_const]
  rfl

end Quantum
