/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module
public import VCVio.Quantum.Comp.ChargeWeight

/-!
# Numbering oracle calls without changing quantum registers

`QuantumComp.numberQueries` tags each call with its position in the execution: a program
started at `t` uses tag `t + j` at its `j`-th call. Local operations preserve the counter,
and adaptive continuations retain their own call counts. The local signature and every
quantum register are unchanged.

A stationary runtime on the enlarged signature can dispatch on the tag, giving an oracle
schedule whose private register persists throughout the run. Constant schedules reproduce
the original run. Query weights at call `j` depend only on the earlier schedule entries;
weights supported on any other tag vanish. These laws apply to numbered translations,
not to arbitrary programs that can choose their own tags.

The counter is syntactic, rather than an additional quantum register. This construction
accounts for oracle-call positions and does not claim a bound on local computation time.
-/

public section

open IPFunctor Matrix MeasureTheory
open scoped ENNReal ComplexOrder

universe u v u₁ v₁ w

namespace Quantum
namespace QuantumOracleSpec

/-- Oracle ports tagged by a natural-number call position, with the same quantum registers
and classical results as the underlying port. -/
@[reducible, expose]
def numbered (spec : QuantumOracleSpec.{u₁, v₁}) : QuantumOracleSpec.{u₁, v₁} where
  Port := ℕ × spec.Port
  In p := spec.In p.2
  Out p := spec.Out p.2
  Result p := spec.Result p.2

end QuantumOracleSpec

namespace QuantumComp

variable {spec : QuantumOracleSpec.{u₁, v₁}} {L : LocalSig.{u, v}}
  {W : QReg → Type w} {A : QReg}

/-- Tag each oracle call by its position, starting at the supplied counter. Local operations
keep the counter, and every oracle call advances it by one. -/
@[expose]
noncomputable def numberQueries : {A : QReg} → QuantumComp L spec W A →
    ℕ → QuantumComp L spec.numbered W A :=
  fun {_} x ↦ IFreeM.fold (P := toIPFunctor L spec)
    (D := fun A ↦ ℕ → QuantumComp L spec.numbered W A)
    (fun _ a _ ↦ QuantumComp.pure a)
    (fun _ cmd next t ↦ match cmd with
      | .prim o => primBind o fun b ↦ next (ULift.up b) t
      | .query i E e => queryBind (t, i) E e fun r ↦ next (ULift.up r) (t + 1)) x

/-- Returning does not consume a call position. -/
@[simp]
theorem numberQueries_pure (a : W A) (t : ℕ) :
    (QuantumComp.pure a : QuantumComp L spec W A).numberQueries t = QuantumComp.pure a := rfl

/-- Local operations preserve the call counter in every continuation. -/
@[simp]
theorem numberQueries_primBind (o : L.Op A)
    (next : (b : L.Outcome o) → QuantumComp L spec W (L.next o b)) (t : ℕ) :
    (primBind o next).numberQueries t = primBind o (fun b ↦ (next b).numberQueries t) := rfl

/-- A call uses the current counter as its tag and advances it in every continuation. -/
@[simp]
theorem numberQueries_queryBind (i : spec.Port) (E : QReg) (e : A ≃ spec.In i × E)
    (next : spec.Result i → QuantumComp L spec W (QReg.of (spec.Out i × E))) (t : ℕ) :
    (queryBind i E e next).numberQueries t =
      queryBind (t, i) E e (fun r ↦ (next r).numberQueries (t + 1)) := rfl

/-- Numbering preserves any port-charge budget when the charge ignores the added tag. -/
theorem isQueryChargeBound_numberQueries_iff (x : QuantumComp L spec W A)
    (t : ℕ) (c : spec.Port → ℕ) (n : ℕ) :
    (x.numberQueries t).IsQueryChargeBound (fun p ↦ c p.2) n ↔
      x.IsQueryChargeBound c n := by
  induction x using QuantumComp.inductionOn generalizing t n with
  | pure _ a => simp only [numberQueries_pure, isQueryChargeBound_pure]
  | primBind _ o next ih =>
    rw [numberQueries_primBind, isQueryChargeBound_primBind_iff,
      isQueryChargeBound_primBind_iff]
    exact forall_congr' fun b ↦ ih b t n
  | queryBind _ i E e next ih =>
    rw [numberQueries_queryBind, isQueryChargeBound_queryBind_iff,
      isQueryChargeBound_queryBind_iff]
    exact and_congr_right' (forall_congr' fun r ↦ ih r (t + 1) (n - c i))

/-- Numbering preserves the total oracle-call budget exactly. -/
theorem isTotalQueryBound_numberQueries_iff (x : QuantumComp L spec W A) (t n : ℕ) :
    (x.numberQueries t).IsTotalQueryBound n ↔ x.IsTotalQueryBound n := by
  rw [← isQueryChargeBound_one_iff, ← isQueryChargeBound_one_iff]
  exact isQueryChargeBound_numberQueries_iff x t (fun _ ↦ 1) n

end QuantumComp

namespace QuantumRuntime

variable {spec : QuantumOracleSpec.{u₁, v₁}} {L : LocalSig.{u, v}}
  {W : QReg → Type w} {A : QReg}

/-- Dispatch tagged ports using the supplied schedule, keeping the runtime's private register
and initial state. The definition exposes these structural projections. -/
@[reducible, expose]
noncomputable def numbered (R : QuantumRuntime spec)
    (steps : ℕ → ∀ i, SubInstrument (spec.In i × R.D) (spec.Out i × R.D) (spec.Result i)) :
    QuantumRuntime spec.numbered where
  D := R.D
  init := R.init
  step p := steps p.1 p.2

variable (R : QuantumRuntime spec) (I : L.Interp)

/-- A constant schedule runs the numbered translation exactly as the original runtime,
including every leaf's final private register. -/
theorem run_numberQueries_const (x : QuantumComp L spec W A) (t : ℕ) :
    (R.numbered (fun _ ↦ R.step)).run I (x.numberQueries t) = R.run I x := by
  induction x using QuantumComp.inductionOn generalizing t with
  | pure _ a => rw [QuantumComp.numberQueries_pure, run_pure, run_pure]
  | primBind _ o next ih =>
    rw [QuantumComp.numberQueries_primBind, run_primBind, run_primBind]
    exact congrArg _ (funext fun b ↦ ih b t)
  | queryBind _ i E e next ih =>
    rw [QuantumComp.numberQueries_queryBind, run_queryBind, run_queryBind]
    have he : (R.numbered (fun _ ↦ R.step)).queryStep (t, i) E e =
        R.queryStep i E e := rfl
    rw [he]
    exact congrArg _ (funext fun r ↦ ih r (t + 1))

/-- Constant scheduling preserves every classical observation of the output leaf. -/
theorem evalDistMap_numberQueries_const {γ : Type*} [MeasurableSpace γ]
    (x : QuantumComp L spec W A) (t : ℕ) (ρ : SubState A) (f : (Σ B, W B) → γ) :
    (R.numbered (fun _ ↦ R.step)).evalDistMap I (x.numberQueries t) ρ f =
      R.evalDistMap I x ρ f := by
  simp only [evalDistMap, matrix_jointPost, run_numberQueries_const]

variable (steps steps' : ℕ → ∀ i,
  SubInstrument (spec.In i × R.D) (spec.Out i × R.D) (spec.Result i))

/-- Schedules agreeing throughout the available call interval run a bounded translated
program to the same complete instrument. -/
theorem run_numberQueries_eq_of_prefix {x : QuantumComp L spec W A} {n t : ℕ}
    (hx : x.IsTotalQueryBound n)
    (h : ∀ m, t ≤ m → m < t + n → steps m = steps' m) :
    (R.numbered steps).run I (x.numberQueries t) =
      (R.numbered steps').run I (x.numberQueries t) := by
  induction x using QuantumComp.inductionOn generalizing n t with
  | pure _ a => rw [QuantumComp.numberQueries_pure, run_pure, run_pure]
  | primBind _ o next ih =>
    rw [QuantumComp.isTotalQueryBound_primBind_iff] at hx
    rw [QuantumComp.numberQueries_primBind, run_primBind, run_primBind]
    exact congrArg _ (funext fun b ↦ ih b (hx b) h)
  | queryBind _ i E e next ih =>
    rw [QuantumComp.isTotalQueryBound_queryBind_iff] at hx
    rw [QuantumComp.numberQueries_queryBind, run_queryBind, run_queryBind]
    have ht : steps t = steps' t := h t le_rfl (by omega)
    have he : (R.numbered steps).queryStep (t, i) E e =
        (R.numbered steps').queryStep (t, i) E e := by
      unfold queryStep
      simp only [numbered]
      rw [ht]
    rw [he]
    congr 1
    funext r
    exact ih r (hx.2 r) (fun m hlow hupp ↦ h m (by omega) (by omega))

/-- The weight at call `j` depends only on the preceding `j` schedule entries, not on
that call's answering step or any later step. No positivity hypothesis is needed. -/
theorem queryWeight_numberQueries_eq_of_prefix
    (weight : ∀ i, Matrix (spec.numbered.In i × R.D)
      (spec.numbered.In i × R.D) ℂ → ℝ≥0∞)
    (x : QuantumComp L spec W A) (t j : ℕ)
    (h : ∀ m, t ≤ m → m < t + j → steps m = steps' m)
    (ρ : Matrix (A × R.D) (A × R.D) ℂ) :
    (R.numbered steps).queryWeight I weight (x.numberQueries t) ρ j =
      (R.numbered steps').queryWeight I weight (x.numberQueries t) ρ j := by
  induction x using QuantumComp.inductionOn generalizing t j with
  | pure _ a => rw [QuantumComp.numberQueries_pure, queryWeight_pure, queryWeight_pure]
  | primBind _ o next ih =>
    rw [QuantumComp.numberQueries_primBind, queryWeight_primBind, queryWeight_primBind]
    exact tsum_congr fun b ↦ ih b t j h _
  | queryBind _ i E e next ih =>
    rw [QuantumComp.numberQueries_queryBind]
    cases j with
    | zero => rw [queryWeight_queryBind_zero, queryWeight_queryBind_zero]
    | succ j =>
      rw [queryWeight_queryBind_succ, queryWeight_queryBind_succ]
      have ht : steps t = steps' t := h t le_rfl (by omega)
      have he : (R.numbered steps).queryStep (t, i) E e =
          (R.numbered steps').queryStep (t, i) E e := by
        unfold queryStep
        simp only [numbered]
        rw [ht]
      rw [he]
      exact tsum_congr fun r ↦ ih r (t + 1) j (fun m hlow hupp ↦
        h m (by omega) (by omega)) _

variable (Rnum : QuantumRuntime spec.numbered)

/-- A weight vanishing on the actual call tag contributes nothing at that call. This is a
syntactic property of translated programs, including zero-weight branches. -/
theorem queryWeight_numberQueries_eq_zero (I : L.Interp)
    (weight : ∀ i, Matrix (spec.numbered.In i × Rnum.D)
      (spec.numbered.In i × Rnum.D) ℂ → ℝ≥0∞)
    (x : QuantumComp L spec W A) (t j : ℕ)
    (h : ∀ i σ, i.1 = t + j → weight i σ = 0)
    (ρ : Matrix (A × Rnum.D) (A × Rnum.D) ℂ) :
    Rnum.queryWeight I weight (x.numberQueries t) ρ j = 0 := by
  induction x using QuantumComp.inductionOn generalizing t j with
  | pure _ a => rw [QuantumComp.numberQueries_pure, queryWeight_pure]
  | primBind _ o next ih =>
    rw [QuantumComp.numberQueries_primBind, queryWeight_primBind]
    exact ENNReal.tsum_eq_zero.mpr fun b ↦ ih b t j h _
  | queryBind _ i E e next ih =>
    rw [QuantumComp.numberQueries_queryBind]
    cases j with
    | zero =>
      rw [queryWeight_queryBind_zero]
      exact h (t, i) _ (by simp)
    | succ j =>
      rw [queryWeight_queryBind_succ]
      exact ENNReal.tsum_eq_zero.mpr fun r ↦
        ih r (t + 1) j (fun ik σ hik ↦ h ik σ (by omega)) _

section Width

variable {P : Type u₁} {In : P → QReg}

/-- A width cap on the source program bounds the weight of each numbered call. Only
ports that respect that source width cap need satisfy the one-step trace estimate. -/
theorem queryWeight_numberQueries_le_mul_of_isWidthBound
    (Rnum : QuantumRuntime (uBatchSpec P In).numbered) (I : L.Interp)
    {weight : ∀ i, Matrix (((uBatchSpec P In).numbered.In i) × Rnum.D)
      (((uBatchSpec P In).numbered.In i) × Rnum.D) ℂ → ℝ≥0∞}
    (C : ℝ≥0∞) (k : ℕ)
    (hw : ∀ i, i.2.2 ≤ k → ∀ σ, σ.PosSemidef →
      weight i σ ≤ C * ENNReal.ofReal σ.trace.re)
    {x : QuantumComp L (uBatchSpec P In) W A} (hx : x.IsWidthBound k)
    {ρ : Matrix (A × Rnum.D) (A × Rnum.D) ℂ} (hρ : ρ.PosSemidef) (t j : ℕ) :
    Rnum.queryWeight I weight (x.numberQueries t) ρ j ≤ C * ENNReal.ofReal ρ.trace.re := by
  induction x using QuantumComp.inductionOn generalizing t j with
  | pure _ a => simp
  | primBind _ o next ih =>
    rw [QuantumComp.isWidthBound_primBind_iff] at hx
    rw [QuantumComp.numberQueries_primBind, queryWeight_primBind]
    refine (ENNReal.tsum_le_tsum fun b ↦
      ih b (hx b) (((I o).frame Rnum.D).posSemidef_branch_apply b hρ) t j).trans ?_
    rw [ENNReal.tsum_mul_left]
    exact mul_le_mul le_rfl
      (((I o).frame Rnum.D).isCPTNIFamily.tsum_ofReal_trace_re_le hρ) bot_le bot_le
  | queryBind _ i E e next ih =>
    rw [QuantumComp.isWidthBound_queryBind_iff] at hx
    rw [QuantumComp.numberQueries_queryBind]
    cases j with
    | zero =>
      rw [queryWeight_queryBind_zero]
      simpa only [trace_callInput] using hw (t, i) hx.1 _ (posSemidef_callInput e hρ)
    | succ j =>
      rw [queryWeight_queryBind_succ]
      refine (ENNReal.tsum_le_tsum fun r ↦
        ih r (hx.2 r) ((Rnum.queryStep (t, i) E e).posSemidef_branch_apply r hρ)
          (t + 1) j).trans ?_
      rw [ENNReal.tsum_mul_left]
      exact mul_le_mul le_rfl
        ((Rnum.queryStep (t, i) E e).isCPTNIFamily.tsum_ofReal_trace_re_le hρ) bot_le bot_le

end Width

end QuantumRuntime
end Quantum
