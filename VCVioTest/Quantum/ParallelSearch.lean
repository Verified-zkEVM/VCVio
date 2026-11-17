/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module
public import VCVio.Quantum.Oracle.ParallelSearch
public import VCVio.Quantum.Oracle.ClassicalParallel

/-!
# Parallel reprogramming and marked-search regressions

Query unions count repeated addresses once, and zero-width calls have empty query unions.
Nonbinary oracle actions retain spectators. Marked search is checked against exact classical
guessing probabilities and an actual batch algorithm that reads the complete two-point domain.
-/

public section

open Quantum Matrix MeasureTheory OracleSpec OracleComp
open scoped ENNReal ComplexOrder Kronecker

namespace VCVioTest.QuantumParallelSearch

/-! ## Query unions -/

/-- Four repeated slots over a two-point domain still describe one union event. -/
example :
    parallelInputProjector (Y := ZMod 3) 4 {false}
      (fun _ ↦ (false, 0)) (fun _ ↦ (false, 0)) = 1 := by
  simp [parallelInputProjector]

/-- Repeated slots do not multiply the successful basis state's union mass. -/
example :
    (MatrixMap.conj (parallelInputProjector (Y := ZMod 3) 4 {false})
      (Matrix.single (fun _ ↦ (false, 0)) (fun _ ↦ (false, 0)) 1)).trace.re = 1 := by
  rw [re_trace_conj_parallelInputProjector]
  classical
  rw [Finset.sum_eq_single (fun _ : Fin 4 ↦ (false, (0 : ZMod 3)))]
  · simp
  · intro b _ hb
    simp [Ne.symm hb]
  · simp

/-- A tuple avoiding the marked address has zero union mass. -/
example :
    parallelInputProjector (Y := ZMod 3) 4 {true}
      (fun _ ↦ (false, 0)) (fun _ ↦ (false, 0)) = 0 := by
  simp [parallelInputProjector]

/-- Even the full disagreement set is invisible to a width-zero call. -/
example : parallelInputProjector (X := Bool) (Y := ZMod 3) 0 Set.univ = 0 := by
  ext a b
  simp [parallelInputProjector]

/-- An empty disagreement set projects out every positive-width tuple. -/
example (k : ℕ) : parallelInputProjector (X := Bool) (Y := ZMod 3) k ∅ = 0 := by
  ext a b
  simp [parallelInputProjector]

/-- The full domain selects every tuple of positive width. -/
example : parallelInputProjector (X := Bool) (Y := ZMod 3) 3 Set.univ = 1 := by
  ext a b
  simp [parallelInputProjector, Matrix.one_apply]

/-- The union projector retains off-diagonal coherence between a repeated-input tuple and
a tuple containing two distinct addresses; it erases coherence to a tuple with no hit. -/
example :
    let ρ : Matrix (Fin 3 → Bool × ZMod 3) (Fin 3 → Bool × ZMod 3) ℂ :=
      Matrix.of fun _ _ ↦ 1 / 216
    let σ := MatrixMap.conj (parallelInputProjector (Y := ZMod 3) 3 {true}) ρ
    σ (fun _ ↦ (true, 0)) (fun i ↦ (i == 0, 0)) = 1 / 216 ∧
      σ (fun _ ↦ (true, 0)) (fun _ ↦ (false, 0)) = 0 := by
  dsimp only
  rw [MatrixMap.conj_apply, parallelInputProjector_conjTranspose]
  simp [parallelInputProjector, Matrix.diagonal_mul, Matrix.mul_diagonal]

/-- Uniform singleton challenges use the same input matrix, including its spectator. -/
example (ρ : Matrix ((Fin 3 → Bool × ZMod 3) × Bool)
    ((Fin 3 → Bool × ZMod 3) × Bool) ℂ) (hρ : ρ.PosSemidef) :
    ∑ b : Bool, (1 / 2 : ℝ) * (MatrixMap.conj
      (parallelInputProjector (Y := ZMod 3) 3 {b} ⊗ₖ (1 : Matrix Bool Bool ℂ)) ρ).trace.re ≤
      (3 / 2 : ℝ) * ρ.trace.re := by
  have h := sum_mul_re_trace_conj_parallelInputProjector_frame_le
    (fun _ : Bool ↦ (1 / 2 : ℝ)) (by intro b; norm_num)
    (fun b ↦ ({b} : Set Bool)) (1 / 2)
    (by intro x; cases x <;> norm_num [Set.indicator, Fintype.sum_bool]) 3 hρ
  convert h using 1
  ring

/-! ## Nonbinary response registers and common finishers -/

/-- The modified address carries the nonbinary response two. -/
@[expose]
def nonbinary (b : Bool) : ZMod 5 := if b then 2 else 0

/-- Three repeated queries add two modulo five in every slot and retain the spectator. -/
example :
    MatrixMap.conj (parallelOracleUnitary nonbinary 3 ⊗ₖ (1 : Matrix Bool Bool ℂ))
      (Matrix.single (fun _ ↦ (true, 4), true) (fun _ ↦ (true, 4), true) 1) =
      Matrix.single (fun _ ↦ (true, 1), true) (fun _ ↦ (true, 1), true) 1 := by
  rw [parallelOracleUnitary, basisMatrix_kronecker_one, conj_basisMatrix_single]
  congr 1 <;> ext i <;> decide +revert

/-- Reprogramming retains an arbitrary spectator, common CP/TNI finisher, and PSD input. -/
example {C : Type} [Fintype C]
    (Φ : MatrixMap ((Fin 3 → Bool × ZMod 5) × Bool) C)
    (hΦ : Φ.IsCP) (hT : Φ.IsTNI)
    (ρ : Matrix ((Fin 3 → Bool × ZMod 5) × Bool) ((Fin 3 → Bool × ZMod 5) × Bool) ℂ)
    (hρ : ρ.PosSemidef) :
    ENNReal.ofReal (Φ (MatrixMap.conj
      (parallelOracleUnitary nonbinary 3 ⊗ₖ (1 : Matrix Bool Bool ℂ)) ρ)).trace.re ^
        (2⁻¹ : ℝ) ≤
      ENNReal.ofReal (Φ (MatrixMap.conj
        (parallelOracleUnitary (0 : Bool → ZMod 5) 3 ⊗ₖ (1 : Matrix Bool Bool ℂ)) ρ)).trace.re ^
          (2⁻¹ : ℝ) +
        (4 * ENNReal.ofReal (MatrixMap.conj
          (parallelInputProjector (Y := ZMod 5) 3 {true} ⊗ₖ (1 : Matrix Bool Bool ℂ))
            ρ).trace.re) ^ (2⁻¹ : ℝ) :=
  rpow_inv_two_parallel_reprogramming_le nonbinary 0 3 {true}
    (by intro b hb; cases b <;> simp_all [nonbinary]) Φ hΦ hT hρ

/-! ## Fixed classical guesses -/

private theorem event_of_pure_run {X : Type} [Fintype X] [DecidableEq X]
    {A : QReg}
    (R : QuantumRuntime (qromBatchSpec X (ZMod 2)))
    (x : QComp (qromBatchSpec X (ZMod 2)) A A X)
    (ρ : SubState A) (a y : X)
    (hx : R.run₂ .instruments x = SubInstrument.pure a) :
    R.evalDistMap .instruments x ρ
      (fun p ↦ (QuantumComp₂.leafEquiv A X).symm p = y) {True} =
      if a = y then ENNReal.ofReal (ρ.prod R.init).matrix.trace.re else 0 := by
  have he := congrArg (fun μ : Measure Prop ↦ μ {True})
    (R.evalDist₂_map_eq_evalDistMap .instruments (fun a ↦ a = y) x ρ)
  rw [← he, QuantumRuntime.evalDist₂, QuantumRuntime.run₂_map, hx]
  rw [SubInstrument.map_eq_bind_pure, SubInstrument.pure_bind, SubInstrument.pure,
    DSubInstrument.outcomeMeasure_ret]
  by_cases h : a = y <;> simp [h, Measure.smul_apply]

/-- Return a fixed classical guess without consulting the oracle. -/
@[expose]
noncomputable def noQuery {X : Type} [Fintype X] [DecidableEq X] (g : X) :
    QComp (qromBatchSpec X (ZMod 2)) (QReg.of Bool) (QReg.of Bool) X :=
  QuantumComp₂.pure g

/-- A rank-two mixture has trace one half, so success remains unconditional. -/
noncomputable def mixedInput : SubState Bool where
  matrix := Matrix.diagonal fun _ ↦ (1 / 4 : ℂ)
  posSemidef := Matrix.PosSemidef.diagonal (by intro b; norm_num [Complex.nonneg_iff])
  trace_re_le_one := by norm_num [Matrix.trace, Matrix.diag, Fintype.sum_bool]

private theorem advantage_of_constant_run {X : Type} [Fintype X] [DecidableEq X]
    {A : QReg} (x : QComp (qromBatchSpec X (ZMod 2)) A A X) (g : X) (ρ : SubState A)
    (hx : ∀ y, (parallelOracleRuntime (markedFunction y)).run₂ .instruments x =
      SubInstrument.pure g) :
    markedSearchAdvantage .instruments x ρ (QuantumComp₂.leafEquiv A X).symm =
      ENNReal.ofReal ρ.matrix.trace.re / Fintype.card X := by
  rw [markedSearchAdvantage_eq_sum .instruments x ρ (QuantumComp₂.leafEquiv A X).symm]
  have h (y : X) := event_of_pure_run (parallelOracleRuntime (markedFunction y))
    x ρ g y (hx y)
  have ht (y : X) : (ρ.prod (parallelOracleRuntime (markedFunction y)).init).matrix.trace.re =
      ρ.matrix.trace.re := by
    change (ρ.prod (SubState.basis ())).matrix.trace.re = _
    rw [SubState.trace_re_prod, SubState.trace_basis]
    simp
  simp only [h, ht]
  calc
    _ = (Fintype.card X : ℝ≥0∞)⁻¹ * ENNReal.ofReal ρ.matrix.trace.re := by simp
    _ = _ := ENNReal.div_eq_inv_mul.symm

/-- A fixed no-query guess succeeds with its input mass divided by the domain cardinality. -/
theorem advantage_noQuery {X : Type} [Fintype X] [DecidableEq X] (g : X)
    (ρ : SubState Bool) :
    markedSearchAdvantage .instruments (noQuery g) ρ
      (QuantumComp₂.leafEquiv (QReg.of Bool) X).symm =
      ENNReal.ofReal ρ.matrix.trace.re / Fintype.card X :=
  advantage_of_constant_run (noQuery g) g ρ (by intro y; simp [noQuery])

/-- No-query success on three points is exactly one third. -/
example : markedSearchAdvantage .instruments (noQuery (0 : Fin 3)) (SubState.basis false)
    (QuantumComp₂.leafEquiv (QReg.of Bool) (Fin 3)).symm = 1 / 3 := by
  rw [advantage_noQuery]
  simp

/-- Missing input mass is not renormalized: the half-mass mixture succeeds with one sixth. -/
example : markedSearchAdvantage .instruments (noQuery (0 : Fin 3)) mixedInput
    (QuantumComp₂.leafEquiv (QReg.of Bool) (Fin 3)).symm = 1 / 6 := by
  rw [advantage_noQuery]
  norm_num [mixedInput, Matrix.trace, Matrix.diag, Fintype.sum_bool,
    ENNReal.ofReal_div_of_pos, div_eq_mul_inv, ← ENNReal.mul_inv]

/-- There is no uncertainty on a singleton domain, even without querying. -/
example : markedSearchAdvantage .instruments (noQuery ()) (SubState.basis false)
    (QuantumComp₂.leafEquiv (QReg.of Bool) Unit).symm = 1 := by
  rw [advantage_noQuery]
  simp

/-- Query both Boolean addresses and infer which one was marked. -/
@[expose]
def findMark : OracleComp (unifSpec + (Bool →ₒ ZMod 2).batch) Bool := do
  let r ← liftM ((unifSpec + (Bool →ₒ ZMod 2).batch).query (.inr [false, true]))
  pure ((r 0 : ZMod 2) == 0)

/-- The real batch embedding identifies each fixed mark with certainty. -/
theorem run_findMark (y : Bool) :
    (parallelOracleRuntime (markedFunction y)).run₂ .instruments findMark.toQuantumBatch =
      SubInstrument.pure y := by
  rw [run_toQuantumBatch]
  have h : simulateQ (unifFwdAnswerImpl (QueryImpl.ofFn (markedFunction y))).batch' findMark =
      pure y := by
    cases y <;> rfl
  rw [h]
  simp

private theorem findMark_online : findMark.IsOnlineQueryBound (1, 2) := by
  rw [findMark, isOnlineQueryBound_query_bind_inr_iff]
  simp [IsOnlineQueryBound]

/-- Full-domain classical search uses one round holding two points. -/
theorem findMark_round : findMark.toQuantumBatch.IsTotalQueryBound 1 :=
  findMark_online.isTotalQueryBound_toQuantumBatch

/-- The width cap counts the actual two-slot call. -/
theorem findMark_width : findMark.toQuantumBatch.IsWidthBound 2 :=
  findMark_online.isPointQueryBound.isPointBound_toQuantumBatch.isWidthBound

/-- The actual two-slot marked-oracle algorithm succeeds with probability one. -/
example : markedSearchAdvantage .instruments findMark.toQuantumBatch (SubState.basis ())
    (QuantumComp₂.leafEquiv (QReg.of Unit) Bool).symm = 1 := by
  rw [markedSearchAdvantage_eq_sum .instruments findMark.toQuantumBatch
    (SubState.basis ()) (QuantumComp₂.leafEquiv (QReg.of Unit) Bool).symm]
  have h (y : Bool) := event_of_pure_run (parallelOracleRuntime (markedFunction y))
    findMark.toQuantumBatch (SubState.basis ()) y y (run_findMark y)
  have ht (y : Bool) : ((SubState.basis ()).prod
      (parallelOracleRuntime (markedFunction y)).init).matrix.trace.re = 1 := by
    change ((SubState.basis ()).prod (SubState.basis ())).matrix.trace.re = 1
    simp
  simp only [h, ht, ite_true, ENNReal.ofReal_one, Finset.sum_const, Finset.card_univ,
    Fintype.card_bool, nsmul_eq_mul, mul_one]
  norm_num [ENNReal.inv_mul_cancel]

/-- An empty oracle round is followed by a fixed guess. -/
@[expose]
def emptyGuess : OracleComp (unifSpec + (Bool →ₒ ZMod 2).batch) Bool := do
  let _ ← liftM ((unifSpec + (Bool →ₒ ZMod 2).batch).query (.inr []))
  pure false

/-- Width zero leaks no mark information: the fixed output law is independent of the mark. -/
theorem run_emptyGuess (y : Bool) :
    (parallelOracleRuntime (markedFunction y)).run₂ .instruments emptyGuess.toQuantumBatch =
      SubInstrument.pure false := by
  rw [run_toQuantumBatch]
  have h : simulateQ (unifFwdAnswerImpl (QueryImpl.ofFn (markedFunction y))).batch' emptyGuess =
      pure false := rfl
  rw [h]
  simp

/-- A zero-width call still costs one round. -/
theorem emptyGuess_round : emptyGuess.toQuantumBatch.IsTotalQueryBound 1 := by
  have h : emptyGuess.IsOnlineQueryBound (1, 0) := by simp [emptyGuess, IsOnlineQueryBound]
  exact h.isTotalQueryBound_toQuantumBatch

/-- The same call has width cap zero. -/
theorem emptyGuess_width : emptyGuess.toQuantumBatch.IsWidthBound 0 := by
  have h : emptyGuess.IsPointQueryBound 0 := by simp [emptyGuess, IsPointQueryBound]
  exact h.isPointBound_toQuantumBatch.isWidthBound

/-- One zero-width round retains the exact no-query success probability one half. -/
example : markedSearchAdvantage .instruments emptyGuess.toQuantumBatch (SubState.basis ())
    (QuantumComp₂.leafEquiv (QReg.of Unit) Bool).symm = 1 / 2 := by
  rw [advantage_of_constant_run emptyGuess.toQuantumBatch false (SubState.basis ()) run_emptyGuess]
  simp

/-- The general bound retains the guessing term when `q = 0`. -/
example : markedSearchAdvantage .instruments (noQuery (0 : Fin 3)) (SubState.basis false)
    (QuantumComp₂.leafEquiv (QReg.of Bool) (Fin 3)).symm ≤ 1 / 3 := by
  have h := markedSearchAdvantage_le .instruments
    (show (noQuery (0 : Fin 3)).IsTotalQueryBound 0 from
      QuantumComp.isTotalQueryBound_pure _ _)
    (show (noQuery (0 : Fin 3)).IsWidthBound 4 from QuantumComp.isWidthBound_pure _ _)
    (SubState.basis false) (QuantumComp₂.leafEquiv (QReg.of Bool) (Fin 3)).symm
  simpa using h.trans (min_le_right _ _)

/-- `k = 0` remains informative even though a real quantum round occurs. -/
example : markedSearchAdvantage .instruments emptyGuess.toQuantumBatch (SubState.basis ())
    (QuantumComp₂.leafEquiv (QReg.of Unit) Bool).symm ≤ 1 / 2 := by
  have h := markedSearchAdvantage_le .instruments emptyGuess_round emptyGuess_width
    (SubState.basis ()) (QuantumComp₂.leafEquiv (QReg.of Unit) Bool).symm
  simpa using h.trans (min_le_right _ _)

/-- A local instrument may lose mass and choose between width zero and width one. -/
noncomputable def adaptiveWidth
    (p : DSubInstrument Bool Bool
      (fun b ↦ (Fin (if b then 1 else 0) → Fin 16 × ZMod 2) × Bool)) :
    QuantumComp LocalSig.instruments (qromBatchSpec (Fin 16) (ZMod 2))
      (fun _ ↦ Fin 16) (QReg.of Bool) :=
  QuantumComp.primBind
    ⟨Bool, fun b ↦ QReg.of ((Fin (if b then 1 else 0) → Fin 16 × ZMod 2) × Bool), p⟩
    fun b ↦ QuantumComp.queryBind ((), if b then 1 else 0) (QReg.of Bool) (Equiv.refl _)
      fun _ ↦ QuantumComp.pure (if b then 1 else 0)

/-- Distinct adaptive width ports share one total-round budget. -/
example (p : DSubInstrument Bool Bool
    (fun b ↦ (Fin (if b then 1 else 0) → Fin 16 × ZMod 2) × Bool)) :
    (adaptiveWidth p).IsTotalQueryBound 1 ∧ (adaptiveWidth p).IsWidthBound 1 := by
  constructor <;> simp [adaptiveWidth, LocalSig.InstrumentOp.Outcome, Bool.forall_bool]

/-- An unsaturated bound of nine sixteenths applies to adaptive, potentially lossy execution
from a genuine rank-two subnormalized mixture. -/
example (p : DSubInstrument Bool Bool
    (fun b ↦ (Fin (if b then 1 else 0) → Fin 16 × ZMod 2) × Bool)) :
    markedSearchAdvantage .instruments (adaptiveWidth p) mixedInput (fun out ↦ out.2) ≤
      9 / 16 := by
  have h := markedSearchAdvantage_le .instruments
    (show (adaptiveWidth p).IsTotalQueryBound 1 by
      simp [adaptiveWidth, LocalSig.InstrumentOp.Outcome])
    (show (adaptiveWidth p).IsWidthBound 1 by
      simp [adaptiveWidth, LocalSig.InstrumentOp.Outcome, Bool.forall_bool])
    mixedInput (fun out ↦ out.2)
  convert h.trans (min_le_right _ _) using 1
  norm_num

end VCVioTest.QuantumParallelSearch
