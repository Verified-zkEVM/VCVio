/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module
public import VCVio.Quantum.Oracle.ParallelPreimage
public import Mathlib.Data.ZMod.Basic

/-!
# Random-function preimage search regressions

A fixed target is not conditioned to have a preimage. Pure counting checks the independent
avoiding-reference coupling against a biased unrestricted reference. Quantum examples retain
lost mass, singleton ranges, empty domains, and adaptive round/point budgets.
-/

public section

open Quantum ProbabilityTheory Matrix MeasureTheory
open scoped ENNReal Kronecker ComplexOrder

namespace VCVioTest.QuantumParallelPreimage

/-! ## Independent target sets -/

/-- Avoiding bases and labels give six equiprobable samples, two of which hit the target. -/
example : Fintype.card ((Unit → {y : Fin 3 // y ≠ 0}) × (Unit → Fin 3)) = 6 ∧
    (Finset.univ.filter fun p : (Unit → {y : Fin 3 // y ≠ 0}) × (Unit → Fin 3) ↦
      targetPatch 0 p.1 p.2 () = 0).card = 2 := by decide

/-- An unrestricted uniform reference would instead hit in five of nine samples.
That biased construction cannot represent the uniform function's one-third target incidence. -/
example : Fintype.card (Fin 3 × Fin 3) = 9 ∧
    (Finset.univ.filter fun p : Fin 3 × Fin 3 ↦
      (if p.2 = 0 then 0 else p.1) = 0).card = 5 := by decide

/-- Singleton labels mark every input even though an avoiding table cannot be sampled. -/
example : (∑ labels : Unit → ZMod 1,
    Set.indicator {z | labels z = 0}
      (fun _ ↦ (Fintype.card (Unit → ZMod 1) : ℝ≥0∞)⁻¹) ()) = 1 := by
  simpa using sum_indicator_target_eq_ennreal (X := Unit) (0 : ZMod 1) ()

/-! ## Oracle-independent input mass -/

/-- A genuine rank-two mixed substate has half the normalized mass. -/
@[expose, reducible]
noncomputable def mixedInput : SubState Bool where
  matrix := Matrix.diagonal fun _ ↦ (1 / 4 : ℂ)
  posSemidef := Matrix.PosSemidef.diagonal (by intro b; norm_num [Complex.nonneg_iff])
  trace_re_le_one := by norm_num [Matrix.trace, Matrix.diag, Fintype.sum_bool]

private theorem mixedInput_trace : mixedInput.matrix.trace.re = 1 / 2 := by
  norm_num [mixedInput, Matrix.trace, Matrix.diag, Fintype.sum_bool]

/-- An oracle-independent program returning one input without any calls. -/
@[expose, reducible]
noncomputable def noQuery {X Y : Type} [Fintype X] [DecidableEq X]
    [Fintype Y] [DecidableEq Y] (A : QReg) (out : X) :
    QuantumComp LocalSig.instruments.{0} (qromBatchSpec X Y) (fun _ ↦ X) A :=
  QuantumComp.pure out

private theorem univ_guess_probability :
    (parallelOracleRuntime (0 : Unit → ZMod 3)).evalDistMap .instruments
      (noQuery (QReg.of Unit) ()) (SubState.basis ())
      (fun leaf ↦ leaf.2 ∈ (Set.univ : Set Unit)) {True} = 1 := by
  let R := parallelOracleRuntime (0 : Unit → ZMod 3)
  have hm : R.evalDistMap .instruments (noQuery (QReg.of Unit) ()) (SubState.basis ())
      (fun leaf ↦ leaf.2 ∈ (Set.univ : Set Unit)) {True} =
      R.evalDistMap .instruments (noQuery (QReg.of Unit) ()) (SubState.basis ())
        (fun _ ↦ ()) Set.univ := by
    rw [R.evalDistMap_apply .instruments _ _ _ (MeasurableSet.singleton True),
      R.evalDistMap_apply .instruments _ _ _ MeasurableSet.univ]
    simp
  rw [hm, R.evalDistMap_apply_univ .instruments _ _ (fun _ ↦ ()),
    lossless_run_parallelOracleRuntime .instruments
      (show (noQuery (Y := ZMod 3) (QReg.of Unit) ()).Lossless .instruments by simp [noQuery])
      0 ((SubState.basis ()).prod R.init).matrix]
  change ENNReal.ofReal ((SubState.basis ()).prod (SubState.basis ())).matrix.trace.re = 1
  rw [SubState.trace_re_prod, SubState.trace_basis]
  norm_num

/-- The generic finding estimate permits unnormalized weight two, whose success weight is two.
Silently normalizing the challenge family or inserting a probability cap would fail this check. -/
theorem finding_unnormalized_weight :
    (∑ _ω : Unit, ENNReal.ofReal (2 : ℝ) *
      (parallelOracleRuntime (0 : Unit → ZMod 3)).evalDistMap .instruments
        (noQuery (QReg.of Unit) ()) (SubState.basis ())
        (fun leaf ↦ leaf.2 ∈ (Set.univ : Set Unit)) {True}) = 2 ∧
    (∑ _ω : Unit, ENNReal.ofReal (2 : ℝ) *
      (parallelOracleRuntime (0 : Unit → ZMod 3)).evalDistMap .instruments
        (noQuery (QReg.of Unit) ()) (SubState.basis ())
        (fun leaf ↦ leaf.2 ∈ (Set.univ : Set Unit)) {True}) ≤ 2 := by
  constructor
  · rw [Fintype.sum_unique, univ_guess_probability]
    norm_num
  · have h := sum_mul_evalDistMap_mem_parallel_le_of_isPointBound
      (Ω := Unit) .instruments (0 : Unit → ZMod 3) (fun _ ↦ 0)
      (fun _ ↦ (2 : ℝ)) (fun _ ↦ by norm_num) (fun _ ↦ Set.univ)
      (fun _ _ _ ↦ rfl) 2 (by norm_num) (fun _ ↦ by simp)
      (x := noQuery (Y := ZMod 3) (QReg.of Unit) ())
      (show (noQuery (Y := ZMod 3) (QReg.of Unit) ()).IsTotalQueryBound 0 by simp [noQuery])
      (show (noQuery (Y := ZMod 3) (QReg.of Unit) ()).IsPointBound 0 by simp [noQuery])
      (SubState.basis ()) (fun leaf ↦ leaf.2)
    simpa using h

/-- An empty challenge family needs no fictitious inhabitant and has zero weighted success. -/
example : (∑ _ω : Empty, ENNReal.ofReal (0 : ℝ) *
    (parallelOracleRuntime (0 : Unit → ZMod 3)).evalDistMap .instruments
      (noQuery (QReg.of Unit) ()) (SubState.basis ())
      (fun leaf ↦ leaf.2 ∈ (Set.univ : Set Unit)) {True}) ≤ 0 := by
  have h := sum_mul_evalDistMap_mem_parallel_le_of_isPointBound
    (Ω := Empty) .instruments (0 : Unit → ZMod 3) (fun _ ↦ 0)
    (fun _ ↦ (0 : ℝ)) (fun _ ↦ le_rfl) (fun _ ↦ Set.univ)
    (fun _ _ _ ↦ rfl) 0 le_rfl (fun _ ↦ by simp)
    (x := noQuery (Y := ZMod 3) (QReg.of Unit) ())
    (show (noQuery (Y := ZMod 3) (QReg.of Unit) ()).IsTotalQueryBound 0 by simp [noQuery])
    (show (noQuery (Y := ZMod 3) (QReg.of Unit) ()).IsPointBound 0 by simp [noQuery])
    (SubState.basis ()) (fun leaf ↦ leaf.2)
  simpa only [ENNReal.ofReal_zero, zero_mul] using h

/-- Pure fixed-target guessing on a singleton input domain succeeds with probability one third.
Conditioning the target to be in the function's image would incorrectly give probability one. -/
theorem fixed_target_no_queries :
    preimageSearchAdvantage (2 : ZMod 3) .instruments
      (noQuery (QReg.of Unit) ()) (SubState.basis ()) (fun leaf ↦ leaf.2) = 1 / 3 := by
  rw [preimageSearchAdvantage_eq_of_isPointBound_zero_of_lossless
    (x := noQuery (Y := ZMod 3) (QReg.of Unit) ()) 2 .instruments
    (by simp [noQuery]) (by simp [noQuery])]
  norm_num [SubState.trace_basis]

/-- The same fixed-target game keeps the half-mass input unnormalized. -/
theorem fixed_target_half_mass :
    preimageSearchAdvantage (2 : ZMod 3) .instruments
      (noQuery (QReg.of Bool) ()) mixedInput (fun leaf ↦ leaf.2) = 1 / 6 := by
  rw [preimageSearchAdvantage_eq_of_isPointBound_zero_of_lossless
    (x := noQuery (Y := ZMod 3) (QReg.of Bool) ()) 2 .instruments
    (by simp [noQuery]) (by simp [noQuery])]
  change ENNReal.ofReal mixedInput.matrix.trace.re / Fintype.card (ZMod 3) = 1 / 6
  rw [mixedInput_trace]
  norm_num [ENNReal.ofReal_div_of_pos]
  apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
  norm_num

/-- A singleton answer group has every input marked, while lost mass remains failure. -/
theorem singleton_range_half_mass :
    preimageSearchAdvantage (0 : ZMod 1) .instruments
      (noQuery (QReg.of Bool) false) mixedInput (fun leaf ↦ leaf.2) = 1 / 2 := by
  rw [preimageSearchAdvantage_eq_of_isPointBound_zero_of_lossless
    (x := noQuery (Y := ZMod 1) (QReg.of Bool) false) 0 .instruments
    (by simp [noQuery]) (by simp [noQuery])]
  change ENNReal.ofReal mixedInput.matrix.trace.re / Fintype.card (ZMod 1) = 1 / 2
  rw [mixedInput_trace]
  norm_num [ENNReal.ofReal_div_of_pos]

/-- The actual singleton-range theorem takes its trivial cap without an avoiding table. -/
example : preimageSearchAdvantage (0 : ZMod 1) .instruments
    (noQuery (QReg.of Bool) false) mixedInput (fun leaf ↦ leaf.2) ≤ 1 := by
  have h := preimageSearchAdvantage_le_of_isPointBound
    (x := noQuery (Y := ZMod 1) (QReg.of Bool) false) 0 .instruments
    (show (noQuery (Y := ZMod 1) (QReg.of Bool) false).IsTotalQueryBound 0 by simp [noQuery])
    (show (noQuery (Y := ZMod 1) (QReg.of Bool) false).IsPointBound 0 by simp [noQuery])
    mixedInput (fun leaf ↦ leaf.2)
  simpa using h

/-- A width-zero oracle round spends one round and zero points. -/
@[expose, reducible]
noncomputable def zeroWidthCall :
    QuantumComp LocalSig.instruments (qromBatchSpec Unit (ZMod 3))
      (fun _ ↦ Unit) (QReg.of (Fin 0 → Unit × ZMod 3)) :=
  QuantumComp.queryBind ((), 0) (QReg.of Unit) (Equiv.prodPUnit _).symm fun _ ↦
    QuantumComp.pure ()

/-- An actual empty batch reveals no oracle point and leaves the one-third guessing term. -/
theorem zero_width_guess :
    zeroWidthCall.IsTotalQueryBound 1 ∧ zeroWidthCall.IsPointBound 0 ∧
      preimageSearchAdvantage 2 .instruments zeroWidthCall
        (SubState.basis (fun i ↦ Fin.elim0 i)) (fun leaf ↦ leaf.2) = 1 / 3 := by
  refine ⟨by simp [zeroWidthCall], by simp [zeroWidthCall], ?_⟩
  rw [preimageSearchAdvantage_eq_of_isPointBound_zero_of_lossless 2 .instruments
    (show zeroWidthCall.IsPointBound 0 by simp [zeroWidthCall])
    (show zeroWidthCall.Lossless .instruments by simp [zeroWidthCall])]
  norm_num [SubState.trace_basis]

/-- With an empty input domain, a local failure has no output leaf and no guessed address. -/
@[expose, reducible]
noncomputable def emptyDomainFail :
    QuantumComp LocalSig.instruments (qromBatchSpec Empty (ZMod 3))
      (fun _ ↦ Empty) (QReg.of Unit) :=
  QuantumComp.primBind ⟨Empty, fun _ ↦ QReg.of Unit, DSubInstrument.fail⟩ fun e ↦ e.elim

/-- Empty domains remain admitted by both the actual game and the resource-bounded theorem. -/
theorem empty_domain_failure :
    preimageSearchAdvantage 2 .instruments emptyDomainFail (SubState.basis ())
      (fun leaf ↦ leaf.2) = 0 ∧
    preimageSearchAdvantage 2 .instruments emptyDomainFail (SubState.basis ())
      (fun leaf ↦ leaf.2) ≤ 1 / 3 := by
  constructor
  · rw [preimageSearchAdvantage_eq_sum]
    simp [QuantumRuntime.evalDistMap]
  · have h := preimageSearchAdvantage_le_of_isPointBound 2 .instruments
      (show emptyDomainFail.IsTotalQueryBound 0 by simp [emptyDomainFail])
      (show emptyDomainFail.IsPointBound 0 by simp [emptyDomainFail])
      (SubState.basis ()) (fun leaf ↦ leaf.2)
    simpa using h.trans (min_le_right _ _)

/-! ## Adaptive point budgets -/

/-- Branches choose profiles `(0, 2)` and `(1, 1)` with a common two-point total.
The local instruments may measure, entangle, change registers or lose mass. -/
noncomputable def adaptivePoints
    (p : DSubInstrument Bool Bool
      (fun b ↦ (Fin (if b then 0 else 1) → Bool × ZMod 256) × Bool))
    (s : ∀ b : Bool,
      SubInstrument ((Fin (if b then 0 else 1) → Bool × ZMod 256) × Bool)
        ((Fin (if b then 2 else 1) → Bool × ZMod 256) × Bool) Unit) :
    QuantumComp LocalSig.instruments (qromBatchSpec Bool (ZMod 256))
      (fun _ ↦ Bool) (QReg.of Bool) :=
  QuantumComp.primBind
    ⟨Bool, fun b ↦ QReg.of ((Fin (if b then 0 else 1) → Bool × ZMod 256) × Bool), p⟩
    fun b ↦ QuantumComp.queryBind ((), if b then 0 else 1) (QReg.of Bool) (Equiv.refl _)
      fun _ ↦ QuantumComp.primBind
        ⟨Unit, fun _ ↦ QReg.of ((Fin (if b then 2 else 1) → Bool × ZMod 256) × Bool), s b⟩
        fun _ ↦ QuantumComp.queryBind ((), if b then 2 else 1) (QReg.of Bool) (Equiv.refl _)
          fun _ ↦ QuantumComp.pure b

/-- The adaptive branch sum is two, rather than the width cap times two rounds. -/
theorem adaptivePoints_budgets
    (p : DSubInstrument Bool Bool
      (fun b ↦ (Fin (if b then 0 else 1) → Bool × ZMod 256) × Bool))
    (s : ∀ b : Bool,
      SubInstrument ((Fin (if b then 0 else 1) → Bool × ZMod 256) × Bool)
        ((Fin (if b then 2 else 1) → Bool × ZMod 256) × Bool) Unit) (n : ℕ) :
    ((adaptivePoints p s).IsTotalQueryBound n ↔ 2 ≤ n) ∧
      ((adaptivePoints p s).IsPointBound n ↔ 2 ≤ n) := by
  constructor
  · simp [adaptivePoints, LocalSig.InstrumentOp.Outcome]
    omega
  · simp [adaptivePoints, LocalSig.InstrumentOp.Outcome, Bool.forall_bool]
    omega

/-- A fixed nonzero target has the unsaturated bound 25/256 for both adaptive profiles,
even on lossy executions from a mixed half-mass input. -/
theorem adaptivePoints_preimage_le
    (p : DSubInstrument Bool Bool
      (fun b ↦ (Fin (if b then 0 else 1) → Bool × ZMod 256) × Bool))
    (s : ∀ b : Bool,
      SubInstrument ((Fin (if b then 0 else 1) → Bool × ZMod 256) × Bool)
        ((Fin (if b then 2 else 1) → Bool × ZMod 256) × Bool) Unit) :
    preimageSearchAdvantage 17 .instruments (adaptivePoints p s) mixedInput
      (fun leaf ↦ leaf.2) ≤ 25 / 256 := by
  have h := preimageSearchAdvantage_le_of_isPointBound 17 .instruments
    ((adaptivePoints_budgets p s 2).1.mpr le_rfl)
    ((adaptivePoints_budgets p s 2).2.mpr le_rfl) mixedInput (fun leaf ↦ leaf.2)
  convert h.trans (min_le_right _ _) using 1
  have hsqrt : Real.sqrt (4 : ℝ) = 2 := by
    convert Real.sqrt_sq_eq_abs (2 : ℝ) using 1 <;> norm_num
  norm_num [hsqrt, show (2 : ℝ) * 2 = 4 by norm_num]

end VCVioTest.QuantumParallelPreimage
