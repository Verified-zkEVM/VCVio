/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module
public import VCVio.Schemes.PointerChainPuzzle.QuantumCoupling.RankBounds
public import VCVio.Quantum.Comp.Finisher

/-!
# Sharp zero-query pointer-chain recovery

An adversary can guess the key by returning the public commitment. The complete programmed
oracle contains both responses, but with no queries its recovery probability is exactly the
input mass divided by the state-space cardinality. No distinct-label conditioning is imposed.
-/

public section

open Quantum PointerChainPuzzle PointerChainPuzzle.LeanSeal MeasureTheory ProbabilityTheory
open scoped ENNReal ComplexOrder

namespace VCVioTest.PointerChainRankBounds

private theorem hb : 16 ≤ 32 := by decide
private theorem hB : hashInputBound 16 ≤ 86 := by decide

/-- Return a public field without querying the oracle or measuring the retained register. -/
@[expose, reducible]
noncomputable def guessCommitment (P : LeanSeal.Puzzle 16 1) :
    QuantumComp LocalSig.instruments (qromBatchSpec (ByteArray.Bounded 86) (Bytes 32))
      (fun _ ↦ Bytes 32) (QReg.of Unit) := QuantumComp.pure P.commitment

private theorem pure_recovery (H : ByteArray.Bounded 86 → Bytes 32)
    (ρ : SubState Unit) (word key : Bytes 32) :
    (parallelOracleRuntime H).evalDistMap .instruments
      (QuantumComp.pure (X := fun _ : QReg ↦ Bytes 32) (A := QReg.of Unit) word)
      ρ (fun leaf ↦ leaf.2 = key) {True} = ρ.mass * (if word = key then 1 else 0) := by
  let : MeasurableSpace (Σ _ : QReg, Bytes 32) := ⊤
  rw [QuantumRuntime.evalDistMap_eq_map_evalDist _ _ _ _ _ Measurable.of_discrete,
    QuantumRuntime.evalDist, QuantumRuntime.run_pure, DSubInstrument.outcomeMeasure_ret,
    Measure.map_smul _ Measurable.of_discrete.aemeasurable,
    Measure.map_dirac' Measurable.of_discrete]
  rw [Measure.smul_apply, SubState.trace_re_prod]
  change ENNReal.ofReal (ρ.matrix.trace.re * (SubState.basis ()).matrix.trace.re) *
    (Measure.dirac (word = key)) {True} = _
  rw [SubState.trace_basis]
  by_cases h : word = key <;> simp [h, SubState.mass]

/-- Guessing the public commitment achieves exactly the baseline, including lost input mass. -/
theorem average_guessCommitment (H : ByteArray.Bounded 86 → Bytes 32) (ρ : SubState Unit) :
    averageRankHybridSuccess (m := 0) .instruments (by decide : 16 ≤ 32)
      (by decide : hashInputBound 16 ≤ 86) 0 0 Fin.elim0
      H guessCommitment ρ 0 = ρ.mass / Fintype.card (Bytes 32) := by
  classical
  let : MeasurableSpace (Bytes 32) := ⊤
  have hp := uniform_pair_eq (R := Bytes 32) (PathValue.commit : PathValue 1 0)
    PathValue.key (by intro h; cases h)
  rw [uniformOn_univ_apply_setOf] at hp
  have he :
      (∑ W : PathValue 1 0 → Bytes 32,
        (Fintype.card (PathValue 1 0 → Bytes 32) : ℝ≥0∞)⁻¹ *
          (if W .commit = W .key then 1 else 0)) =
        (Fintype.card (Bytes 32) : ℝ≥0∞)⁻¹ := by
    simpa only [mul_ite, mul_one, mul_zero, Finset.sum_ite,
      Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul, div_eq_mul_inv] using hp
  unfold averageRankHybridSuccess
  have hw (W : PathValue 1 0 → Bytes 32) :
      rankHybridSuccess .instruments hb hB 0 0 Fin.elim0 H guessCommitment ρ 0 W =
        ρ.mass * (if W .commit = W .key then 1 else 0) := by
    rw [rankHybridSuccess_zero, pure_recovery]
    rfl
  change (∑ W : PathValue 1 0 → Bytes 32,
    (Fintype.card (PathValue 1 0 → Bytes 32) : ℝ≥0∞)⁻¹ *
      rankHybridSuccess .instruments hb hB 0 0 Fin.elim0 H guessCommitment ρ 0 W) = _
  trans ∑ W : PathValue 1 0 → Bytes 32,
    (Fintype.card (PathValue 1 0 → Bytes 32) : ℝ≥0∞)⁻¹ *
      (ρ.mass * (if W .commit = W .key then 1 else 0))
  · apply Finset.sum_congr rfl
    intro W _
    exact congrArg ((Fintype.card (PathValue 1 0 → Bytes 32) : ℝ≥0∞)⁻¹ * ·) (hw W)
  · rw [div_eq_mul_inv, ← he, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro W _
    ring

/-- The root bound keeps the exact zero-query baseline even with a positive width allowance. -/
example : rankRecoveryBound 16 1 0 0 17 = (Fintype.card (Bytes 32) : ℝ≥0∞)⁻¹ := by
  unfold rankRecoveryBound
  simp only [Nat.cast_zero, zero_mul, add_zero]
  rw [← ENNReal.rpow_two, rpow_inv_two_rpow_two]

/-- No successful input mass is created by the public-field strategy. -/
example (H : ByteArray.Bounded 86 → Bytes 32) (ρ : SubState Unit) (hρ : ρ.mass = 0) :
    averageRankHybridSuccess (m := 0) .instruments hb hB 0 0 Fin.elim0
      H guessCommitment ρ 0 = 0 := by
  rw [average_guessCommitment, hρ]
  simp

/-- A subnormalized fixture with half of the input mass. -/
noncomputable def halfInput : SubState Unit where
  matrix := Matrix.diagonal fun _ ↦ (1 / 2 : ℂ)
  posSemidef := Matrix.PosSemidef.diagonal (by intro u; norm_num [Complex.nonneg_iff])
  trace_re_le_one := by norm_num [Matrix.trace, Matrix.diag]

/-- Returning the commitment does not normalize the half-mass input. -/
example (H : ByteArray.Bounded 86 → Bytes 32) :
    averageRankHybridSuccess (m := 0) .instruments hb hB 0 0 Fin.elim0
      H guessCommitment halfInput 0 = (1 / 2 : ℝ≥0∞) / Fintype.card (Bytes 32) := by
  rw [average_guessCommitment]
  norm_num [halfInput, SubState.mass, Matrix.trace, Matrix.diag, ENNReal.ofReal_div_of_pos]

end VCVioTest.PointerChainRankBounds
