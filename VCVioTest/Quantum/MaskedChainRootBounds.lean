/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module
public import VCVio.Quantum.Oracle.MaskedChain.RootBounds
public import VCVio.Quantum.Comp.Finisher
public import Mathlib.Data.ZMod.Basic

/-!
# Root-accumulated masked-chain regressions

Guessing the published first vertex has exact success equal to the input mass divided by the
vertex-space size. For the one-link puzzle (`q = 0`), the patched bound keeps this baseline
and the real-game coupling has no collision allowance for its sole programmed input. With sixteen
vertices and one round of width one, the capped root bound is five eighths, while the event-error
bound is capped at one.
-/

public section

open Quantum Quantum.MaskedChain MeasureTheory ProbabilityTheory
open scoped ENNReal ComplexOrder

namespace VCVioTest.MaskedChainRootBounds

/-- A public-puzzle strategy with no oracle calls, retaining arbitrary initial mass. -/
@[expose, reducible]
noncomputable def guessFirst (ρ : SubState Unit) (q : ℕ) :
    OnlineAdversary LocalSig.instruments (ZMod 16) q where
  initialReg := QReg.of Unit
  initialState := ρ
  run P := QuantumComp.pure P.1

private theorem pure_recovery (H : ZMod 16 → ZMod 16) (ρ : SubState Unit)
    (word key : ZMod 16) :
    (parallelOracleRuntime H).evalDistMap .instruments
      (QuantumComp.pure (X := fun _ : QReg ↦ ZMod 16) (A := QReg.of Unit) word)
      ρ (fun leaf ↦ leaf.2 = key) {True} = ρ.mass * (if word = key then 1 else 0) := by
  let : MeasurableSpace (Σ _ : QReg, ZMod 16) := ⊤
  rw [QuantumRuntime.evalDistMap_eq_map_evalDist _ _ _ _ _ Measurable.of_discrete,
    QuantumRuntime.evalDist, QuantumRuntime.run_pure, DSubInstrument.outcomeMeasure_ret,
    Measure.map_smul _ Measurable.of_discrete.aemeasurable,
    Measure.map_dirac' Measurable.of_discrete, smul_apply, SubState.trace_re_prod]
  change ENNReal.ofReal (ρ.matrix.trace.re * (SubState.basis ()).matrix.trace.re) *
    (Measure.dirac (word = key)) {True} = _
  rw [SubState.trace_basis]
  by_cases h : word = key <;> simp [h, SubState.mass]

/-- The actual oracle-dependent challenge leaves first-vertex guessing at its exact baseline. -/
theorem recovery_guessFirst (ρ : SubState Unit) (q : ℕ) :
    recoveryAdvantage .instruments (guessFirst ρ q) = ρ.mass / 16 := by
  classical
  let : MeasurableSpace (ZMod 16) := ⊤
  have hp := uniform_pair_eq (R := ZMod 16) (0 : Fin (q + 2)) (Fin.last (q + 1))
    (by intro h; have hv := congrArg Fin.val h; simp only [Fin.val_zero, Fin.val_last] at hv; omega)
  rw [uniformOn_univ_apply_setOf] at hp
  have he : (∑ vertices : Fin (q + 2) → ZMod 16,
      (Fintype.card (Fin (q + 2) → ZMod 16) : ℝ≥0∞)⁻¹ *
        (if vertices 0 = vertices (Fin.last (q + 1)) then 1 else 0)) =
      (Fintype.card (ZMod 16) : ℝ≥0∞)⁻¹ := by
    simpa only [mul_ite, mul_one, mul_zero, Finset.sum_ite, Finset.sum_const_zero,
      add_zero, Finset.sum_const, nsmul_eq_mul, div_eq_mul_inv] using hp
  have havg (H : ZMod 16 → ZMod 16) :
      (∑ vertices : Fin (q + 2) → ZMod 16,
        (Fintype.card (Fin (q + 2) → ZMod 16) : ℝ≥0∞)⁻¹ *
          (parallelOracleRuntime H).evalDistMap .instruments
            ((guessFirst ρ q).run (publicPuzzle H vertices)) ρ
            (fun leaf ↦ leaf.2 = vertices (Fin.last (q + 1))) {True}) =
        ρ.mass * (Fintype.card (ZMod 16) : ℝ≥0∞)⁻¹ := by
    trans ∑ vertices : Fin (q + 2) → ZMod 16,
      (Fintype.card (Fin (q + 2) → ZMod 16) : ℝ≥0∞)⁻¹ *
        (ρ.mass * (if vertices 0 = vertices (Fin.last (q + 1)) then 1 else 0))
    · apply Finset.sum_congr rfl
      intro vertices _
      exact congrArg ((Fintype.card (Fin (q + 2) → ZMod 16) : ℝ≥0∞)⁻¹ * ·)
        (pure_recovery H ρ _ _)
    · rw [← he, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro vertices _
      ring
  rw [recoveryAdvantage_eq_sum]
  trans ∑ _H : ZMod 16 → ZMod 16,
    (Fintype.card (ZMod 16 → ZMod 16) : ℝ≥0∞)⁻¹ *
      (ρ.mass * (Fintype.card (ZMod 16) : ℝ≥0∞)⁻¹)
  · apply Finset.sum_congr rfl
    intro H _
    exact congrArg ((Fintype.card (ZMod 16 → ZMod 16) : ℝ≥0∞)⁻¹ * ·) (havg H)
  · rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← mul_assoc,
      ENNReal.mul_inv_cancel (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
        (ENNReal.natCast_ne_top _), one_mul]
    norm_num [div_eq_mul_inv]

/-- Zero successful mass remains failure in the actual game. -/
example (ρ : SubState Unit) (hρ : ρ.mass = 0) (q : ℕ) :
    recoveryAdvantage .instruments (guessFirst ρ q) = 0 := by
  rw [recovery_guessFirst, hρ]
  simp

/-- A half-mass input for the actual public-puzzle strategy. -/
noncomputable def halfInput : SubState Unit where
  matrix := Matrix.diagonal fun _ ↦ (1 / 2 : ℂ)
  posSemidef := Matrix.PosSemidef.diagonal (by intro u; norm_num [Complex.nonneg_iff])
  trace_re_le_one := by norm_num [Matrix.trace, Matrix.diag]

/-- No run renormalizes the missing half of the input mass. -/
example (q : ℕ) : recoveryAdvantage .instruments (guessFirst halfInput q) = 1 / 32 := by
  have hm : halfInput.mass = 1 / 2 := by
    norm_num [halfInput, SubState.mass, Matrix.trace, Matrix.diag, ENNReal.ofReal_div_of_pos]
  rw [recovery_guessFirst, hm]
  apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
  norm_num

/-- For the one-link puzzle, the real and patched bounds equal the exact guessing baseline. -/
example : rootPatchedRecoveryBound (ZMod 16) 0 7 = 1 / 16 ∧
    rootRecoveryBound (ZMod 16) 0 7 = 1 / 16 := by
  simp only [rootRecoveryBound, rootPatchedRecoveryBound, Finset.range_zero,
    Finset.sum_empty, mul_zero, add_zero]
  rw [← ENNReal.rpow_two, rpow_inv_two_rpow_two]
  constructor
  · norm_num
  · apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
    rw [ENNReal.toReal_add (by finiteness) (by finiteness)]
    norm_num

private theorem root_inv_16 :
    ((16 : ℝ≥0∞)⁻¹) ^ (2⁻¹ : ℝ) = (4 : ℝ≥0∞)⁻¹ := by
  apply ENNReal.rpow_left_injective (show (2 : ℝ) ≠ 0 by norm_num)
  change (((16 : ℝ≥0∞)⁻¹) ^ (2⁻¹ : ℝ)) ^ (2 : ℝ) =
    ((4 : ℝ≥0∞)⁻¹) ^ (2 : ℝ)
  rw [rpow_inv_two_rpow_two, ENNReal.rpow_two]
  apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
  norm_num

/-- With sixteen vertices and one round of width one, the capped root-accumulated bound is
five eighths, while the event-error bound is capped at one. -/
example : min 1 (rootRecoveryBound (ZMod 16) 1 1) = 5 / 8 ∧
    min 1 (recoveryBound (ZMod 16) 1 1) = 1 := by
  have hn : rootRecoveryBound (ZMod 16) 1 1 = 5 / 8 := by
    norm_num [rootRecoveryBound, rootPatchedRecoveryBound]
    rw [show (1 / 2 : ℝ) = 2⁻¹ by norm_num, root_inv_16]
    apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
    rw [ENNReal.toReal_add (by finiteness) (by finiteness), ENNReal.toReal_pow,
      ENNReal.toReal_add (by finiteness) (by finiteness)]
    norm_num
  have ho : recoveryBound (ZMod 16) 1 1 = 9 / 8 := by
    norm_num [recoveryBound]
    rw [show (1 / 2 : ℝ) = 2⁻¹ by norm_num, root_inv_16]
    apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
    rw [ENNReal.toReal_add (by finiteness) (by finiteness),
      ENNReal.toReal_add (by finiteness) (by finiteness)]
    norm_num
  rw [hn, ho]
  constructor
  · apply min_eq_right
    apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
    norm_num
  · apply min_eq_left
    apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
    norm_num

end VCVioTest.MaskedChainRootBounds
