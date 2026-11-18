/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module
public import VCVio.Quantum.Oracle.MaskedChain.Bounds
public import Mathlib.Data.ZMod.Basic

/-!
# Masked-chain endpoint and coupling regressions

Repeated chain inputs retain their earliest programming value. On such collisions the real
oracle masks need not equal independently programmed masks, so their joint laws require a
collision error. The examples use additive groups with more than two elements and tuples
wider than their input domain.

The endpoint theorem specializes to explicit unsaturated bounds at zero and one round.
Zero initial adversary mass remains failure in the actual oracle-dependent challenge game.
-/

public section

open Quantum Quantum.MaskedChain MeasureTheory
open scoped ENNReal Kronecker
open scoped Matrix

namespace VCVioTest.QuantumMaskedChain

/-- Four input cells over a three-element domain, with three occurrences of zero. -/
def repeated : Fin 4 → ZMod 3 := ![0, 0, 1, 0]

/-- Conflicting programming values at the repeated input. -/
def answers : Fin 4 → ZMod 3 := ![1, 2, 2, 0]

/-- The first occurrence retains priority over two different later answers. -/
example : patch 4 repeated (fun _ ↦ 0) answers 0 = 1 := by decide

/-- Programming the repeated input leaves the distinct programmed cell intact. -/
example : patch 4 repeated (fun _ ↦ 0) answers 1 = 2 := by decide

/-- An unqueried input keeps its original value. -/
example : patch 4 repeated (fun _ ↦ 0) answers 2 = 0 := by decide

/-- Oracle-derived and independently programmed masks can disagree on colliding inputs.
The collision term in the joint comparison is necessary even over a small cyclic group. -/
example : oracleMasks (patch 2 (![0, 0] : Fin 2 → ZMod 3) (fun _ ↦ 0) ![1, 2])
      (![0, 0, 1] : Fin 3 → ZMod 3) 1 ≠
    maskEquiv (![0, 0, 1] : Fin 3 → ZMod 3) (![1, 2] : Fin 2 → ZMod 3) 1 := by
  decide

/-- Fresh programming values keep a repeated-input oracle cell uniform: eight of the sixteen
complete oracle/value samples program it to one. -/
example : (Finset.univ.filter fun p : (ZMod 2 → ZMod 2) × (Fin 2 → ZMod 2) ↦
    patch 2 (fun _ ↦ 0) p.1 p.2 0 = 1).card = 8 := by decide

/-! ## Endpoint theorem integration -/

universe u v
variable {L : LocalSig.{u, v}}

/-- At zero rounds, the explicit bound retains its guessing and collision terms. -/
example (I : L.Interp) (adv : OnlineAdversary L (ZMod 256) 0)
    (hb : adv.IsQueryBound 0 7) : recoveryAdvantage I adv ≤ 1 / 128 := by
  have h := recoveryAdvantage_le I adv hb
  refine h.trans ((min_le_right _ _).trans_eq ?_)
  norm_num [recoveryBound]
  apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
  norm_num [ENNReal.toReal_add, ENNReal.toReal_mul, ENNReal.toReal_div]

private theorem root_inv_256 : ((256 : ℝ≥0∞)⁻¹ ^ (2⁻¹ : ℝ)) = (16 : ℝ≥0∞)⁻¹ := by
  apply ENNReal.rpow_left_injective (show (2 : ℝ) ≠ 0 by norm_num)
  change (((256 : ℝ≥0∞)⁻¹) ^ (2⁻¹ : ℝ)) ^ (2 : ℝ) = ((16 : ℝ≥0∞)⁻¹) ^ (2 : ℝ)
  rw [Quantum.rpow_inv_two_rpow_two, ENNReal.rpow_two]
  apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
  norm_num

/-- One round against two masked links has a nontrivial 17/64 endpoint bound; all three
error terms contribute, so a missing hybrid or collision term changes this value. -/
example (I : L.Interp) (adv : OnlineAdversary L (ZMod 256) 1)
    (hb : adv.IsQueryBound 1 1) : recoveryAdvantage I adv ≤ 17 / 64 := by
  have h := recoveryAdvantage_le I adv hb
  refine h.trans ((min_le_right _ _).trans_eq ?_)
  norm_num [recoveryBound]
  rw [show (1 / 2 : ℝ) = 2⁻¹ by norm_num, root_inv_256]
  apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
  rw [ENNReal.toReal_add (by finiteness) (by finiteness),
    ENNReal.toReal_add (by finiteness) (by finiteness)]
  norm_num

/-- Zero adversary mass remains failure even when the public challenge depends on the oracle. -/
theorem recoveryAdvantage_zero {G : Type} [Fintype G] [DecidableEq G] [AddCommGroup G]
    {q : ℕ} (I : L.Interp) (adv : OnlineAdversary L G q)
    (hρ : adv.initialState.matrix = 0) : recoveryAdvantage I adv = 0 := by
  rw [recoveryAdvantage_eq_sum]
  simp only [QuantumRuntime.evalDistMap, QuantumRuntime.matrix_jointPost, hρ,
    Matrix.zero_kronecker, map_zero, Matrix.trace_zero, Complex.zero_re,
    ENNReal.ofReal_zero, zero_smul, Measure.sum_zero]
  simp

end VCVioTest.QuantumMaskedChain
