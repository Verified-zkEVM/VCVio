/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module
public import VCVio.Schemes.MaskedChainPuzzle
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

/-- Repeating a programmed input only at the endpoint does not spoil agreement with the
published masks; only repetitions among the programmed inputs require a collision allowance. -/
example :
    oracleMasks (patch 2 (![0, 1] : Fin 2 → ZMod 3) (fun _ ↦ 0) ![1, 2])
        (![0, 1, 0] : Fin 3 → ZMod 3) =
      maskEquiv (![0, 1, 0] : Fin 3 → ZMod 3) (![1, 2] : Fin 2 → ZMod 3) := by
  apply oracleMasks_patch_of_input_injective
  decide

/-- Fresh programming values keep a repeated-input oracle cell uniform: eight of the sixteen
complete oracle/value samples program it to one. -/
example : (Finset.univ.filter fun p : (ZMod 2 → ZMod 2) × (Fin 2 → ZMod 2) ↦
    patch 2 (fun _ ↦ 0) p.1 p.2 0 = 1).card = 8 := by decide

/-! ## Endpoint theorem integration -/

universe u v
variable {L : LocalSig.{u, v}}

/-- For the one-link puzzle, the explicit bound is the exact guessing probability. -/
example (I : L.Interp) (adv : OnlineAdversary L (ZMod 256) 0)
    (hb : adv.IsQueryBound 0 7) : recoveryAdvantage I adv ≤ 1 / 256 := by
  have h := recoveryAdvantage_le I adv hb
  refine h.trans ((min_le_right _ _).trans_eq ?_)
  norm_num [recoveryBound]

private theorem root_inv_256 : ((256 : ℝ≥0∞)⁻¹ ^ (2⁻¹ : ℝ)) = (16 : ℝ≥0∞)⁻¹ := by
  apply ENNReal.rpow_left_injective (show (2 : ℝ) ≠ 0 by norm_num)
  change (((256 : ℝ≥0∞)⁻¹) ^ (2⁻¹ : ℝ)) ^ (2 : ℝ) = ((16 : ℝ≥0∞)⁻¹) ^ (2 : ℝ)
  rw [Quantum.rpow_inv_two_rpow_two, ENNReal.rpow_two]
  apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
  norm_num

/-- One round against two masked links has a nontrivial 33/128 endpoint bound; all three
error terms contribute, so a missing hybrid or collision term changes this value. -/
theorem oneRound_recoveryAdvantage_le (I : L.Interp) (adv : OnlineAdversary L (ZMod 256) 1)
    (hb : adv.IsQueryBound 1 1) : recoveryAdvantage I adv ≤ 33 / 128 := by
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

/-! ## Named puzzle experiment -/

/-- The nonbinary solver uses subtraction to unmask two successive links under one oracle. -/
example [MeasurableSpace (Option (ZMod 3))] :
    (parallelOracleRuntime (fun x : ZMod 3 ↦ x + 1)).evalDist₂ .instruments
      ((MaskedChainPuzzle.scheme (G := ZMod 3) 1).solve (0, ![0, 1])) (SubState.basis ()) =
        Measure.dirac (some (1 : ZMod 3)) := by
  have hp : publicPuzzle (fun x : ZMod 3 ↦ x + 1) (![0, 2, 1] : Fin 3 → ZMod 3) =
      (0, ![0, 1]) := by decide
  have h := MaskedChainPuzzle.evalDist_scheme_solve_publicPuzzle
    (fun x : ZMod 3 ↦ x + 1) (![0, 2, 1] : Fin 3 → ZMod 3)
  rw [hp] at h
  exact h

/-- The honest quantum solver uses two rounds to recover a two-link chain with certainty.
The one-round root bound for the same sixteen-element vertex space is strictly below one. -/
example [MeasurableSpace (Option (ZMod 16))] (H : ZMod 16 → ZMod 16)
    (vertices : Fin 3 → ZMod 16) :
    (((MaskedChainPuzzle.scheme 1).solve (publicPuzzle H vertices)).IsTotalQueryBound 2) ∧
      (parallelOracleRuntime H).evalDist₂ .instruments
        ((MaskedChainPuzzle.scheme 1).solve (publicPuzzle H vertices)) (SubState.basis ()) =
          Measure.dirac (some (vertices (Fin.last 2))) :=
  ⟨(MaskedChainPuzzle.scheme_solve_queryBound _).1,
    MaskedChainPuzzle.evalDist_scheme_solve_publicPuzzle H vertices⟩

/-- The actual two-phase experiment inherits the unsaturated endpoint bound, even though its
honest generator uses more points than the online adversary's one-point allowance. -/
example (adv : OnlineAdversary LocalSig.instruments (ZMod 256) 1)
    (hb : adv.IsQueryBound 1 1) :
    (MaskedChainPuzzle.adversary adv).IsQueryBound ⟨0, 0, 1, 1, 1⟩ ∧
      Quantum.TimeLockPuzzle.qromDelayAdvantage (MaskedChainPuzzle.scheme 1)
        (MaskedChainPuzzle.adversary adv) ≤ 33 / 128 := by
  refine ⟨MaskedChainPuzzle.adversary_isQueryBound adv hb, ?_⟩
  rw [MaskedChainPuzzle.qromDelayAdvantage_eq_recoveryAdvantage]
  exact oneRound_recoveryAdvantage_le .instruments adv hb

/-- Zero initial adversary mass gives zero recovery probability in the named experiment. -/
example {G : Type} [Fintype G] [DecidableEq G] [AddCommGroup G] {q : ℕ}
    (adv : OnlineAdversary LocalSig.instruments G q) (hρ : adv.initialState.matrix = 0) :
    Quantum.TimeLockPuzzle.qromDelayAdvantage (MaskedChainPuzzle.scheme q)
      (MaskedChainPuzzle.adversary adv) = 0 := by
  rw [MaskedChainPuzzle.qromDelayAdvantage_eq_recoveryAdvantage]
  exact recoveryAdvantage_zero .instruments adv hρ

end VCVioTest.QuantumMaskedChain
