/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.CryptoFoundations.HardnessAssumptions.DiscreteLogRelation
public import Mathlib.Algebra.Field.ZMod

/-!
# Discrete-log relation regression tests

The fixed coefficient vector `![1, -1]` finds precisely collisions between two supplied
elements. The finder `alwaysWins` returns `![b₁, -b₀]` on a nonzero basis `b` and `![1, 0]` on
the zero basis, so it wins every relation experiment; over the field with five elements
`experiment_le` then makes the named reduction solve discrete logarithm with probability at
least `4/5`.
-/

public section

open OracleComp OracleSpec
open scoped ENNReal

namespace DiscreteLogRelation

/-- A two-coordinate finder that always wins: `![b₁, -b₀]` on a nonzero basis `b`, and `![1, 0]`
on the zero basis. -/
def alwaysWins : Adversary (ZMod 5) (ZMod 5) 2 :=
  fun b => pure (if b = 0 then ![1, 0] else ![b 1, -b 0])

/-- `alwaysWins` wins the relation experiment over `ZMod 5` with probability one. -/
theorem alwaysWins_experiment :
    Pr{let b ← experiment (1 : ZMod 5) alwaysWins}[b = true] = 1 := by
  have h : experiment (1 : ZMod 5) alwaysWins =
      (do let _ ← $ᵗ (Fin 2 → ZMod 5); pure true) := by
    simp only [experiment, alwaysWins, pure_bind]
    congr 1
    funext x
    congr 1
    revert x
    decide
  simp [h]

/-- The named reduction from `alwaysWins` solves discrete logarithm over `ZMod 5` with
probability at least `4/5`, by `experiment_le` and `alwaysWins_experiment`. -/
theorem alwaysWins_reduction :
    letI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
    (4 / 5 : ℝ≥0∞) ≤
      Pr{let b ← DiffieHellman.dlogExperiment (1 : ZMod 5) (reduction alwaysWins)}[b = true] := by
  let : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have h := experiment_le (1 : ZMod 5) one_ne_zero alwaysWins
  rw [alwaysWins_experiment, ZMod.card] at h
  have h45 : (4 / 5 : ℝ≥0∞) + 1 / 5 = 1 := by
    rw [ENNReal.div_add_div_same, show (4 : ℝ≥0∞) + 1 = 5 by norm_num]
    exact ENNReal.div_self (by norm_num) (by norm_num)
  exact (ENNReal.add_le_add_iff_right (by simp)).mp (h45.trans_le (by exact_mod_cast h))

/-- The vector `![1, -1]` wins exactly on equality of the two sampled scalars. -/
theorem pair_experiment_zmod_five :
    letI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
    experiment (F := ZMod 5) (1 : ZMod 5) (fun _ => pure ![1, -1]) =
      (do let x ← $ᵗ (Fin 2 → ZMod 5); pure (decide (x 0 = x 1))) := by
  let : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hn : (![1, -1] : Fin 2 → ZMod 5) ≠ 0 := by
    intro h
    have h0 := congrFun h 0
    norm_num at h0
  simp [experiment, hn, Fin.sum_univ_two, sub_eq_zero, ← sub_eq_add_neg]

end DiscreteLogRelation
