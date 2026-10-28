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
elements. Its standard-model reduction specializes over the field with five elements.
-/

public section

open OracleComp OracleSpec
open scoped ENNReal

namespace DiscreteLogRelation

/-- The fixed two-coordinate relation adversary satisfies the reduction bound over `ZMod 5`. -/
theorem reduction_zmod_five :
    letI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
    let A : Adversary (ZMod 5) (ZMod 5) 2 := fun _ => pure ![1, -1]
    Pr{let b ← experiment (1 : ZMod 5) A}[b = true] ≤
      Pr{let b ← DiffieHellman.dlogExperiment (1 : ZMod 5) (reduction A)}[b = true] +
        (1 / 5 : ℝ≥0∞) := by
  let : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  dsimp only
  simpa [ZMod.card] using experiment_le (F := ZMod 5) (1 : ZMod 5)
    (by
      simp only [smul_eq_mul, mul_one]
      exact ⟨fun _ _ h => h, fun x => ⟨x, rfl⟩⟩)
    (fun _ => pure ![1, -1])

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
