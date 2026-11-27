/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import VCVio.OracleComp.Constructions.SampleableType.GuessIndex
public import VCVio.OracleComp.Constructions.SampleableType.Measure

/-!
# Checks for guessing an index of a list uniformly

`prEvent_exists_mem_le_mul_prEvent_getD` at `q = 0`, where it forces the event to have
probability `0`, and at a fixed list of `q = 3` entries with one satisfying entry, where both
sides are `1`, so no factor below `q` would do.
-/

public section

open scoped ENNReal

namespace VCVioTest.GuessIndex

/-- At `q = 0` every list is empty and the bound forces probability `0`. -/
example (mx : ProbComp (List ℕ)) (hmx : ∀ l ∈ support mx, l.length ≤ 0) (S : ℕ → Prop) :
    Pr{let l ← mx}[∃ x ∈ l, S x] = 0 := by
  simpa using prEvent_exists_mem_le_mul_prEvent_getD mx hmx S 0

/-- The list `[0, 1, 2]` always has an entry equal to `1`. -/
example : Pr{let l ← (pure [0, 1, 2] : ProbComp (List ℕ))}[∃ x ∈ l, x = 1] = 1 := by
  simp

/-- A uniform index of `Fin 3` reads the entry `1` of `[0, 1, 2]` with probability `1 / 3`. -/
example : Pr{let l ← (pure [0, 1, 2] : ProbComp (List ℕ)); let i ← $ᵗ Fin (max 3 1)}[
    l.getD i 5 = 1] = 3⁻¹ := by
  simp only [pure_bind, SampleableType.prEvent_uniformSample, Fintype.card_fin]
  rw [show (Finset.univ.filter fun i : Fin (max 3 1) ↦ [0, 1, 2].getD i 5 = 1).card = 1 by
    decide]
  simp

/-- The bound is tight: at `[0, 1, 2]` with `q = 3` both sides are `1`, so the factor `q` cannot
be replaced by anything smaller. -/
example : Pr{let l ← (pure [0, 1, 2] : ProbComp (List ℕ))}[∃ x ∈ l, x = 1] ≤
    (3 : ℕ) * Pr{let l ← (pure [0, 1, 2] : ProbComp (List ℕ)); let i ← $ᵗ Fin (max 3 1)}[
      l.getD i 5 = 1] :=
  prEvent_exists_mem_le_mul_prEvent_getD _ (by simp) _ 5

example : ((3 : ℕ) : ℝ≥0∞) * 3⁻¹ = 1 :=
  ENNReal.mul_inv_cancel (by simp) (by simp)

end VCVioTest.GuessIndex
