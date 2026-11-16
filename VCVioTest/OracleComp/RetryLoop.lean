/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module
public import VCVio.OracleComp.Constructions.RetryLoop

/-!
# Tests for first-success retry loops

`ProbComp.measureTVDist_firstSome_le_geometric` at attempts that differ, with `ζ = 1/4` and
`q = 1/2`. Over four equally likely cases both attempts reject on two; on the others `a₂` returns
`some true` twice, while `a₁` returns `some true` once and `some false` once. At budget `2` the
loops are at least `3/8` apart, which is the bound `ζ · (1 + q)`. A bound of `ζ` without the
geometric factor would fail here.
-/

public section

open OracleComp ENNReal ProbComp SampleableType

namespace RetryLoopTest

/-- An attempt that rejects on `0` and `1`, returns `some true` on `2` and `some false` on `3`. -/
def f₁ : Fin 4 → Option Bool
  | 0 | 1 => none
  | 2 => some true
  | 3 => some false

/-- An attempt that rejects on `0` and `1` and otherwise returns `some true`. -/
def f₂ : Fin 4 → Option Bool
  | 0 | 1 => none
  | 2 | 3 => some true

/-- The first test attempt. -/
noncomputable def a₁ : ProbComp (Option Bool) := f₁ <$> ($ᵗ Fin 4)

/-- The second test attempt. -/
noncomputable def a₂ : ProbComp (Option Bool) := f₂ <$> ($ᵗ Fin 4)

/-- One step of a loop over a uniform draw from `Fin 4`, as a sum over the four cases. -/
private lemma prEvent_firstSome_succ (f : Fin 4 → Option Bool) (n : ℕ) (e : Option Bool) :
    Pr{let x ← firstSome (f <$> ($ᵗ Fin 4)) (n + 1)}[x = e] =
      4⁻¹ * ∑ u : Fin 4, (f u).elim (Pr{let x ← firstSome (f <$> ($ᵗ Fin 4)) n}[x = e])
        fun a => if some a = e then 1 else 0 := by
  rw [firstSome_succ, bind_map_left, prEvent_bind_eq_tsum_of_countable, tsum_fintype,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [SampleableType.prEvent_uniformSample_eq_singleton, Fintype.card_fin, Nat.cast_ofNat]
  congr 1
  cases f u with
  | none => rfl
  | some a => simp [eq_comm]

/-- With one attempt left, the first loop returns `some false` on one of the four cases. -/
private lemma prEvent_firstSome_a₁_one : Pr{let x ← firstSome a₁ 1}[x = some false] = 4⁻¹ := by
  rw [a₁, prEvent_firstSome_succ, Fin.sum_univ_four]
  simp [f₁, firstSome]

/-- Over two draws, the first loop returns `some false` with probability `3/8`. -/
theorem prEvent_firstSome_a₁ : Pr{let x ← firstSome a₁ 2}[x = some false] = 3 / 8 := by
  have h := prEvent_firstSome_a₁_one
  rw [a₁] at h
  rw [a₁, prEvent_firstSome_succ, Fin.sum_univ_four]
  simp only [f₁, h, Option.some.injEq, Option.elim_none, Option.elim_some, Bool.true_eq_false,
    reduceIte, add_zero]
  rw [← ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)]
  simp [ENNReal.toReal_add, ENNReal.toReal_mul]
  norm_num

/-- The second loop never returns `some false`. -/
theorem prEvent_firstSome_a₂ : Pr{let x ← firstSome a₂ 2}[x = some false] = 0 := by
  have h : Pr{let x ← firstSome a₂ 1}[x = some false] = 0 := by
    rw [a₂, prEvent_firstSome_succ, Fin.sum_univ_four]
    simp [f₂, firstSome]
  rw [a₂] at h ⊢
  rw [prEvent_firstSome_succ, Fin.sum_univ_four]
  simp [f₂, h]

/-- The attempts are at most `1/4` apart: they differ only on the input `3`. -/
theorem measureTVDist_a₁_a₂_le :
    letI : MeasurableSpace (Option Bool) := ⊤
    measureTVDist a₁ a₂ ≤ 1 / 4 := by
  let : MeasurableSpace (Option Bool) := ⊤
  let : MeasurableSpace (Fin 4) := ⊤
  have h := measureETVDist_bind_bind_le_of_bad ($ᵗ Fin 4)
    (fun u => (pure (f₁ u) : ProbComp (Option Bool))) (fun u => pure (f₂ u))
    Measurable.of_discrete Measurable.of_discrete (bad := {3}) MeasurableSet.of_discrete 0
    (Filter.Eventually.of_forall fun u hu => by
      have hfu : f₁ u = f₂ u := by
        fin_cases u
        · rfl
        · rfl
        · rfl
        · exact absurd rfl hu
      rw [hfu, measureETVDist_self])
  rw [zero_mul, add_zero, SampleableType.evalDist_uniformSample_singleton, Fintype.card_fin] at h
  have hbound := ENNReal.toReal_mono (by simp) h
  rw [measureTVDist_eq_toReal_measureETVDist, a₁, a₂, map_eq_bind_pure_comp,
    map_eq_bind_pure_comp]
  refine hbound.trans (le_of_eq ?_)
  simp

/-- The second attempt rejects with probability `1/2`. -/
theorem prEvent_a₂_none : Pr{let x ← a₂}[x = none].toReal ≤ 1 / 2 := by
  have hcard : (Finset.univ.filter fun u : Fin 4 => f₂ u = none).card = 2 := by decide
  rw [a₂, prEvent_map, SampleableType.prEvent_uniformSample, hcard, Fintype.card_fin]
  simp [ENNReal.toReal_div]
  norm_num

/-- **The geometric factor is needed.** The loops are at least `3/8` apart, which is the bound
`ζ · (1 + q)` at `ζ = 1/4`, `q = 1/2`, and above `ζ` alone. -/
theorem three_eighths_le_measureTVDist_firstSome :
    letI : MeasurableSpace (Option Bool) := ⊤
    (3 / 8 : ℝ) ≤ measureTVDist (firstSome a₁ 2) (firstSome a₂ 2) := by
  let : MeasurableSpace (Option Bool) := ⊤
  have h := abs_prEvent_toReal_sub_le_measureTVDist (firstSome a₁ 2) (firstSome a₂ 2)
    (· = some false) .of_discrete
  rw [prEvent_firstSome_a₁, prEvent_firstSome_a₂] at h
  refine le_trans (le_of_eq ?_) h
  simp only [ENNReal.toReal_div, ENNReal.toReal_ofNat, ENNReal.toReal_zero, sub_zero]
  exact (abs_of_pos (by norm_num)).symm

/-- The bound of `measureTVDist_firstSome_le_geometric` at these attempts is exactly `3/8`. -/
example : (1 / 4 : ℝ) * ∑ j ∈ Finset.range 2, (1 / 2 : ℝ) ^ j = 3 / 8 := by
  norm_num [Finset.sum_range_succ]

end RetryLoopTest
