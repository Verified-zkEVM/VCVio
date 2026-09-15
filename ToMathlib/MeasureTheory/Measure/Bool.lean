/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma, Quang Dao
-/

module
public import ToMathlib.MeasureTheory.Measure.Subprobability
public import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
import Mathlib.Tactic.Linarith

/-!
# Boolean observation distances

The distance of the `true` event and Boolean bias are expressed in real numbers.
The hidden-bit identity requires total branches explicitly; missing mass cannot be
silently identified with the `false` outcome.
-/

public section

open MeasureTheory

namespace MeasureTheory.Measure
/-- Absolute difference between the masses of the two Boolean outcomes. -/
@[expose]
noncomputable def boolBias (μ : Measure Bool) : ℝ :=
  |(μ {true}).toReal - (μ {false}).toReal|
/-- Absolute difference between two measures on the event `{true}`. -/
@[expose]
noncomputable def boolDist (μ ν : Measure Bool) : ℝ :=
  |(μ {true}).toReal - (ν {true}).toReal|
/-- The two singleton events partition the Boolean sample space. -/
@[simp]
lemma apply_true_add_apply_false (μ : Measure Bool) :
    μ {true} + μ {false} = μ Set.univ := by
  rw [← measure_union (by simp) (measurableSet_singleton false)]
  congr 1
  ext value
  cases value <;> simp
/-- Boolean bias is twice the distance of the `true` mass from one half when the measure is
total. -/
lemma boolBias_eq_two_mul_abs_sub_half (μ : Measure Bool)
    (htotal : μ {true} + μ {false} = 1) :
    μ.boolBias = 2 * |(μ {true}).toReal - 1 / 2| := by
  have htrue_le : μ {true} ≤ 1 := by
    rw [← htotal]
    exact le_add_right (le_refl _)
  have htrue_ne_top : μ {true} ≠ ⊤ := ne_of_lt (htrue_le.trans_lt ENNReal.one_lt_top)
  have hfalse : μ {false} = 1 - μ {true} := by
    rw [← htotal, ENNReal.add_sub_cancel_left htrue_ne_top]
  unfold boolBias
  rw [hfalse, ENNReal.toReal_sub_of_le htrue_le ENNReal.one_ne_top, ENNReal.toReal_one,
    show (μ {true}).toReal - (1 - (μ {true}).toReal) =
      2 * ((μ {true}).toReal - 1 / 2) by ring,
    abs_mul, abs_two]
/-- Boolean bias under a probability measure is twice the distance of the `true` mass from one
half. -/
lemma boolBias_eq_two_mul_abs_sub_half_of_isProbabilityMeasure
    (μ : Measure Bool) [IsProbabilityMeasure μ] :
    μ.boolBias = 2 * |(μ {true}).toReal - 1 / 2| := by
  apply boolBias_eq_two_mul_abs_sub_half μ
  rw [apply_true_add_apply_false, measure_univ]
/-- The Boolean event distance satisfies the triangle inequality. -/
lemma boolDist_triangle (μ ν ρ : Measure Bool) :
    μ.boolDist ρ ≤ μ.boolDist ν + ν.boolDist ρ := abs_sub_le _ _ _
/-- A measure has zero Boolean event distance from itself. -/
@[simp]
lemma boolDist_self (μ : Measure Bool) : μ.boolDist μ = 0 := by
  simp [boolDist]
/-- Boolean event distance is symmetric. -/
lemma boolDist_comm (μ ν : Measure Bool) : μ.boolDist ν = ν.boolDist μ := abs_sub_comm _ _
/-- The mass of the `true` event is bounded by that of another measure plus their Boolean
distance. -/
lemma apply_true_le_add_ofReal_boolDist (μ ν : Measure Bool)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    μ {true} ≤ ν {true} + ENNReal.ofReal (μ.boolDist ν) := by
  unfold boolDist
  set a : ℝ := (μ {true}).toReal
  set b : ℝ := (ν {true}).toReal
  rw [show μ {true} = ENNReal.ofReal a from
      (ENNReal.ofReal_toReal (measure_ne_top μ _)).symm,
    show ν {true} = ENNReal.ofReal b from
      (ENNReal.ofReal_toReal (measure_ne_top ν _)).symm,
    ← ENNReal.ofReal_add ENNReal.toReal_nonneg (abs_nonneg _)]
  exact ENNReal.ofReal_le_ofReal (by linarith [le_abs_self (a - b)])
/-- A fair hidden-bit guessing experiment has the event distance of its two total branches. -/
lemma boolBias_bind_coin (coin μ ν : Measure Bool)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hcT : coin {true} = 1 / 2) (hcF : coin {false} = 1 / 2)
    (hμ : μ {true} + μ {false} = 1) (hν : ν {true} + ν {false} = 1) :
    (coin.bind fun b => (if b then μ else ν).bind
      fun z => Measure.dirac (b == z)).boolBias = μ.boolDist ν := by
  have hgame : ∀ x : Bool, (coin.bind fun b => (if b then μ else ν).bind
        fun z => Measure.dirac (b == z)) {x} = (μ {x} + ν {!x}) / 2 := by
    intro x
    simp only [Measure.bind_apply (MeasurableSet.singleton x) Measurable.of_discrete.aemeasurable,
      lintegral_fintype, Fintype.sum_bool, hcT, hcF]
    cases x <;> simp [Measure.dirac_apply', div_eq_mul_inv, mul_add, mul_comm]
  have hm := congrArg ENNReal.toReal hμ
  have hn := congrArg ENNReal.toReal hν
  simp only [ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _),
    ENNReal.toReal_one] at hm hn
  unfold boolBias boolDist
  rw [hgame true, hgame false]
  simp only [Bool.not_true, Bool.not_false, ENNReal.toReal_div,
    ENNReal.toReal_ofNat, ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)]
  congr 1
  linarith
end MeasureTheory.Measure
