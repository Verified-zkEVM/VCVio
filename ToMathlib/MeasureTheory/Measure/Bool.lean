/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma, Quang Dao
-/

module
public import ToMathlib.MeasureTheory.Measure.Subprobability
public import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
public import Mathlib.MeasureTheory.Measure.Prod
public import ToMathlib.Data.ENNReal.AbsDiff
import Mathlib.Tactic.Linarith

/-!
# Boolean observation distances

The Boolean bias of a measure is the distance between the masses of its two outcomes, and the
Boolean distance of two measures is the distance between their masses on `true`. Both are
`ENNReal.absDiff`, the `edist` of `ℝ≥0∞`. The hidden-bit identity requires total branches
explicitly; missing mass cannot be silently identified with the `false` outcome.
-/

public section

open MeasureTheory ENNReal

namespace MeasureTheory.Measure

/-- Distance between the masses of the two Boolean outcomes. -/
@[expose]
noncomputable def boolBias (μ : Measure Bool) : ℝ≥0∞ :=
  ENNReal.absDiff (μ {true}) (μ {false})

/-- Distance between the masses two measures give the event `{true}`. -/
@[expose]
noncomputable def boolDist (μ ν : Measure Bool) : ℝ≥0∞ :=
  ENNReal.absDiff (μ {true}) (ν {true})

/-- The two singleton events partition the Boolean sample space. -/
@[simp]
lemma apply_true_add_apply_false (μ : Measure Bool) :
    μ {true} + μ {false} = μ Set.univ := by
  rw [← measure_union (by simp) (measurableSet_singleton false)]
  congr 1
  ext value
  cases value <;> simp

/-- The two Boolean outcome masses sum to one under a probability measure. -/
@[simp↓, grind norm↓]
lemma apply_true_add_apply_false_eq_one (μ : Measure Bool) [IsProbabilityMeasure μ] :
    μ {true} + μ {false} = 1 := by
  rw [apply_true_add_apply_false, measure_univ]

/-- A Boolean selector partitions each event of the first marginal into its two branches. -/
lemma fst_apply_eq_add {α : Type*} [MeasurableSpace α] (μ : Measure (α × Bool))
    {s : Set α} (hs : MeasurableSet s) :
    μ.fst s = μ (s ×ˢ {true}) + μ (s ×ˢ {false}) := by
  rw [Measure.fst_apply hs, ← measure_union
    (Set.disjoint_prod.mpr (Or.inr (by simp))) (hs.prod (measurableSet_singleton false))]
  congr 1
  ext ⟨a, b⟩
  cases b <;> simp

/-- The Boolean bias of a finite measure is finite. -/
lemma boolBias_ne_top (μ : Measure Bool) [IsFiniteMeasure μ] : μ.boolBias ≠ ⊤ :=
  ne_top_of_le_ne_top (add_ne_top.mpr ⟨measure_ne_top μ _, measure_ne_top μ _⟩)
    (absDiff_le_add _ _)

/-- The Boolean distance of two finite measures is finite. -/
lemma boolDist_ne_top (μ ν : Measure Bool) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    μ.boolDist ν ≠ ⊤ :=
  ne_top_of_le_ne_top (add_ne_top.mpr ⟨measure_ne_top μ _, measure_ne_top ν _⟩)
    (absDiff_le_add _ _)

/-- The real Boolean bias of a finite measure is the absolute difference of its outcome masses. -/
lemma toReal_boolBias (μ : Measure Bool) [IsFiniteMeasure μ] :
    μ.boolBias.toReal = |(μ {true}).toReal - (μ {false}).toReal| :=
  absDiff_toReal (measure_ne_top μ _) (measure_ne_top μ _)

/-- The real Boolean distance of two finite measures is the absolute difference of their masses
on `true`. -/
lemma toReal_boolDist (μ ν : Measure Bool) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    (μ.boolDist ν).toReal = |(μ {true}).toReal - (ν {true}).toReal| :=
  absDiff_toReal (measure_ne_top μ _) (measure_ne_top ν _)

/-- Boolean bias is twice the distance of the `true` mass from one half when the measure is
total. -/
lemma boolBias_eq_two_mul_absDiff_half (μ : Measure Bool)
    (htotal : μ {true} + μ {false} = 1) :
    μ.boolBias = 2 * ENNReal.absDiff (μ {true}) (1 / 2) := by
  have htrue_le : μ {true} ≤ 1 := htotal ▸ le_self_add
  have htrue_ne_top : μ {true} ≠ ⊤ := ne_top_of_le_ne_top one_ne_top htrue_le
  have hfalse : μ {false} = 1 - μ {true} := by
    rw [← htotal, ENNReal.add_sub_cancel_left htrue_ne_top]
  have hhalf : (1 / 2 : ℝ≥0∞) ≠ ⊤ := by simp
  have hfalse_ne_top : μ {false} ≠ ⊤ := hfalse ▸ sub_ne_top one_ne_top
  rw [boolBias, ← ENNReal.toReal_eq_toReal_iff' (ne_top_of_le_ne_top
      (add_ne_top.mpr ⟨htrue_ne_top, hfalse_ne_top⟩) (absDiff_le_add _ _))
      (mul_ne_top ofNat_ne_top (ne_top_of_le_ne_top (add_ne_top.mpr ⟨htrue_ne_top, hhalf⟩)
        (absDiff_le_add _ _))),
    absDiff_toReal htrue_ne_top hfalse_ne_top, toReal_mul, absDiff_toReal htrue_ne_top hhalf,
    hfalse, ENNReal.toReal_sub_of_le htrue_le one_ne_top]
  simp only [toReal_one, toReal_ofNat, toReal_div]
  rw [show (μ {true}).toReal - (1 - (μ {true}).toReal) =
      2 * ((μ {true}).toReal - 1 / 2) by ring, abs_mul, abs_two]

/-- Boolean bias under a probability measure is twice the distance of the `true` mass from one
half. -/
lemma boolBias_eq_two_mul_absDiff_half_of_isProbabilityMeasure
    (μ : Measure Bool) [IsProbabilityMeasure μ] :
    μ.boolBias = 2 * ENNReal.absDiff (μ {true}) (1 / 2) :=
  boolBias_eq_two_mul_absDiff_half μ (apply_true_add_apply_false_eq_one μ)

/-- The Boolean event distance satisfies the triangle inequality. -/
lemma boolDist_triangle (μ ν ρ : Measure Bool) :
    μ.boolDist ρ ≤ μ.boolDist ν + ν.boolDist ρ := absDiff_triangle _ _ _

/-- A measure has zero Boolean event distance from itself. -/
@[simp]
lemma boolDist_self (μ : Measure Bool) : μ.boolDist μ = 0 := absDiff_self _

/-- Boolean event distance is symmetric. -/
lemma boolDist_comm (μ ν : Measure Bool) : μ.boolDist ν = ν.boolDist μ := absDiff_comm _ _

/-- The Boolean distance between the ends of a hybrid sequence is at most the sum of the
distances between adjacent hybrids. -/
lemma boolDist_le_sum_range (μ : ℕ → Measure Bool) (q : ℕ) :
    (μ 0).boolDist (μ q) ≤ ∑ i ∈ Finset.range q, (μ i).boolDist (μ (i + 1)) := by
  simpa only [boolDist, absDiff_eq_edist] using edist_le_range_sum_edist (fun i => μ i {true}) q

/-- The mass of the `true` event is bounded by that of another measure plus their Boolean
distance. -/
lemma apply_true_le_add_boolDist (μ ν : Measure Bool) :
    μ {true} ≤ ν {true} + μ.boolDist ν :=
  le_add_tsub.trans (by gcongr; exact le_self_add)

/-- Two probability measures on `Bool` are within Boolean distance `ε` when each outcome has
mass under the first at most its mass under the second plus `ε`. -/
lemma boolDist_le_of_apply_le (μ ν : Measure Bool) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] {ε : ℝ≥0∞} (h : ∀ b, μ {b} ≤ ν {b} + ε) : μ.boolDist ν ≤ ε := by
  refine absDiff_le_iff.2
    ⟨h true, (ENNReal.add_le_add_iff_right (measure_ne_top μ {false})).1 ?_⟩
  calc ν {true} + μ {false} ≤ ν {true} + (ν {false} + ε) := by gcongr; exact h false
    _ = μ {true} + ε + μ {false} := by
      rw [← add_assoc, apply_true_add_apply_false_eq_one, add_right_comm,
        apply_true_add_apply_false_eq_one]

/-- A fair hidden-bit guessing experiment has the event distance of its two total branches. -/
lemma boolBias_bind_coin (coin μ ν : Measure Bool)
    (hcT : coin {true} = 1 / 2) (hcF : coin {false} = 1 / 2)
    (hμ : μ {true} + μ {false} = 1) (hν : ν {true} + ν {false} = 1) :
    (coin.bind fun b => (if b then μ else ν).bind
      fun z => Measure.dirac (b == z)).boolBias = μ.boolDist ν := by
  let : IsProbabilityMeasure μ := ⟨by rwa [← apply_true_add_apply_false]⟩
  let : IsProbabilityMeasure ν := ⟨by rwa [← apply_true_add_apply_false]⟩
  have hgame : ∀ x : Bool, (coin.bind fun b => (if b then μ else ν).bind
        fun z => Measure.dirac (b == z)) {x} = (μ {x} + ν {!x}) / 2 := by
    intro x
    simp only [Measure.bind_apply (MeasurableSet.singleton x) Measurable.of_discrete.aemeasurable,
      lintegral_fintype, Fintype.sum_bool, hcT, hcF]
    cases x <;> simp [Measure.dirac_apply', div_eq_mul_inv, mul_add, mul_comm]
  have hfin : ∀ x : Bool, (μ {x} + ν {!x}) / 2 ≠ ⊤ := fun x =>
    div_ne_top (add_ne_top.mpr ⟨measure_ne_top _ _, measure_ne_top _ _⟩) two_ne_zero
  have hm := congrArg ENNReal.toReal hμ
  have hn := congrArg ENNReal.toReal hν
  simp only [ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _),
    ENNReal.toReal_one] at hm hn
  unfold boolBias
  rw [hgame true, hgame false, ← ENNReal.toReal_eq_toReal_iff'
      (ne_top_of_le_ne_top (add_ne_top.mpr ⟨hfin true, hfin false⟩) (absDiff_le_add _ _))
      (boolDist_ne_top μ ν),
    absDiff_toReal (hfin true) (hfin false), toReal_boolDist]
  simp only [Bool.not_true, Bool.not_false, ENNReal.toReal_div,
    ENNReal.toReal_ofNat, ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)]
  congr 1
  linarith

end MeasureTheory.Measure
