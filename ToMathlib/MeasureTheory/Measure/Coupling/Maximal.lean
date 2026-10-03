/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import ToMathlib.MeasureTheory.Measure.Coupling
public import ToMathlib.MeasureTheory.Measure.TotalVariation
public import Mathlib.MeasureTheory.Measure.Dirac.Basic
public import ToMathlib.MeasureTheory.Measure.FinsetConcentrated

/-!
# Maximal couplings of finitely supported measures

Two probability measures concentrated on a common finite set `F` overlap by
`∑ a ∈ F, min (μ {a}) (ν {a})`, and their total variation is one minus this overlap. No coupling
puts more than the overlap `min (μ {a}) (ν {a})` on a diagonal point, and `maximalCoupling`, which
puts the overlap on the diagonal and spreads the residual masses independently, attains it.
-/

public section

noncomputable section

open ENNReal

namespace MeasureTheory.Measure

variable {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]

/-- A probability measure concentrated on a finite set has point masses summing to one. -/
private theorem sum_apply_singleton_eq_one {μ : Measure α} [IsProbabilityMeasure μ] {F : Finset α}
    (hF : μ (↑F)ᶜ = 0) : ∑ a ∈ F, μ {a} = 1 := by
  have h := measure_inter_conull hF (s := Set.univ)
  rw [Set.univ_inter, measure_univ] at h
  rw [sum_measure_singleton, h]

/-- Truncated subtraction distributes over a finite sum with a finite subtrahend. -/
private theorem sum_tsub_distrib_of_le {ι : Type*} (s : Finset ι) {f g : ι → ℝ≥0∞}
    (hg : ∑ i ∈ s, g i ≠ ⊤) (h : ∀ i ∈ s, g i ≤ f i) :
    ∑ i ∈ s, (f i - g i) = ∑ i ∈ s, f i - ∑ i ∈ s, g i := by
  refine ENNReal.eq_sub_of_add_eq hg ?_
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i hi => tsub_add_cancel_of_le (h i hi)

/-- Spreading a mass against weights normalized by their total returns the mass, whenever the
total is finite and vanishes only together with the mass. -/
private theorem sum_mul_div_self {ι : Type*} {F : Finset ι} {p : ι → ℝ≥0∞}
    (htop : ∑ i ∈ F, p i ≠ ⊤) (x : ℝ≥0∞) (hx : ∑ i ∈ F, p i = 0 → x = 0) :
    ∑ i ∈ F, p i * x / ∑ j ∈ F, p j = x := by
  simp_rw [div_eq_mul_inv]
  rw [← Finset.sum_mul, ← Finset.sum_mul, mul_right_comm]
  by_cases h0 : ∑ i ∈ F, p i = 0
  · simp [hx h0]
  · rw [ENNReal.mul_inv_cancel h0 htop, one_mul]

/-- Point masses of a probability measure over a finite set have a finite sum. -/
private theorem sum_apply_singleton_ne_top (μ : Measure α) [IsProbabilityMeasure μ]
    (s : Finset α) : ∑ a ∈ s, μ {a} ≠ ⊤ := by
  rw [sum_measure_singleton]
  exact measure_ne_top μ _

section overlap

variable {μ ν : Measure α} {F : Finset α}

/-- One minus the overlap is the total excess of the first measure over the second. -/
theorem one_sub_sum_min_eq_sum_tsub [IsProbabilityMeasure μ] (hμ : μ (↑F)ᶜ = 0) :
    1 - ∑ a ∈ F, min (μ {a}) (ν {a}) = ∑ a ∈ F, (μ {a} - ν {a}) := by
  have hfin : ∑ a ∈ F, min (μ {a}) (ν {a}) ≠ ⊤ :=
    ne_top_of_le_ne_top (sum_apply_singleton_ne_top μ F)
      (Finset.sum_le_sum fun a _ => min_le_left _ _)
  rw [← sum_apply_singleton_eq_one hμ,
    ← sum_tsub_distrib_of_le _ hfin fun a _ => min_le_left _ _]
  exact Finset.sum_congr rfl fun a _ => tsub_min

/-- The total excesses of each measure over the other agree. -/
theorem sum_tsub_comm [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : μ (↑F)ᶜ = 0) (hν : ν (↑F)ᶜ = 0) :
    ∑ a ∈ F, (ν {a} - μ {a}) = ∑ a ∈ F, (μ {a} - ν {a}) := by
  rw [← one_sub_sum_min_eq_sum_tsub hν, ← one_sub_sum_min_eq_sum_tsub hμ]
  simp only [min_comm]

/-- Total variation between measures concentrated on a common finite set is the total excess of
the first over the second. -/
theorem etvDist_eq_sum_tsub [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : μ (↑F)ᶜ = 0) (hν : ν (↑F)ᶜ = 0) :
    μ.etvDist ν = ∑ a ∈ F, (μ {a} - ν {a}) := by
  classical
  have hsymm := sum_tsub_comm hμ hν
  have hexcess (μ ν : Measure α) (hμ : μ (↑F)ᶜ = 0) (hν : ν (↑F)ᶜ = 0) (s : Set α) :
      μ s ≤ ν s + ∑ a ∈ F, (μ {a} - ν {a}) := by
    rw [apply_eq_sum_indicator_of_compl_eq_zero hμ, apply_eq_sum_indicator_of_compl_eq_zero hν,
      ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun a _ => ?_
    by_cases ha : a ∈ s
    · simp only [Set.indicator_of_mem ha]
      exact le_add_tsub
    · simp only [Set.indicator_of_notMem ha, zero_add, zero_le]
  apply le_antisymm
  · refine iSup_le fun s => ENNReal.absDiff_le_iff.2 ⟨hexcess μ ν hμ hν s, ?_⟩
    rw [← hsymm]
    exact hexcess ν μ hν hμ s
  · let t : Finset α := F.filter fun a => ν {a} < μ {a}
    have ht : MeasurableSet (↑t : Set α) := t.measurableSet
    refine le_trans ?_ (absDiff_apply_le_etvDist μ ν ht)
    refine le_trans ?_ (le_self_add : μ ↑t - ν ↑t ≤ (μ ↑t - ν ↑t) + (ν ↑t - μ ↑t))
    rw [← sum_measure_singleton, ← sum_measure_singleton,
      ← sum_tsub_distrib_of_le _ (sum_apply_singleton_ne_top ν t)
        fun a ha => (Finset.mem_filter.1 ha).2.le, Finset.sum_filter]
    refine le_of_eq (Finset.sum_congr rfl fun a _ => ?_)
    split_ifs with h
    · rfl
    · exact tsub_eq_zero_of_le (not_lt.1 h)

/-- Total variation between measures concentrated on a common finite set is one minus their
overlap. -/
theorem etvDist_eq_one_sub_sum_min [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : μ (↑F)ᶜ = 0) (hν : ν (↑F)ᶜ = 0) :
    μ.etvDist ν = 1 - ∑ a ∈ F, min (μ {a}) (ν {a}) := by
  rw [etvDist_eq_sum_tsub hμ hν, one_sub_sum_min_eq_sum_tsub hμ]

end overlap

/-- No coupling puts more than the overlap on a diagonal point. -/
theorem IsCoupling.apply_diag_le {μ ν : Measure α} {c : Measure (α × α)}
    (hc : IsCoupling c μ ν) (a : α) : c {(a, a)} ≤ min (μ {a}) (ν {a}) := by
  refine le_min ?_ ?_
  · calc c {(a, a)} ≤ c (Prod.fst ⁻¹' {a}) := measure_mono fun z hz => by simp_all
      _ = μ {a} := by rw [← Measure.fst_apply (measurableSet_singleton a), hc.fst_eq]
  · calc c {(a, a)} ≤ c (Prod.snd ⁻¹' {a}) := measure_mono fun z hz => by simp_all
      _ = ν {a} := by rw [← Measure.snd_apply (measurableSet_singleton a), hc.snd_eq]

/-- The maximal coupling of two measures on a finite set: the overlap `min (μ {a}) (ν {a})` sits
on the diagonal, and the residual masses are spread independently. It is a coupling of `μ` and `ν`
when both are probability measures concentrated on `F` (`isCoupling_maximalCoupling`). -/
def maximalCoupling (F : Finset α) (μ ν : Measure α) : Measure (α × α) :=
  (∑ a ∈ F, min (μ {a}) (ν {a}) • dirac (a, a)) +
    ∑ a ∈ F, ∑ b ∈ F,
      ((μ {a} - ν {a}) * (ν {b} - μ {b}) / ∑ c ∈ F, (μ {c} - ν {c})) • dirac (a, b)

section maximal

variable {μ ν : Measure α} {F : Finset α}

/-- The maximal coupling of two probability measures concentrated on a finite set is a
coupling. -/
theorem isCoupling_maximalCoupling [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : μ (↑F)ᶜ = 0) (hν : ν (↑F)ᶜ = 0) :
    IsCoupling (maximalCoupling F μ ν) μ ν := by
  classical
  have hsymm := sum_tsub_comm hμ hν
  have htop : ∑ c ∈ F, (μ {c} - ν {c}) ≠ ⊤ :=
    ne_top_of_le_ne_top (sum_apply_singleton_ne_top μ F)
      (Finset.sum_le_sum fun _ _ => tsub_le_self)
  have htop' : ∑ c ∈ F, (ν {c} - μ {c}) ≠ ⊤ := hsymm ▸ htop
  constructor
  · ext s hs
    rw [Measure.fst_apply hs, apply_eq_sum_indicator_of_compl_eq_zero hμ s, maximalCoupling]
    simp only [Measure.add_apply, Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply,
      smul_eq_mul, Measure.dirac_apply' _ (measurable_fst hs)]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a ha => ?_
    by_cases has : a ∈ s
    · simp only [Set.indicator, Set.mem_preimage, has, ↓reduceIte, Pi.one_apply, mul_one]
      simp_rw [mul_comm (μ {a} - ν {a})]
      rw [← hsymm, sum_mul_div_self htop' (μ {a} - ν {a}) fun h0 =>
          (Finset.sum_eq_zero_iff.1 (hsymm ▸ h0)) a ha]
      exact (add_comm _ _).trans tsub_add_min
    · simp [Set.indicator, has]
  · ext s hs
    rw [Measure.snd_apply hs, apply_eq_sum_indicator_of_compl_eq_zero hν s, maximalCoupling]
    simp only [Measure.add_apply, Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply,
      smul_eq_mul, Measure.dirac_apply' _ (measurable_snd hs)]
    rw [Finset.sum_comm (s := F) (t := F), ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun b hb => ?_
    by_cases hbs : b ∈ s
    · simp only [Set.indicator, Set.mem_preimage, hbs, ↓reduceIte, Pi.one_apply, mul_one]
      rw [sum_mul_div_self htop (ν {b} - μ {b}) fun h0 =>
          (Finset.sum_eq_zero_iff.1 (hsymm.trans h0)) b hb, min_comm]
      exact (add_comm _ _).trans tsub_add_min
    · simp [Set.indicator, hbs]

/-- The maximal coupling puts at least the overlap on each diagonal point of the set. -/
theorem min_le_maximalCoupling_apply_diag {a : α} (ha : a ∈ F) :
    min (μ {a}) (ν {a}) ≤ maximalCoupling F μ ν {(a, a)} := by
  rw [maximalCoupling, Measure.add_apply]
  refine le_add_right ?_
  simp only [Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply, smul_eq_mul]
  refine le_trans ?_ (Finset.single_le_sum (fun _ _ => zero_le) ha)
  simp

end maximal

end MeasureTheory.Measure
