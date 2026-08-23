/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import ToMathlib.Probability.Divergence.Renyi
public import ToMathlib.Probability.ProbabilityMassFunction.RadonNikodym
public import ToMathlib.Probability.ProbabilityMassFunction.RenyiDivergence

/-!
# The discrete Renyi MGF as a corollary of the measure-level one

`ToMathlib.Probability.Divergence.Renyi` defines `InformationTheory.renyiMGF` for a pair of
measures. `renyiMGF_toMeasure` below identifies it with `PMF.renyiMGF` on a countable discrete
space, so a result proved once at the measure level can be read back as the `tsum` formula the
existing development is stated in.

That is what keeps the migration cheap: the discrete theory does not have to be reproved, and
downstream users of `PMF.renyiMGF` are untouched.

This module exists only to connect the two layers, and is the only place in the Renyi development
that mentions `PMF` at all. It is expected to disappear once the discrete layer is retired.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace InformationTheory

variable {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α] [Countable α]


/-- **The measure-level Renyi MGF agrees with the `PMF` one.**

Every lemma proved about `renyiMGF` therefore transports to `PMF.renyiMGF`, and conversely. -/
theorem renyiMGF_toMeasure (a : ℝ) (ha : 1 < a) (p q : PMF α) :
    renyiMGF a p.toMeasure q.toMeasure = PMF.renyiMGF a p q := by
  have ha0 : 0 < a := lt_trans one_pos ha
  by_cases hac : p.toMeasure ≪ q.toMeasure
  · have hsupp := (PMF.absolutelyContinuous_toMeasure_iff p q).mp hac
    rw [renyiMGF_of_ac hac]
    have hcongr : ∫⁻ x, (p.toMeasure.rnDeriv q.toMeasure x) ^ a ∂q.toMeasure
        = ∫⁻ x, (p x / q x) ^ a ∂q.toMeasure := by
      refine lintegral_congr_ae ?_
      filter_upwards [PMF.rnDeriv_toMeasure p q] with x hx
      rw [hx]
    rw [hcongr, lintegral_countable']
    refine tsum_congr fun x => ?_
    rw [PMF.toMeasure_apply_singleton _ _ (MeasurableSet.singleton x)]
    by_cases hq : q x = 0
    · rw [hq, hsupp x hq]
      simp [ENNReal.zero_rpow_of_pos ha0]
    · rw [ENNReal.div_rpow_of_nonneg _ _ ha0.le,
        ENNReal.rpow_sub _ _ hq (PMF.apply_ne_top q x), ENNReal.rpow_one]
      simp only [div_eq_mul_inv]
      ring
  · rw [renyiMGF_of_not_ac hac]
    obtain ⟨x, hq, hp⟩ : ∃ x, q x = 0 ∧ p x ≠ 0 := by
      by_contra hcon
      exact hac ((PMF.absolutelyContinuous_toMeasure_iff p q).mpr
        fun x hx => by_contra fun h => hcon ⟨x, hx, h⟩)
    refine (ENNReal.tsum_eq_top_of_eq_top ⟨x, ?_⟩).symm
    rw [hq, ENNReal.zero_rpow_of_neg (by linarith)]
    exact ENNReal.mul_top (by
      simp only [ne_eq, ENNReal.rpow_eq_zero_iff, hp, false_and, false_or, not_and, not_lt]
      exact fun _ => ha0.le)

/-! ### The discrete theory as a corollary

`PMF.renyiMGF_self` is proved directly in
`ToMathlib.Probability.ProbabilityMassFunction.RenyiDivergence`. Here it falls out of the
measure-level statement and `renyiMGF_toMeasure`, with no `tsum` manipulation — which is the
shape every discrete corollary of a measure-level divergence result will take. -/
example (a : ℝ) (ha : 1 < a) (p : PMF α) : PMF.renyiMGF a p p = 1 := by
  rw [← renyiMGF_toMeasure a ha p p, renyiMGF_self]

end InformationTheory
