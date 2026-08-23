/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
public import Mathlib.InformationTheory.KullbackLeibler.DataProcessing
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-!
# The Renyi moment generating function of a pair of measures

Mathlib states Kullback-Leibler for measures (`InformationTheory.klDiv`) but has no Renyi
divergence at all, so this is local development rather than a wrapper. It follows `klDiv`'s shape
deliberately: `ℝ≥0∞`-valued, defined by an integral of a function of `Measure.rnDeriv`, and
guarded by absolute continuity.

## Why the guard

`∫⁻ x, (∂μ/∂ν x) ^ a ∂ν` integrates against `ν`, so it cannot see a set where `ν` vanishes and
`μ` does not — it would report a finite value for a pair at infinite divergence. The `μ ≪ ν`
guard restores that, and it is what makes `renyiMGF_toMeasure` below an equality rather than an
inequality. Mathlib's `klDiv` carries the same guard for the same reason.

## The discrete theory

`ToMathlib.Probability.Divergence.RenyiDiscrete` identifies this with the countably supported
formula, so that development becomes a corollary of this one rather than a parallel copy. This
module is deliberately free of any dependence on that layer.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace InformationTheory

variable {α : Type*} [MeasurableSpace α]

open scoped Classical in
/-- The Renyi moment generating function of order `a`, also called the Hellinger integral.

For `a > 1` this is `∑' x, p x ^ a * q x ^ (1 - a)` in the countably supported case; see
`ToMathlib.Probability.Divergence.RenyiDiscrete`. -/
noncomputable def renyiMGF (a : ℝ) (μ ν : Measure α) : ℝ≥0∞ :=
  if μ ≪ ν then ∫⁻ x, (μ.rnDeriv ν x) ^ a ∂ν else ⊤

open scoped Classical in
theorem renyiMGF_of_ac {a : ℝ} {μ ν : Measure α} (h : μ ≪ ν) :
    renyiMGF a μ ν = ∫⁻ x, (μ.rnDeriv ν x) ^ a ∂ν := if_pos h

open scoped Classical in
@[simp]
theorem renyiMGF_of_not_ac {a : ℝ} {μ ν : Measure α} (h : ¬ μ ≪ ν) :
    renyiMGF a μ ν = ⊤ := if_neg h

/-- A measure has Renyi MGF one against itself. -/
@[simp]
theorem renyiMGF_self (a : ℝ) (μ : Measure α) [IsProbabilityMeasure μ] :
    renyiMGF a μ μ = 1 := by
  rw [renyiMGF_of_ac (Measure.AbsolutelyContinuous.refl μ)]
  have h : ∫⁻ x, (μ.rnDeriv μ x) ^ a ∂μ = ∫⁻ _, 1 ∂μ := by
    refine lintegral_congr_ae ?_
    filter_upwards [μ.rnDeriv_self] with x hx
    simp [hx]
  rw [h]
  simp

/-! ### Data processing

The inequality is Mathlib's, not ours. `ConvexOn.comp_rnDeriv_map_le` bounds `f` of the pushed
derivative by the conditional expectation of `f` of the original, for *any* convex `f`; taking
`f = (· ^ a)` and integrating is the whole argument. What remains is bookkeeping between the
`ℝ≥0∞` integral this file is stated in and the Bochner integral that scaffolding is stated in.

Both degenerate cases are genuinely trivial rather than swept aside: without absolute continuity,
and without integrability, the right-hand side is already `⊤`. -/

section DataProcessing

variable {β : Type*} [MeasurableSpace β]

/-- The Radon-Nikodym derivative is `ν`-almost everywhere finite, so raising it to a power
commutes with passing through `ℝ`. -/
theorem ofReal_toReal_rnDeriv_rpow (a : ℝ) (ha : 0 ≤ a) (μ ν : Measure α) [SigmaFinite μ] :
    (fun x => ENNReal.ofReal ((μ.rnDeriv ν x).toReal ^ a)) =ᵐ[ν]
      fun x => (μ.rnDeriv ν x) ^ a := by
  filter_upwards [μ.rnDeriv_lt_top ν] with x hx
  rw [← ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg ha,
    ENNReal.ofReal_toReal hx.ne]

theorem aestronglyMeasurable_toReal_rnDeriv_rpow (a : ℝ) (μ ν : Measure α) :
    AEStronglyMeasurable (fun x => (μ.rnDeriv ν x).toReal ^ a) ν :=
  ((Measure.measurable_rnDeriv μ ν).ennreal_toReal.pow_const a).aestronglyMeasurable

/-- A finite Renyi MGF is exactly integrability of the real-valued integrand. -/
theorem integrable_toReal_rnDeriv_rpow (a : ℝ) (ha : 0 ≤ a) (μ ν : Measure α) [SigmaFinite μ]
    (h : ∫⁻ x, (μ.rnDeriv ν x) ^ a ∂ν ≠ ⊤) :
    Integrable (fun x => (μ.rnDeriv ν x).toReal ^ a) ν := by
  refine ⟨aestronglyMeasurable_toReal_rnDeriv_rpow a μ ν, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (.of_forall fun x => Real.rpow_nonneg ENNReal.toReal_nonneg a),
    lintegral_congr_ae (ofReal_toReal_rnDeriv_rpow a ha μ ν)]
  exact h.lt_top

/-- The `ℝ≥0∞` integral of this file and the Bochner integral Mathlib's convexity scaffolding is
stated in are the same number. -/
theorem lintegral_rnDeriv_rpow_eq_ofReal (a : ℝ) (ha : 0 ≤ a) (μ ν : Measure α) [SigmaFinite μ]
    (h_int : Integrable (fun x => (μ.rnDeriv ν x).toReal ^ a) ν) :
    ∫⁻ x, (μ.rnDeriv ν x) ^ a ∂ν
      = ENNReal.ofReal (∫ x, (μ.rnDeriv ν x).toReal ^ a ∂ν) := by
  rw [ofReal_integral_eq_lintegral_ofReal h_int
      (.of_forall fun x => Real.rpow_nonneg ENNReal.toReal_nonneg a),
    lintegral_congr_ae (ofReal_toReal_rnDeriv_rpow a ha μ ν)]

/-- **Data processing inequality for the Renyi MGF**, in Bochner form. -/
theorem integral_toReal_rnDeriv_rpow_map_le (a : ℝ) (ha : 1 < a) (μ ν : Measure α)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] {g : α → β} (hg : Measurable g) (hac : μ ≪ ν)
    (h_int : Integrable (fun x => (μ.rnDeriv ν x).toReal ^ a) ν) :
    ∫ y, ((μ.map g).rnDeriv (ν.map g) y).toReal ^ a ∂(ν.map g)
      ≤ ∫ x, (μ.rnDeriv ν x).toReal ^ a ∂ν := by
  have hf : StronglyMeasurable (fun t : ℝ => t ^ a) := by fun_prop
  have hf_cvx : ConvexOn ℝ (Set.Ici (0 : ℝ)) (fun t : ℝ => t ^ a) := convexOn_rpow ha.le
  have hf_cont : ContinuousWithinAt (fun t : ℝ => t ^ a) (Set.Ici 0) 0 :=
    (Real.continuousAt_rpow_const 0 a (Or.inr (by linarith))).continuousWithinAt
  have hsm : StronglyMeasurable (fun y => ((μ.map g).rnDeriv (ν.map g) y).toReal ^ a) :=
    hf.comp_measurable (Measure.measurable_rnDeriv _ _).ennreal_toReal
  have hLint := hf_cvx.integrable_comp_rnDeriv_map hac hg hf hf_cont h_int
  calc ∫ y, ((μ.map g).rnDeriv (ν.map g) y).toReal ^ a ∂(ν.map g)
      = ∫ x, ((μ.map g).rnDeriv (ν.map g) (g x)).toReal ^ a ∂ν :=
        integral_map hg.aemeasurable hsm.aestronglyMeasurable
    _ ≤ ∫ x, (ν[fun x => (μ.rnDeriv ν x).toReal ^ a | ‹MeasurableSpace β›.comap g]) x ∂ν := by
        refine integral_mono_ae ?_ integrable_condExp ?_
        · exact (integrable_map_measure hsm.aestronglyMeasurable hg.aemeasurable).mp hLint
        · exact hf_cvx.comp_rnDeriv_map_le hac hg hf hf_cont h_int
    _ = ∫ x, (μ.rnDeriv ν x).toReal ^ a ∂ν := integral_condExp hg.comap_le

/-- **Data processing inequality for the Renyi MGF.**

Post-processing by a measurable function cannot increase it. Compare the hand-rolled discrete
proof in `ToMathlib.Probability.ProbabilityMassFunction.RenyiDivergence`, which does the fibrewise
Holder argument by hand; here the convexity is Mathlib's and the argument is one `calc`. -/
theorem renyiMGF_map_le (a : ℝ) (ha : 1 < a) (μ ν : Measure α)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] {g : α → β} (hg : Measurable g) :
    renyiMGF a (μ.map g) (ν.map g) ≤ renyiMGF a μ ν := by
  have ha0 : (0 : ℝ) ≤ a := by linarith
  by_cases hac : μ ≪ ν
  swap; · simp [renyiMGF_of_not_ac hac]
  by_cases htop : renyiMGF a μ ν = ⊤
  · simp [htop]
  rw [renyiMGF_of_ac hac] at htop ⊢
  have h_int := integrable_toReal_rnDeriv_rpow a ha0 μ ν htop
  have h_int_map : Integrable
      (fun y => ((μ.map g).rnDeriv (ν.map g) y).toReal ^ a) (ν.map g) :=
    (convexOn_rpow ha.le).integrable_comp_rnDeriv_map hac hg (by fun_prop)
      ((Real.continuousAt_rpow_const 0 a (Or.inr ha0)).continuousWithinAt) h_int
  rw [renyiMGF_of_ac (hac.map hg), lintegral_rnDeriv_rpow_eq_ofReal a ha0 _ _ h_int_map,
    lintegral_rnDeriv_rpow_eq_ofReal a ha0 _ _ h_int]
  exact ENNReal.ofReal_le_ofReal
    (integral_toReal_rnDeriv_rpow_map_le a ha μ ν hg hac h_int)

end DataProcessing

end InformationTheory
