/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
public import Mathlib.InformationTheory.KullbackLeibler.DataProcessing
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic
public import Mathlib.Probability.Kernel.Composition.RadonNikodym
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

open MeasureTheory ProbabilityTheory
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

/-! ### The Renyi divergence

`renyiDiv` normalises the MGF so that it is one for equal measures and monotone in the order. The
`a ≤ 1` guard matches the discrete definition, which uses it as a trivial bound. -/

open scoped Classical in
/-- The multiplicative Renyi divergence of order `a`. -/
noncomputable def renyiDiv (a : ℝ) (μ ν : Measure α) : ℝ≥0∞ :=
  if a ≤ 1 then 1 else (renyiMGF a μ ν) ^ ((a - 1)⁻¹ : ℝ)

open scoped Classical in
theorem renyiDiv_eq_rpow {a : ℝ} (ha : 1 < a) (μ ν : Measure α) :
    renyiDiv a μ ν = (renyiMGF a μ ν) ^ ((a - 1)⁻¹ : ℝ) := if_neg (not_le.mpr ha)

@[simp]
theorem renyiDiv_self (a : ℝ) (μ : Measure α) [IsProbabilityMeasure μ] :
    renyiDiv a μ μ = 1 := by
  rw [renyiDiv]
  split
  · rfl
  · simp

/-! ### Log-convexity of the Renyi MGF

`a ↦ renyiMGF a` is the moment generating function of the log-likelihood ratio under `ν`, so it is
log-convex. Mathlib states exactly the inequality that expresses this — `lintegral_mul_norm_pow_le`,
Hölder with two exponents summing to one — with no finiteness or positivity side conditions, so the
three-point interpolation is a direct application.

Interpolating at `1/2`, `1` and `a` converts a Renyi bound into a bound on the Hellinger affinity
`renyiMGF (1/2)`, which is the quantity that controls total variation. -/

/-- **Three-point interpolation for the Renyi MGF.**

At `θ = (a-1)/(a-1/2)` the exponents collapse to `∫⁻ ∂μ/∂ν ∂ν = 1`, which is the log-convexity
statement `M₁ ≤ M_{1/2}^θ · M_a^{1-θ}` with `M₁ = 1`. -/
theorem one_le_renyiMGF_half_rpow_mul_renyiMGF_rpow {a : ℝ} (ha : 1 < a) (μ ν : Measure α)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (hac : μ ≪ ν) :
    1 ≤ renyiMGF (1/2) μ ν ^ ((a-1)/(a-1/2)) * renyiMGF a μ ν ^ (1 - (a-1)/(a-1/2)) := by
  set θ : ℝ := (a-1)/(a-1/2) with hθdef
  have hden : a - 1/2 ≠ 0 := by linarith
  have hθ0 : 0 ≤ θ := div_nonneg (by linarith) (by linarith)
  have hθ1 : θ ≤ 1 := by rw [hθdef, div_le_one (by linarith)]; linarith
  have h2 : (2:ℝ)*a - 1 ≠ 0 := by linarith
  have hexp : (1/2 : ℝ) * θ + a * (1 - θ) = 1 := by rw [hθdef]; field_simp; linarith
  rw [renyiMGF_of_ac hac, renyiMGF_of_ac hac]
  have key := ENNReal.lintegral_mul_norm_pow_le
    (μ := ν) (f := fun x => μ.rnDeriv ν x ^ (1/2 : ℝ)) (g := fun x => μ.rnDeriv ν x ^ a)
    (p := θ) (q := 1 - θ)
    ((Measure.measurable_rnDeriv μ ν).pow_const _).aemeasurable
    ((Measure.measurable_rnDeriv μ ν).pow_const _).aemeasurable
    hθ0 (by linarith) (by linarith)
  refine le_trans (le_of_eq ?_) key
  rw [← measure_univ (μ := μ), ← Measure.lintegral_rnDeriv hac]
  refine lintegral_congr fun x => ?_
  rw [← ENNReal.rpow_mul, ← ENNReal.rpow_mul,
    ← ENNReal.rpow_add_of_nonneg _ _ (by positivity) (by nlinarith), hexp, ENNReal.rpow_one]

/-- The `ℝ≥0∞` half of the interpolation argument, with no measures involved: from a two-point
Hölder bound, recover a lower bound on `x²` in terms of `y`. -/
private theorem inv_rpow_le_rpow_two_of_one_le_mul {x y : ℝ≥0∞} {θ : ℝ} (hθ : 0 < θ)
    (h : 1 ≤ x ^ θ * y ^ (1 - θ)) :
    (y ^ ((1 - θ) * θ⁻¹ * 2))⁻¹ ≤ x ^ (2 : ℝ) := by
  have hinv : (0:ℝ) ≤ θ⁻¹ := (inv_pos.mpr hθ).le
  have h1 : (1:ℝ≥0∞) ≤ x * y ^ ((1 - θ) * θ⁻¹) := by
    have h' := ENNReal.rpow_le_rpow h hinv
    rwa [ENNReal.one_rpow, ENNReal.mul_rpow_of_nonneg _ _ hinv,
      ← ENNReal.rpow_mul, ← ENNReal.rpow_mul, mul_inv_cancel₀ hθ.ne', ENNReal.rpow_one] at h'
  have hx0 : x ≠ 0 := by rintro rfl; rw [zero_mul] at h1; exact absurd h1 (by simp)
  have hz0 : y ^ ((1 - θ) * θ⁻¹) ≠ 0 := by
    rintro hz; rw [hz, mul_zero] at h1; exact absurd h1 (by simp)
  have h2 : (y ^ ((1 - θ) * θ⁻¹))⁻¹ ≤ x :=
    (ENNReal.inv_le_iff_le_mul (fun _ => hz0) (fun _ => hx0)).mpr (by rwa [mul_comm])
  have h3 := ENNReal.rpow_le_rpow h2 (by norm_num : (0:ℝ) ≤ 2)
  rwa [ENNReal.inv_rpow, ← ENNReal.rpow_mul] at h3

/-- **A Renyi bound controls the Hellinger affinity.**

`renyiMGF (1/2)` is the Hellinger affinity (the Bhattacharyya coefficient in the discrete case),
and this is the inequality `BC² ≥ R_a⁻¹` that converts a Renyi divergence bound into one on it.
It is the interpolation above, rearranged. -/
theorem renyiDiv_inv_le_renyiMGF_half_rpow_two {a : ℝ} (ha : 1 < a) (μ ν : Measure α)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (hac : μ ≪ ν) :
    (renyiDiv a μ ν)⁻¹ ≤ renyiMGF (1/2) μ ν ^ (2 : ℝ) := by
  have h1 : a - 1 ≠ 0 := by linarith
  have h2 : a - 1/2 ≠ 0 := by linarith
  have h3 : a * 2 - 1 ≠ 0 := by linarith
  have hθpos : 0 < (a-1)/(a-1/2) := div_pos (by linarith) (by linarith)
  have harith : (1 - (a-1)/(a-1/2)) * ((a-1)/(a-1/2))⁻¹ * 2 = (a - 1)⁻¹ := by
    field_simp
    linarith
  have := inv_rpow_le_rpow_two_of_one_le_mul hθpos
    (one_le_renyiMGF_half_rpow_mul_renyiMGF_rpow ha μ ν hac)
  rwa [harith, ← renyiDiv_eq_rpow ha] at this

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

/-! ### Data processing for Markov kernels

Post-processing by a kernel rather than a function. The route is Mathlib's own for
`klDiv_comp_right_le`: a composition is the second marginal of a `compProd`, the first factor is
unchanged by pairing with a common kernel, and the map inequality does the rest. -/

/-- Pairing both measures with the same kernel leaves the Renyi MGF unchanged. -/
theorem renyiMGF_compProd_left (a : ℝ) (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (κ : Kernel α β) [IsMarkovKernel κ] :
    renyiMGF a (μ ⊗ₘ κ) (ν ⊗ₘ κ) = renyiMGF a μ ν := by
  by_cases hac : μ ≪ ν
  · have hac' : μ ⊗ₘ κ ≪ ν ⊗ₘ κ :=
      Measure.AbsolutelyContinuous.compProd_of_compProd hac fun _ a => a
    rw [renyiMGF_of_ac hac', renyiMGF_of_ac hac]
    have h1 : ∫⁻ p, ((μ ⊗ₘ κ).rnDeriv (ν ⊗ₘ κ) p) ^ a ∂(ν ⊗ₘ κ)
        = ∫⁻ p, (μ.rnDeriv ν p.1) ^ a ∂(ν ⊗ₘ κ) := by
      refine lintegral_congr_ae ?_
      filter_upwards [ProbabilityTheory.rnDeriv_measure_compProd_left μ ν κ] with p hp
      rw [hp]
    rw [h1]
    have h2 : ∫⁻ x, (μ.rnDeriv ν x) ^ a ∂((ν ⊗ₘ κ).fst)
        = ∫⁻ p, (μ.rnDeriv ν p.1) ^ a ∂(ν ⊗ₘ κ) := by
      rw [Measure.fst]
      exact lintegral_map (by fun_prop) measurable_fst
    rw [Measure.fst_compProd] at h2
    exact h2.symm
  · rw [renyiMGF_of_not_ac hac, renyiMGF_of_not_ac]
    intro hcon
    exact hac (by
      have := hcon.map (f := Prod.fst) measurable_fst
      rwa [← Measure.fst, ← Measure.fst, Measure.fst_compProd, Measure.fst_compProd] at this)

/-- **Data processing inequality for the Renyi MGF under a Markov kernel.**

Since `κ ∘ₘ μ` is `Measure.bind μ κ`, this is the statement that post-processing a computation by
a randomised procedure cannot increase the divergence. -/
theorem renyiMGF_comp_right_le (a : ℝ) (ha : 1 < a) (μ ν : Measure α)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] (κ : Kernel α β) [IsMarkovKernel κ] :
    renyiMGF a (κ ∘ₘ μ) (κ ∘ₘ ν) ≤ renyiMGF a μ ν :=
  calc renyiMGF a (κ ∘ₘ μ) (κ ∘ₘ ν)
    _ ≤ renyiMGF a (μ ⊗ₘ κ) (ν ⊗ₘ κ) := by
        rw [← Measure.snd_compProd μ κ, ← Measure.snd_compProd ν κ, Measure.snd, Measure.snd]
        exact renyiMGF_map_le a ha _ _ measurable_snd
    _ = renyiMGF a μ ν := renyiMGF_compProd_left a μ ν κ

end DataProcessing

end InformationTheory
