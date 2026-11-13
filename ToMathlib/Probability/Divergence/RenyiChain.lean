/-
Copyright (c) 2026 XC0R. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XC0R
-/

module
public import ToMathlib.Probability.Divergence.Renyi

/-!
# Rényi chain rule over countable spaces, and probability preservation

On a countable space with measurable singletons, the Rényi moment generating function of finite
measures is the Hellinger sum `∑' x, μ {x} ^ a * ν {x} ^ (1 - a)` (`renyiMGF_eq_tsum`). The joint
sum of two compositions `μ ⊗ₘ κ` and `ν ⊗ₘ η` with *different* kernels factors through the first
step (`renyiMGF_compProd`), and data processing then gives the one-step chain rule
`renyiMGF_bind_le`: if every continuation pair is within `B`, the bound multiplies. This
generalizes the same-kernel `renyiMGF_compProd_left`.

`lt_measure_of_renyiDiv_le_sqrt_two` turns a bound `R_{2λ-1}(μ ‖ ν) ≤ √2` on the Rényi divergence
into the transfer of an event of probability above `T · 2^{-(λ-1)}` under `μ` to probability above
`T · 2^{-λ}` under `ν`, for any `T ≥ 1`, through `measure_rpow_div_renyiDiv_le`.
-/

public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace InformationTheory

section Discrete

variable {α : Type*} [MeasurableSpace α] [Countable α] [MeasurableSingletonClass α]

/-- On a countable space, for `a > 1`, the Rényi MGF of finite measures is the Hellinger sum of
the point masses (`⊤` exactly when some point charged by `μ` is not charged by `ν`). -/
theorem renyiMGF_eq_tsum {a : ℝ} (ha : 1 < a) (μ ν : Measure α) [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] :
    renyiMGF a μ ν = ∑' x, μ {x} ^ a * ν {x} ^ (1 - a) := by
  have ha0 : 0 < a := by linarith
  have ha1 : 1 - a < 0 := by linarith
  by_cases hac : μ ≪ ν
  · have hwd : ν.withDensity (fun x => μ {x} / ν {x}) = μ := by
      refine Measure.ext_of_singleton fun x => ?_
      rw [withDensity_apply _ (measurableSet_singleton x), Measure.restrict_singleton,
        lintegral_smul_measure, lintegral_dirac, smul_eq_mul]
      by_cases h0 : ν {x} = 0
      · rw [h0, zero_mul, hac h0]
      · rw [ENNReal.mul_div_cancel h0 (measure_ne_top _ _)]
    have hrn : μ.rnDeriv ν =ᵐ[ν] fun x => μ {x} / ν {x} := by
      conv_lhs => rw [← hwd]
      exact Measure.rnDeriv_withDensity ν (measurable_of_countable _)
    rw [renyiMGF_of_ac hac, lintegral_congr_ae (hrn.mono fun x hx => by rw [hx]),
      lintegral_countable']
    refine tsum_congr fun x => ?_
    by_cases h0 : ν {x} = 0
    · rw [h0, mul_zero, hac h0, ENNReal.zero_rpow_of_pos ha0, zero_mul]
    · rw [ENNReal.div_rpow_of_nonneg _ _ ha0.le, ENNReal.rpow_sub _ _ h0 (measure_ne_top _ _),
        ENNReal.rpow_one]
      simp only [div_eq_mul_inv]
      ring
  · rw [renyiMGF_of_not_ac hac, eq_comm, ← top_le_iff]
    obtain ⟨x, hμx, hνx⟩ : ∃ x, μ {x} ≠ 0 ∧ ν {x} = 0 := by
      by_contra hne
      simp only [not_exists, not_and] at hne
      refine hac (Measure.AbsolutelyContinuous.mk fun s _ hs => ?_)
      rw [← Set.biUnion_of_singleton s]
      refine measure_biUnion_null_iff (Set.to_countable s) |>.2 fun x hx => ?_
      by_contra h
      exact hne x h (measure_mono_null (Set.singleton_subset_iff.2 hx) hs)
    calc ⊤ = μ {x} ^ a * ν {x} ^ (1 - a) := by
          rw [hνx, ENNReal.zero_rpow_of_neg ha1, ENNReal.mul_top (by simpa [ha0] using hμx)]
      _ ≤ _ := ENNReal.le_tsum (f := fun x => μ {x} ^ a * ν {x} ^ (1 - a)) x

/-- A finite measure of total mass at most `1` on a countable space has Rényi MGF at most `1`
against itself. -/
theorem renyiMGF_self_le {a : ℝ} (ha : 1 < a) (μ : Measure α) [IsFiniteMeasure μ]
    (h1 : μ Set.univ ≤ 1) : renyiMGF a μ μ ≤ 1 := by
  rw [renyiMGF_eq_tsum ha]
  calc ∑' x, μ {x} ^ a * μ {x} ^ (1 - a) ≤ ∑' x, μ {x} := by
        refine ENNReal.tsum_le_tsum fun x => le_of_eq ?_
        by_cases h0 : μ {x} = 0
        · rw [h0, ENNReal.zero_rpow_of_pos (by linarith), zero_mul]
        · rw [← ENNReal.rpow_add _ _ h0 (measure_ne_top _ _), add_sub_cancel, ENNReal.rpow_one]
    _ = μ Set.univ := by rw [← lintegral_one, lintegral_countable']; simp
    _ ≤ 1 := h1

end Discrete

section Bind

variable {ι α : Type*} [MeasurableSpace ι] [Countable ι] [MeasurableSingletonClass ι]
  [MeasurableSpace α] [Countable α] [MeasurableSingletonClass α]

omit [Countable α] in
/-- A composition with a kernel built from a function charges the singleton `(u, x)` with
`μ {u} * f u {x}`. -/
theorem compProd_ofFunOfCountable_singleton (μ : Measure ι) (f : ι → Measure α)
    [IsFiniteKernel (Kernel.ofFunOfCountable f)] (u : ι) (x : α) :
    (μ ⊗ₘ Kernel.ofFunOfCountable f) {(u, x)} = μ {u} * f u {x} := by
  rw [← Set.singleton_prod_singleton, Measure.compProd_apply_prod (measurableSet_singleton u)
    (measurableSet_singleton x), Measure.restrict_singleton, lintegral_smul_measure,
    lintegral_dirac, smul_eq_mul]
  rfl

/-- The joint Hellinger sum of two compositions with different kernels factors through the first
step. -/
theorem renyiMGF_compProd {a : ℝ} (ha : 1 < a) (μ ν : Measure ι) [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] (fQ fP : ι → Measure α) [IsFiniteKernel (Kernel.ofFunOfCountable fQ)]
    [IsFiniteKernel (Kernel.ofFunOfCountable fP)] :
    renyiMGF a (μ ⊗ₘ Kernel.ofFunOfCountable fQ) (ν ⊗ₘ Kernel.ofFunOfCountable fP) =
      ∑' u, μ {u} ^ a * ν {u} ^ (1 - a) * renyiMGF a (fQ u) (fP u) := by
  have hQ : ∀ u, IsFiniteMeasure (fQ u) := fun u => by
    have : IsFiniteMeasure (Kernel.ofFunOfCountable fQ u) := inferInstance
    exact this
  have hP : ∀ u, IsFiniteMeasure (fP u) := fun u => by
    have : IsFiniteMeasure (Kernel.ofFunOfCountable fP u) := inferInstance
    exact this
  rw [renyiMGF_eq_tsum ha, ENNReal.tsum_prod']
  refine tsum_congr fun u => ?_
  rw [renyiMGF_eq_tsum ha, ← ENNReal.tsum_mul_left]
  refine tsum_congr fun x => ?_
  rw [compProd_ofFunOfCountable_singleton, compProd_ofFunOfCountable_singleton,
    ENNReal.mul_rpow_of_ne_top (measure_ne_top _ _) (measure_ne_top _ _),
    ENNReal.mul_rpow_of_ne_top (measure_ne_top _ _) (measure_ne_top _ _)]
  ring

/-- **Chain rule, one step.** If every continuation pair is within `B`, the composed pair is
within the first step's MGF times `B`. -/
theorem renyiMGF_bind_le {a : ℝ} (ha : 1 < a) (μ ν : Measure ι) [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] (fQ fP : ι → Measure α) (hQ1 : ∀ u, fQ u Set.univ ≤ 1)
    (hP1 : ∀ u, fP u Set.univ ≤ 1) {B : ℝ≥0∞} (hB : ∀ u, renyiMGF a (fQ u) (fP u) ≤ B) :
    renyiMGF a (μ.bind fQ) (ν.bind fP) ≤ renyiMGF a μ ν * B := by
  have : IsFiniteKernel (Kernel.ofFunOfCountable fQ) := ⟨⟨1, ENNReal.one_lt_top, hQ1⟩⟩
  have : IsFiniteKernel (Kernel.ofFunOfCountable fP) := ⟨⟨1, ENNReal.one_lt_top, hP1⟩⟩
  have hsnd : ∀ (ρ : Measure ι) (f : ι → Measure α) [IsFiniteMeasure ρ]
      [IsFiniteKernel (Kernel.ofFunOfCountable f)],
      (ρ ⊗ₘ Kernel.ofFunOfCountable f).map Prod.snd = ρ.bind f := fun ρ f _ _ => by
    rw [← Measure.snd, Measure.snd_compProd]
    rfl
  calc renyiMGF a (μ.bind fQ) (ν.bind fP)
      = renyiMGF a ((μ ⊗ₘ Kernel.ofFunOfCountable fQ).map Prod.snd)
          ((ν ⊗ₘ Kernel.ofFunOfCountable fP).map Prod.snd) := by rw [hsnd, hsnd]
    _ ≤ renyiMGF a (μ ⊗ₘ Kernel.ofFunOfCountable fQ) (ν ⊗ₘ Kernel.ofFunOfCountable fP) :=
        renyiMGF_map_le a ha _ _ measurable_snd
    _ = ∑' u, μ {u} ^ a * ν {u} ^ (1 - a) * renyiMGF a (fQ u) (fP u) :=
        renyiMGF_compProd ha μ ν fQ fP
    _ ≤ ∑' u, μ {u} ^ a * ν {u} ^ (1 - a) * B := by gcongr with u; exact hB u
    _ = renyiMGF a μ ν * B := by rw [ENNReal.tsum_mul_right, renyiMGF_eq_tsum ha]

end Bind

section Transfer

/-- A Rényi divergence bound `exp E` is an MGF bound `exp ((a - 1) E)`. -/
theorem renyiMGF_le_of_renyiDiv_le {α : Type*} [MeasurableSpace α] {a : ℝ} (ha : 1 < a)
    {μ ν : Measure α} {E : ℝ} (h : renyiDiv a μ ν ≤ ENNReal.ofReal (Real.exp E)) :
    renyiMGF a μ ν ≤ ENNReal.ofReal (Real.exp ((a - 1) * E)) := by
  have ham : a - 1 ≠ 0 := by linarith
  rw [renyiDiv_eq_rpow ha] at h
  calc renyiMGF a μ ν = (renyiMGF a μ ν ^ (a - 1)⁻¹) ^ (a - 1) :=
        (ENNReal.rpow_inv_rpow ham _).symm
    _ ≤ ENNReal.ofReal (Real.exp E) ^ (a - 1) := ENNReal.rpow_le_rpow h (by linarith)
    _ = _ := by
        rw [ENNReal.ofReal_rpow_of_nonneg (Real.exp_pos _).le (by linarith), ← Real.exp_mul,
          mul_comm]

/-- **Probability preservation at order `2λ - 1`** from `R_{2λ-1}(μ ‖ ν) ≤ √2`, with a parameter
`T ≥ 1`: an event of probability above `T · 2^{-(λ-1)}` under `μ` has probability above
`T · 2^{-λ}` under `ν`. -/
theorem lt_measure_of_renyiDiv_le_sqrt_two {α : Type*} [MeasurableSpace α] (lam : ℕ)
    (hlam : 2 ≤ lam) (T : ℝ≥0∞) (hT : 1 ≤ T) (μ ν : Measure α) [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] (hD : renyiDiv (2 * lam - 1) μ ν ≤ (2 : ℝ≥0∞) ^ (1 / 2 : ℝ))
    {s : Set α} (hs : MeasurableSet s) (hwin : T * (2 : ℝ≥0∞) ^ (-((lam : ℝ) - 1)) < μ s) :
    T * (2 : ℝ≥0∞) ^ (-(lam : ℝ)) < ν s := by
  set a : ℝ := 2 * lam - 1 with ha_def
  have hlam' : (2 : ℝ) ≤ lam := by exact_mod_cast hlam
  have ha : 1 < a := by rw [ha_def]; linarith
  have hP := measure_rpow_div_renyiDiv_le ha μ ν hs
  have he : 0 < a / (a - 1) := div_pos (by linarith) (by linarith)
  have hQ := ENNReal.rpow_lt_rpow hwin he
  have h2 : ((2 : ℝ≥0∞) ^ (-((lam : ℝ) - 1))) ^ (a / (a - 1)) =
      (2 : ℝ≥0∞) ^ (-(lam : ℝ)) * (2 : ℝ≥0∞) ^ (1 / 2 : ℝ) := by
    rw [← ENNReal.rpow_mul, ← ENNReal.rpow_add _ _ (by norm_num) (by norm_num)]
    congr 1
    rw [ha_def]
    have : (lam : ℝ) - 1 ≠ 0 := by linarith
    rw [show (2 * (lam : ℝ) - 1 - 1) = 2 * ((lam : ℝ) - 1) by ring]
    field_simp
    ring
  rw [ENNReal.mul_rpow_of_nonneg _ _ he.le, h2] at hQ
  have hTe : T ≤ T ^ (a / (a - 1)) := by
    have : 1 ≤ a / (a - 1) := by rw [le_div_iff₀ (by linarith)]; linarith
    calc T = T ^ (1 : ℝ) := (ENNReal.rpow_one T).symm
      _ ≤ T ^ (a / (a - 1)) := ENNReal.rpow_le_rpow_of_exponent_le hT this
  have hQ' : T * ((2 : ℝ≥0∞) ^ (-(lam : ℝ)) * (2 : ℝ≥0∞) ^ (1 / 2 : ℝ)) < μ s ^ (a / (a - 1)) :=
    lt_of_le_of_lt (by gcongr) hQ
  have hs2 : (2 : ℝ≥0∞) ^ (1 / 2 : ℝ) ≠ 0 := by positivity
  have hs2' : (2 : ℝ≥0∞) ^ (1 / 2 : ℝ) ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_nonneg (by norm_num) (by norm_num)
  calc T * (2 : ℝ≥0∞) ^ (-(lam : ℝ)) =
        T * ((2 : ℝ≥0∞) ^ (-(lam : ℝ)) * (2 : ℝ≥0∞) ^ (1 / 2 : ℝ)) /
          (2 : ℝ≥0∞) ^ (1 / 2 : ℝ) := by rw [← mul_assoc, ENNReal.mul_div_cancel_right hs2 hs2']
    _ < μ s ^ (a / (a - 1)) / (2 : ℝ≥0∞) ^ (1 / 2 : ℝ) := ENNReal.div_lt_div_right hs2 hs2' hQ'
    _ ≤ μ s ^ (a / (a - 1)) / renyiDiv a μ ν := ENNReal.div_le_div_left hD _
    _ ≤ _ := hP

end Transfer

end InformationTheory
