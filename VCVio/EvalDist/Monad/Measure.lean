/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module
public import VCVio.EvalDist.Defs.Measure.Core
public import ToMathlib.MeasureTheory.Measure.IndependentDraws
public import ToMathlib.MeasureTheory.Measure.Bounds
import ToMathlib.Probability.UniformOn

/-!
# Measure-valued computation laws

The Giry composition laws transport measure-level independence to computation syntax.
The general interchange theorem requires joint measurability; the three-draw law
specializes to discrete intermediate results and leaves the final result space arbitrary.
Uniform finite draws can be reindexed by a bijection before an arbitrary continuation.
-/

public section

open MeasureTheory ProbabilityTheory Function

universe u v

variable {m : Type u → Type v} [Monad m] [EvalDistSemantics m]
  [LawfulEvalDistSemantics m] {α β γ δ : Type u}
  [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ] [MeasurableSpace δ]

/-- Reindexing a uniform draw by a bijection does not change the measure of any subsequent
computation. The uniformity hypothesis can come from either native sampling or a compatibility
certificate. -/
theorem evalDist_bind_bijective_of_uniform [LawfulMonad m]
    [DiscreteMeasurableSpace α] [MeasurableSingletonClass α] [Finite α] [Nonempty α]
    (mx : m α) (huniform : 𝒟[mx] = uniformOn Set.univ)
    (e : α → α) (he : Function.Bijective e) (f : α → m β) :
    𝒟[mx >>= fun x => f (e x)] = 𝒟[mx >>= f] := by
  have hmap : 𝒟[e <$> mx] = 𝒟[mx] := by
    rw [evalDist_map_of_discrete, huniform]
    exact map_uniformOn_univ_of_bijective Measurable.of_discrete he
  have hprogram : (mx >>= fun x => f (e x)) = (e <$> mx) >>= f := by
    simp [map_eq_bind_pure_comp, bind_assoc]
  rw [hprogram, evalDist_bind_of_discrete, hmap]
  exact (evalDist_bind_of_discrete mx f).symm

/-- Independent computations commute under a jointly measurable denoted continuation. -/
theorem evalDist_bind_bind_swap (mx : m α) (my : m β) (f : α → β → m γ)
    (hf : Measurable fun p : α × β => 𝒟[f p.1 p.2]) :
    𝒟[mx >>= fun a => my >>= fun b => f a b] =
      𝒟[my >>= fun b => mx >>= fun a => f a b] := by
  have hfa (a : α) : Measurable fun b => 𝒟[f a b] :=
    hf.comp (measurable_const.prodMk measurable_id)
  have hfb (b : β) : Measurable fun a => 𝒟[f a b] :=
    hf.comp (measurable_id.prodMk measurable_const)
  have hleft : Measurable fun a => 𝒟[my >>= f a] := by
    simp_rw [evalDist_bind my _ (hfa _)]
    exact Measure.measurable_bind_prod_right 𝒟[my] hf
  have hright : Measurable fun b => 𝒟[mx >>= fun a => f a b] := by
    simp_rw [evalDist_bind mx _ (hfb _)]
    exact Measure.measurable_bind_prod_right 𝒟[mx] (hf.comp measurable_swap)
  rw [evalDist_bind mx _ hleft, evalDist_bind my _ hright]
  simp_rw [evalDist_bind my _ (hfa _), evalDist_bind mx _ (hfb _)]
  exact Measure.bind_bind_swap _ _ hf

/-- Move the third independent discrete draw to the front of a computation. -/
theorem evalDist_bind_bind_bind_rotate [DiscreteMeasurableSpace α]
    [DiscreteMeasurableSpace β] [DiscreteMeasurableSpace γ]
    (mx : m α) (my : m β) (mz : m γ) (f : α → β → γ → m δ)
    (hf : Measurable fun p : α × β × γ => 𝒟[f p.1 p.2.1 p.2.2]) :
    𝒟[mx >>= fun a => my >>= fun b => mz >>= fun c => f a b c] =
      𝒟[mz >>= fun c => mx >>= fun a => my >>= fun b => f a b c] := by
  simp only [evalDist_bind_of_discrete]
  exact Measure.bind_bind_bind_rotate _ _ _ hf

/-- Compare event masses after a common draw using an almost-everywhere continuation bound. -/
theorem evalDist_bind_apply_mono (mx : m α) (f g : α → m β)
    (hf : Measurable fun a => 𝒟[f a]) (hg : Measurable fun a => 𝒟[g a])
    {event : Set β} (hevent : MeasurableSet event)
    (hfg : ∀ᵐ a ∂𝒟[mx], 𝒟[f a] event ≤ 𝒟[g a] event) :
    𝒟[mx >>= f] event ≤ 𝒟[mx >>= g] event := by
  rw [evalDist_bind mx f hf, evalDist_bind mx g hg]
  exact Measure.bind_apply_mono _ _ _ hf hg hevent hfg

/-- For a discrete common draw, a pointwise continuation bound suffices. -/
theorem evalDist_bind_apply_mono_of_discrete [DiscreteMeasurableSpace α]
    (mx : m α) (f g : α → m β) {event : Set β} (hevent : MeasurableSet event)
    (hfg : ∀ a, 𝒟[f a] event ≤ 𝒟[g a] event) :
    𝒟[mx >>= f] event ≤ 𝒟[mx >>= g] event :=
  evalDist_bind_apply_mono mx f g .of_discrete .of_discrete hevent
    (Filter.Eventually.of_forall hfg)

/-- Charge a bad intermediate event separately from uniformly bounded good continuations. -/
theorem evalDist_bind_apply_le_add_of_bad (mx : m α) (f : α → m β)
    (hf : Measurable fun a => 𝒟[f a]) {bad : Set α} (hbad : MeasurableSet bad)
    {event : Set β} (hevent : MeasurableSet event) {ε₁ ε₂ : ENNReal}
    (hbadBound : 𝒟[mx] bad ≤ ε₁) (hgood : ∀ a, a ∉ bad → 𝒟[f a] event ≤ ε₂) :
    𝒟[mx >>= f] event ≤ ε₁ + ε₂ := by
  rw [evalDist_bind mx f hf]
  exact Measure.bind_apply_le_add_of_bad _ _ hf hbad hevent hbadBound hgood

/-- Charge a bad intermediate event and integrate an almost-everywhere continuation bound. -/
theorem evalDist_bind_apply_le_add_lintegral_of_bad (mx : m α) (f : α → m β)
    (hf : Measurable fun a => 𝒟[f a]) {bad : Set α} (hbad : MeasurableSet bad)
    {event : Set β} (hevent : MeasurableSet event) (bound : α → ENNReal) {ε : ENNReal}
    (hgood : ∀ᵐ a ∂𝒟[mx], a ∉ bad → 𝒟[f a] event ≤ bound a + ε) :
    𝒟[mx >>= f] event ≤ 𝒟[mx] bad + ε + ∫⁻ a, bound a ∂𝒟[mx] := by
  rw [evalDist_bind mx f hf]
  exact Measure.bind_apply_le_add_lintegral_of_bad _ _ hf hbad hevent hgood

/-- Compare two denoted continuations outside a measurable disagreement set. -/
theorem evalDist_bind_apply_le_add_of_disagree (mx : m α) (f g : α → m β)
    (hf : Measurable fun a => 𝒟[f a]) (hg : Measurable fun a => 𝒟[g a])
    {bad : Set α} (hbad : MeasurableSet bad)
    {event : Set β} (hevent : MeasurableSet event) {ε : ENNReal}
    (hgood : ∀ᵐ a ∂𝒟[mx], a ∉ bad → 𝒟[f a] event ≤ 𝒟[g a] event + ε) :
    𝒟[mx >>= f] event ≤ 𝒟[mx >>= g] event + 𝒟[mx] bad + ε := by
  rw [evalDist_bind mx f hf, evalDist_bind mx g hg]
  exact Measure.bind_apply_le_add_of_disagree _ _ _ hf hg hbad hevent hgood
