/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import ToMathlib.Probability.Divergence.Renyi
public import ToMathlib.Probability.Divergence.TotalVariation
public import ToMathlib.Probability.ProbabilityMassFunction.RadonNikodym
public import ToMathlib.Probability.ProbabilityMassFunction.Measure
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

universe u

namespace InformationTheory

variable {α : Type u} [MeasurableSpace α] [DiscreteMeasurableSpace α]


/-- **The measure-level Renyi MGF agrees with the `PMF` one, under absolute continuity.**

Absolute continuity is where the two definitions must agree for *every* positive order: without it
they part company below `a = 1`, since an integral against `q` cannot see a point `q` misses while
the sum can. Order `1/2` — the Hellinger affinity — is the case this form exists to serve. -/
theorem renyiMGF_toMeasure_of_ac {a : ℝ} (ha0 : 0 < a) (p q : PMF α)
    (hac : p.toMeasure ≪ q.toMeasure) :
    renyiMGF a p.toMeasure q.toMeasure = PMF.renyiMGF a p q := by
  · have hsupp := (PMF.absolutelyContinuous_toMeasure_iff p q).mp hac
    rw [renyiMGF_of_ac hac]
    have hcongr : ∫⁻ x, (p.toMeasure.rnDeriv q.toMeasure x) ^ a ∂q.toMeasure
        = ∫⁻ x, (p x / q x) ^ a ∂q.toMeasure := by
      refine lintegral_congr_ae ?_
      filter_upwards [PMF.rnDeriv_toMeasure_of_ac p q hac] with x hx
      rw [hx]
    rw [hcongr]
    conv_lhs => rw [← PMF.restrict_toMeasure_support q]
    rw [lintegral_countable _ q.support_countable]
    have hind : (fun x => (p x) ^ a * (q x) ^ (1 - a))
        = q.support.indicator (fun x => (p x) ^ a * (q x) ^ (1 - a)) := by
      funext x
      by_cases hq : x ∈ q.support
      · simp [hq]
      · have hq0 : q x = 0 := by simpa [PMF.mem_support_iff] using hq
        simp [hq, hq0, hsupp x hq0, ENNReal.zero_rpow_of_pos ha0]
    rw [PMF.renyiMGF, hind, ← tsum_subtype]
    refine tsum_congr fun x => ?_
    rw [PMF.toMeasure_apply_singleton _ _ MeasurableSet.of_discrete]
    have hq : q ↑x ≠ 0 := (PMF.mem_support_iff q _).mp x.2
    rw [ENNReal.div_rpow_of_nonneg _ _ ha0.le,
      ENNReal.rpow_sub _ _ hq (PMF.apply_ne_top q x), ENNReal.rpow_one]
    simp only [div_eq_mul_inv]
    ring

/-- **The measure-level Renyi MGF agrees with the `PMF` one.**

Every lemma proved about `renyiMGF` therefore transports to `PMF.renyiMGF`, and conversely. -/
theorem renyiMGF_toMeasure (a : ℝ) (ha : 1 < a) (p q : PMF α) :
    renyiMGF a p.toMeasure q.toMeasure = PMF.renyiMGF a p q := by
  have ha0 : 0 < a := lt_trans one_pos ha
  by_cases hac : p.toMeasure ≪ q.toMeasure
  · exact renyiMGF_toMeasure_of_ac ha0 p q hac
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

/-- The measure-level multiplicative Rényi divergence agrees with the `PMF` definition. -/
theorem renyiDiv_toMeasure (a : ℝ) (ha : 1 < a) (p q : PMF α) :
    renyiDiv a p.toMeasure q.toMeasure = PMF.renyiDiv a p q := by
  rw [renyiDiv_eq_rpow ha, PMF.renyiDiv_eq_rpow ha, renyiMGF_toMeasure a ha]

/-! ### The discrete theory as a corollary

`PMF.renyiMGF_self` is proved directly in
`ToMathlib.Probability.ProbabilityMassFunction.RenyiDivergence`. Here it falls out of the
measure-level statement and `renyiMGF_toMeasure`, with no `tsum` manipulation — which is the
shape every discrete corollary of a measure-level divergence result will take. -/
example (a : ℝ) (ha : 1 < a) (p : PMF α) : PMF.renyiMGF a p p = 1 := by
  rw [← renyiMGF_toMeasure a ha p p, renyiMGF_self]

end InformationTheory

namespace PMF

universe u₀
variable {α' : Type u₀} {β : Type u₀}

/-! ### The data processing inequality for `PMF`

`PMF.renyiMGF_map_le` was proved directly by a fibrewise Holder argument spanning roughly a hundred
and twenty lines. It is now a corollary of `InformationTheory.renyiMGF_map_le`, whose own proof
defers the convexity to Mathlib.

The statements are unchanged, hypotheses included, so every downstream user is unaffected. Note in
particular that no measurable structure appears: the discrete sigma-algebra is introduced inside
the proof with `letI`, which is what lets this reach callers such as `SPMF.renyiDiv_map_le` that
instantiate at `Option α'` for a completely arbitrary carrier. -/

/-- Data processing inequality for the Rényi MGF under deterministic maps:
`M_a(f∗p ‖ f∗q) ≤ M_a(p ‖ q)`.
Applying a deterministic function can only decrease the Rényi MGF. -/
theorem renyiMGF_map_le (a : ℝ) (ha : 1 ≤ a) (f : α' → β) (p q : PMF α') :
    (f <$> p).renyiMGF a (f <$> q) ≤ p.renyiMGF a q := by
  rcases eq_or_lt_of_le ha with rfl | ha
  · simp only [PMF.renyiMGF, sub_self, ENNReal.rpow_zero, mul_one, ENNReal.rpow_one]
    rw [(f <$> p).tsum_coe, p.tsum_coe]
  let _ : MeasurableSpace α' := ⊤
  let _ : MeasurableSpace β := ⊤
  have hf : Measurable f := Measurable.of_discrete
  change PMF.renyiMGF a (PMF.map f p) (PMF.map f q) ≤ PMF.renyiMGF a p q
  rw [← InformationTheory.renyiMGF_toMeasure a ha, ← InformationTheory.renyiMGF_toMeasure a ha,
    ← PMF.toMeasure_map f p hf, ← PMF.toMeasure_map f q hf]
  exact InformationTheory.renyiMGF_map_le a ha _ _ hf

/-- Data processing inequality for the multiplicative Rényi divergence:
`R_a(f∗p ‖ f∗q) ≤ R_a(p ‖ q)`. -/
theorem renyiDiv_map_le (a : ℝ) (ha : 1 < a) (f : α' → β) (p q : PMF α') :
    (f <$> p).renyiDiv a (f <$> q) ≤ p.renyiDiv a q := by
  let _ : MeasurableSpace α' := ⊤
  let _ : MeasurableSpace β := ⊤
  have hf : Measurable f := Measurable.of_discrete
  change PMF.renyiDiv a (PMF.map f p) (PMF.map f q) ≤ PMF.renyiDiv a p q
  rw [← InformationTheory.renyiDiv_toMeasure a ha,
    ← InformationTheory.renyiDiv_toMeasure a ha,
    ← PMF.toMeasure_map f p hf, ← PMF.toMeasure_map f q hf]
  exact InformationTheory.renyiDiv_map_le a ha _ _ hf

/-- Data processing inequality for the Rényi MGF under Markov kernels (post-processing). -/
theorem renyiMGF_bind_right_le (a : ℝ) (ha : 1 ≤ a) (f : α' → PMF β) (p q : PMF α') :
    (p.bind f).renyiMGF a (q.bind f) ≤ p.renyiMGF a q := by
  rcases eq_or_lt_of_le ha with rfl | ha
  · simp only [PMF.renyiMGF, sub_self, ENNReal.rpow_zero, mul_one, ENNReal.rpow_one]
    rw [(p.bind f).tsum_coe, p.tsum_coe]
  let _ : MeasurableSpace α' := ⊤
  let _ : MeasurableSpace β := ⊤
  let κ : ProbabilityTheory.Kernel α' β := ⟨fun x => (f x).toMeasure, Measurable.of_discrete⟩
  have _ : ProbabilityTheory.IsMarkovKernel κ :=
    ⟨fun x => PMF.toMeasure.isProbabilityMeasure (f x)⟩
  rw [← InformationTheory.renyiMGF_toMeasure a ha, ← InformationTheory.renyiMGF_toMeasure a ha,
    PMF.toMeasure_bind, PMF.toMeasure_bind]
  exact InformationTheory.renyiMGF_comp_right_le a ha _ _ κ

/-- Data processing inequality for the multiplicative Rényi divergence under Markov kernels. -/
theorem renyiDiv_bind_right_le (a : ℝ) (ha : 1 < a) (f : α' → PMF β) (p q : PMF α') :
    (p.bind f).renyiDiv a (q.bind f) ≤ p.renyiDiv a q := by
  let _ : MeasurableSpace α' := ⊤
  let _ : MeasurableSpace β := ⊤
  let κ : ProbabilityTheory.Kernel α' β := ⟨fun x => (f x).toMeasure, Measurable.of_discrete⟩
  have _ : ProbabilityTheory.IsMarkovKernel κ :=
    ⟨fun x => PMF.toMeasure.isProbabilityMeasure (f x)⟩
  rw [← InformationTheory.renyiDiv_toMeasure a ha,
    ← InformationTheory.renyiDiv_toMeasure a ha, PMF.toMeasure_bind, PMF.toMeasure_bind]
  exact InformationTheory.renyiDiv_comp_right_le a ha _ _ κ

/-! ### Total variation against the Renyi divergence

`InformationTheory.lintegral_absDiff_div_two_rpow_two_le` is stated for two densities against a
common measure; a `PMF` pair is that situation at the counting measure on the (countable) union of
their supports, so the discrete bound is an instantiation rather than a separate argument. -/

/-- Total variation is controlled by the Bhattacharyya coefficient `M_{1/2}`. -/
theorem etvDist_rpow_two_le_one_sub_renyiMGF_half {α : Type*} (p q : PMF α) :
    p.etvDist q ^ (2:ℝ) ≤ 1 - (PMF.renyiMGF (1/2) p q) ^ (2:ℝ) := by
  classical
  set s : Set α := p.support ∪ q.support with hs
  have hcnt : Countable ↥s := (p.support_countable.union q.support_countable).to_subtype
  let _ : MeasurableSpace ↥s := ⊤
  have htrans : ∀ F : α → ℝ≥0∞, (∀ x, x ∉ s → F x = 0) →
      ∫⁻ x : ↥s, F ↑x ∂(Measure.count : Measure ↥s) = ∑' x, F x := by
    intro F hF
    rw [lintegral_count, tsum_subtype s F, show s.indicator F = F from ?_]
    funext x
    by_cases hx : x ∈ s
    · simp [hx]
    · simp [hx, hF x hx]
  have hp0 : ∀ x, x ∉ s → p x = 0 := fun x hx =>
    (PMF.apply_eq_zero_iff p x).mpr fun h => hx (.inl h)
  have hq0 : ∀ x, x ∉ s → q x = 0 := fun x hx =>
    (PMF.apply_eq_zero_iff q x).mpr fun h => hx (.inr h)
  have key := InformationTheory.lintegral_absDiff_div_two_rpow_two_le
    (Measure.count : Measure ↥s) (f := fun x : ↥s => p ↑x) (g := fun x : ↥s => q ↑x)
    Measurable.of_discrete.aemeasurable Measurable.of_discrete.aemeasurable
    (by rw [htrans _ hp0]; exact p.tsum_coe) (by rw [htrans _ hq0]; exact q.tsum_coe)
  rw [htrans (fun y => ENNReal.absDiff (p y) (q y))
      (fun x hx => by simp [hp0 x hx, hq0 x hx]),
    htrans (fun y => (p y * q y) ^ (1/2:ℝ))
      (fun x hx => by simp [hp0 x hx, hq0 x hx])] at key
  refine le_trans (le_of_eq ?_) (le_trans key (tsub_le_tsub_left (le_of_eq ?_) 1))
  · rfl
  · rw [PMF.renyiMGF]
    refine congrArg (· ^ (2:ℝ)) (tsum_congr fun x => ?_)
    rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]
    norm_num

/-- **Finite-order Renyi divergence bounds TV distance (squared form)**:
`TV(p, q)² ≤ 1 - R_a(p ‖ q)⁻¹`.

The two halves are `InformationTheory.lintegral_absDiff_div_two_rpow_two_le` (Cauchy-Schwarz
against the Hellinger affinity) and `InformationTheory.renyiDiv_inv_le_renyiMGF_half_rpow_two`
(log-convexity of the Renyi MGF, interpolating at `1/2`, `1` and `a`). Both rest on the same
Mathlib inequality, `ENNReal.lintegral_mul_norm_pow_le`. -/
theorem etvDist_sq_le_of_renyiDiv {α : Type*} (a : ℝ) (ha : 1 < a) (p q : PMF α) :
    p.etvDist q ^ (2 : ℝ) ≤ 1 - (p.renyiDiv a q)⁻¹ := by
  let _ : MeasurableSpace α := ⊤
  have ha0 : (0:ℝ) < a := lt_trans one_pos ha
  by_cases hac : p.toMeasure ≪ q.toMeasure
  · refine le_trans (etvDist_rpow_two_le_one_sub_renyiMGF_half p q) (tsub_le_tsub_left ?_ 1)
    have hhalf : PMF.renyiMGF (1/2) p q
        = InformationTheory.renyiMGF (1/2) p.toMeasure q.toMeasure :=
      (InformationTheory.renyiMGF_toMeasure_of_ac (by norm_num) p q hac).symm
    have hdiv : p.renyiDiv a q = InformationTheory.renyiDiv a p.toMeasure q.toMeasure := by
      rw [PMF.renyiDiv_eq_rpow ha, InformationTheory.renyiDiv_eq_rpow ha,
        InformationTheory.renyiMGF_toMeasure a ha]
    rw [hhalf, hdiv]
    exact InformationTheory.renyiDiv_inv_le_renyiMGF_half_rpow_two ha _ _ hac
  · have htop : p.renyiDiv a q = ⊤ := by
      rw [PMF.renyiDiv_eq_rpow ha, ← InformationTheory.renyiMGF_toMeasure a ha,
        InformationTheory.renyiMGF_of_not_ac hac]
      exact ENNReal.top_rpow_of_pos (by simp; linarith)
    rw [htop, ENNReal.inv_top, tsub_zero]
    calc p.etvDist q ^ (2:ℝ) ≤ (1:ℝ≥0∞) ^ (2:ℝ) :=
          ENNReal.rpow_le_rpow (PMF.etvDist_le_one p q) (by norm_num)
      _ = 1 := ENNReal.one_rpow 2

end PMF
