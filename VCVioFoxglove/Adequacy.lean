/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import VCVioFoxglove.Interp
public import Foxglove.Rules.Derived

/-!
# Foxglove laws are VCVio's distributions

For a lawfully implemented `OracleComp` program, a law in Foxglove is exactly VCVio's output
distribution, in both directions:

* `wp_of_evalDist`: VCVio's distribution is a Foxglove law (`WP_SAMP` at `lawOf_interp`);
* `evalDist_of_wp`: a Foxglove law is VCVio's distribution (Foxglove's adequacy,
  `lawPMF_eq_of_wp`);
* `wp_hasDistribution_iff` and its measure and event-notation forms state both at once;
* `exists_evalDist_of_wp`, `exists_prEvent_of_wp`: the same for law descriptions
  `⦃X, ∃ μ, ⌜P μ⌝ ∗ X ~ μ⦄`, the shape worked examples state results in.

`MeasureTheory` is not opened here: it breaks iris-lean's `⌜_⌝` and `∗` notation.
-/

@[expose] public section

namespace Foxglove

open Interp

noncomputable section

variable {ι α : Type} {oSpec : OracleSpec ι} [BernoulliImpl oSpec] [oSpec.AnswerMeasure]
  [LawfulBernoulliImpl oSpec] [Inhabited α] [Countable α] [MeasurableSpace α]
  [MeasurableSingletonClass α] {oa : OracleComp oSpec α} {ν : PMF α}

/-! ## From VCVio to Foxglove -/

/-- **VCVio's distribution is a Foxglove law.** -/
theorem wp_of_evalDist (h : ∀ a, 𝒟[oa] {a} = ν a) : ⊢ wp oa ⦃X, X ~ ν⦄ :=
  Proofs.WP_SAMP (BernoulliInterpretable.interp oa) ν fun a ↦ (lawOf_interp oa a).trans (h a)

/-- `wp_of_evalDist`, from an equation of measures. -/
theorem wp_of_evalDist_eq_toMeasure (h : 𝒟[oa] = ν.toMeasure) : ⊢ wp oa ⦃X, X ~ ν⦄ :=
  wp_of_evalDist fun a ↦ by rw [h, PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton a)]

omit [MeasurableSpace α] [MeasurableSingletonClass α] in
/-- `wp_of_evalDist`, in VCVio's event notation. -/
theorem wp_of_prEvent (h : ∀ a, Pr{let x ← oa}[x = a] = ν a) : ⊢ wp oa ⦃X, X ~ ν⦄ :=
  Proofs.WP_SAMP (BernoulliInterpretable.interp oa) ν fun a ↦
    (lawOf_interp_eq_prEvent oa a).trans (h a)

/-! ## From Foxglove to VCVio -/

/-- **A Foxglove law is VCVio's distribution.** -/
theorem evalDist_of_wp (h : ⊢ wp oa ⦃X, X ~ ν⦄) (a : α) : 𝒟[oa] {a} = ν a :=
  (lawOf_interp oa a).symm.trans (lawOf_of_wp h a)

/-- `evalDist_of_wp`, as an equation of measures. -/
theorem evalDist_eq_toMeasure_of_wp (h : ⊢ wp oa ⦃X, X ~ ν⦄) : 𝒟[oa] = ν.toMeasure := by
  rw [← lawPMF_eq_of_wp h, toMeasure_lawPMF_interp]

omit [MeasurableSpace α] [MeasurableSingletonClass α] in
/-- `evalDist_of_wp`, in VCVio's event notation. -/
theorem prEvent_of_wp (h : ⊢ wp oa ⦃X, X ~ ν⦄) (a : α) : Pr{let x ← oa}[x = a] = ν a :=
  (lawOf_interp_eq_prEvent oa a).symm.trans (lawOf_of_wp h a)

/-- **A Foxglove law description holds of VCVio's distribution.** -/
theorem exists_evalDist_of_wp {P : PMF α → Prop} (h : ⊢ wp oa ⦃X, ∃ μ : PMF α, ⌜P μ⌝ ∗ X ~ μ⦄) :
    ∃ ν : PMF α, P ν ∧ ∀ a, 𝒟[oa] {a} = ν a :=
  ⟨_, lawPMF_of_wp h, fun a ↦ by rw [lawPMF_apply, lawOf_interp]⟩

omit [MeasurableSpace α] [MeasurableSingletonClass α] in
/-- `exists_evalDist_of_wp`, in VCVio's event notation. -/
theorem exists_prEvent_of_wp {P : PMF α → Prop} (h : ⊢ wp oa ⦃X, ∃ μ : PMF α, ⌜P μ⌝ ∗ X ~ μ⦄) :
    ∃ ν : PMF α, P ν ∧ ∀ a, Pr{let x ← oa}[x = a] = ν a :=
  ⟨_, lawPMF_of_wp h, fun a ↦ by rw [lawPMF_apply, lawOf_interp_eq_prEvent]⟩

/-! ## Both directions -/

/-- **A program has law `ν` in Foxglove exactly when VCVio gives it the distribution `ν`.** -/
theorem wp_hasDistribution_iff : (⊢ wp oa ⦃X, X ~ ν⦄) ↔ ∀ a, 𝒟[oa] {a} = ν a :=
  ⟨evalDist_of_wp, wp_of_evalDist⟩

/-- `wp_hasDistribution_iff`, as an equation of measures. -/
theorem wp_hasDistribution_iff_evalDist_eq_toMeasure :
    (⊢ wp oa ⦃X, X ~ ν⦄) ↔ 𝒟[oa] = ν.toMeasure :=
  ⟨evalDist_eq_toMeasure_of_wp, wp_of_evalDist_eq_toMeasure⟩

omit [MeasurableSpace α] [MeasurableSingletonClass α] in
/-- `wp_hasDistribution_iff`, in VCVio's event notation. -/
theorem wp_hasDistribution_iff_prEvent :
    (⊢ wp oa ⦃X, X ~ ν⦄) ↔ ∀ a, Pr{let x ← oa}[x = a] = ν a :=
  ⟨prEvent_of_wp, wp_of_prEvent⟩

end

end Foxglove
