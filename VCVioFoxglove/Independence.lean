/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import VCVioFoxglove.Specs
public import Foxglove.Rules.Independence

/-!
# Independence in VCVio's terms

Foxglove states that a pair-valued program's components are independent with laws `μ` and `ν`
as `⊢ wp oa ⦃X, (Prod.fst ∘ X) ~ μ ∗ (Prod.snd ∘ X) ~ ν⦄`, and builds such statements
compositionally (`wp_bind_pair_sep`, `wp_bind_sep_bind`). Adequacy reads them in VCVio:

* `evalDist_eq_product_of_wp_sep`: the output measure is the product law;
* `prEvent_and_of_wp_sep`: events of the two components multiply;
* `prEvent_eq_of_wp_sep_uniform`: a uniform component is matched by an independent guess with
  probability `1 / |β|`.
-/

@[expose] public section

namespace Foxglove

open Interp OracleSpec OracleComp
open scoped ENNReal

noncomputable section

variable {ι β γ : Type} {oSpec : OracleSpec ι} [BernoulliImpl oSpec] [oSpec.AnswerMeasure]
  [LawfulBernoulliImpl oSpec] [Inhabited β] [Inhabited γ] [Countable β] [Countable γ]
  {oa : OracleComp oSpec (β × γ)} {μ : PMF β} {ν : PMF γ}

/-- **Independent components have the product output measure.** -/
theorem evalDist_eq_product_of_wp_sep [MeasurableSpace (β × γ)]
    [MeasurableSingletonClass (β × γ)]
    (h : ⊢ wp oa ⦃X, (Prod.fst ∘ X) ~ μ ∗ (Prod.snd ∘ X) ~ ν⦄) : 𝒟[oa] = (μ ⊗ ν).toMeasure :=
  evalDist_eq_toMeasure_of_wp (wp_law_product_of_sep h)

/-- The probability of an event of a program with law `ρ` is `ρ`'s mass on it. -/
private lemma prEvent_eq_toMeasureWithMs {α : Type} [Inhabited α] [Countable α]
    {ob : OracleComp oSpec α} {ρ : PMF α} (h : ⊢ wp ob ⦃X, X ~ ρ⦄) (p : α → Prop) :
    Pr{let x ← ob}[p x] = ρ.toMeasureWithMs ⊤ {x | p x} := by
  let : MeasurableSpace α := ⊤
  rw [prEvent_eq_evalDist_of_discrete, evalDist_eq_toMeasure_of_wp h]
  rfl

private lemma toMeasureWithMs_univ {α : Type} (ρ : PMF α) : ρ.toMeasureWithMs ⊤ Set.univ = 1 := by
  let : MeasurableSpace α := ⊤
  exact MeasureTheory.measure_univ (μ := ρ.toMeasure)

/-- **Events of independent components multiply.** -/
theorem prEvent_and_of_wp_sep (h : ⊢ wp oa ⦃X, (Prod.fst ∘ X) ~ μ ∗ (Prod.snd ∘ X) ~ ν⦄)
    (p : β → Prop) (q : γ → Prop) :
    Pr{let x ← oa}[p x.1 ∧ q x.2] = Pr{let x ← oa}[p x.1] * Pr{let x ← oa}[q x.2] := by
  have hρ := wp_law_product_of_sep h
  rw [prEvent_eq_toMeasureWithMs hρ, prEvent_eq_toMeasureWithMs hρ,
    prEvent_eq_toMeasureWithMs hρ,
    show {x : β × γ | p x.1 ∧ q x.2} = {b | p b} ×ˢ {c | q c} from rfl,
    show {x : β × γ | p x.1} = {b | p b} ×ˢ Set.univ by ext; simp,
    show {x : β × γ | q x.2} = Set.univ ×ˢ {c | q c} by ext; simp,
    product_toMeasure_prod, product_toMeasure_prod, product_toMeasure_prod,
    toMeasureWithMs_univ, toMeasureWithMs_univ, mul_one, one_mul]

/-- **An independent guess of a uniform value is right with probability `1 / |β|`.** -/
theorem prEvent_eq_of_wp_sep_uniform [Fintype β] {oa : OracleComp oSpec (β × β)} {ν : PMF β}
    (h : ⊢ wp oa ⦃X, (Prod.fst ∘ X) ~ PMF.uniformOfFintype' β ∗ (Prod.snd ∘ X) ~ ν⦄) :
    Pr{let x ← oa}[x.1 = x.2] = (Fintype.card β : ℝ≥0∞)⁻¹ := by
  classical
  let : MeasurableSpace (β × β) := ⊤
  rw [prEvent_eq_toMeasureWithMs (wp_law_product_of_sep h), PMF.toMeasureWithMs,
    PMF.toMeasure_apply _ MeasurableSpace.measurableSet_top, ENNReal.tsum_prod']
  simp only [Set.indicator_apply, Set.mem_ofPred_eq, product_apply, PMF.uniformOfFintype'_apply]
  rw [tsum_congr fun b ↦ (tsum_eq_single b fun c hc ↦ ite_eq_right (Ne.symm hc)).trans
    (ite_eq_left rfl), ENNReal.tsum_mul_left, PMF.tsum_coe, mul_one]

omit [Countable β] in
/-- **A sample and a sampler whose output measure does not depend on it are independent**,
the second with its own tape law. -/
theorem wp_bind_pair_sep_of_evalDist_eq [MeasurableSpace γ] [MeasurableSingletonClass γ]
    {C : OracleComp oSpec β} {F : β → OracleComp oSpec γ} (hC : ⊢ wp C ⦃X, X ~ μ⦄)
    (hF : ∀ b, 𝒟[F b] = 𝒟[F default]) :
    ⊢ wp (C >>= fun b ↦ F b >>= fun c ↦ pure (b, c)) ⦃Z, (Prod.fst ∘ Z) ~ μ ∗
      (Prod.snd ∘ Z) ~ lawPMF (BernoulliInterpretable.interp (F default))⦄ :=
  wp_bind_pair_sep hC fun b ↦ wp_of_evalDist_eq (hF b) (wp_lawPMF _)

omit [BernoulliImpl oSpec] [LawfulBernoulliImpl oSpec] in
/-- **A decided event of two draws is an event of the pair of draws**: the shape in which the
independence lemmas apply. -/
theorem evalDist_decide_bind_bind {α δ : Type} (A : OracleComp oSpec α)
    (B : α → OracleComp oSpec δ) (p : α → δ → Prop) [∀ a d, Decidable (p a d)] :
    𝒟[do let a ← A; let d ← B a; return decide (p a d)] {true}
      = Pr{let x ← (do let a ← A; let d ← B a; pure (a, d))}[p x.1 x.2] := by
  rw [prEvent_eq_evalDist_decide]
  simp only [bind_assoc, pure_bind]

end

end Foxglove
