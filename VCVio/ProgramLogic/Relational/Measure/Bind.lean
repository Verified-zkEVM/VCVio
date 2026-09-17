/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module
public import VCVio.ProgramLogic.Relational.Measure
public import ToMathlib.MeasureTheory.Measure.Coupling.Bind

/-!
# Sequential rules for measure-valued relational logic

An initial relational judgment and a measurable conditional joint family compose by Giry bind.
The family is explicit data, so the rule does not silently assume a measurable choice from
pointwise existential coupling witnesses. Initial states may themselves have arbitrary laws.
-/

public section

open MeasureTheory

universe u v w₁ w₂ x y

namespace MeasureProgramLogic

variable {α γ : Type u} {β δ : Type v}
variable [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ] [MeasurableSpace δ]

/-- Compose a relational state law with measurable conditional couplings. -/
theorem CouplingPost.bind {γ : Type x} {δ : Type y}
    [MeasurableSpace γ] [MeasurableSpace δ] {μ : Measure α} {ν : Measure β}
    {R : α → β → Prop} {S : γ → δ → Prop} (hinit : CouplingPost μ ν R)
    {k : α → Measure γ} {l : β → Measure δ} {j : α × β → Measure (γ × δ)}
    (hk : Measurable k) (hl : Measurable l) (hj : Measurable j)
    (hS : MeasurableSet {z : γ × δ | S z.1 z.2})
    (hstep : ∀ z, R z.1 z.2 →
      Measure.IsCoupling (j z) (k z.1) (l z.2) ∧ ∀ᵐ out ∂j z, S out.1 out.2) :
    CouplingPost (μ.bind k) (ν.bind l) S := by
  obtain ⟨c, hc⟩ := hinit
  have hm := hc.mono fun z hz => (hstep z hz).1
  refine ⟨c.bind hk hl hj hm, ?_⟩
  change ∀ᵐ z ∂(c.bind hk hl hj hm).joint, S z.1 z.2
  rw [Measure.Coupling.bind_joint]
  exact Measure.ae_bind_of_ae hj hS (hc.mono fun z hz => (hstep z hz).2)

/-- The sequential relational rule for any two monads with lawful measure semantics. -/
theorem relWP_bind {m₁ : Type u → Type w₁} {m₂ : Type v → Type w₂}
    [Monad m₁] [Monad m₂] [EvalDistSemantics m₁] [EvalDistSemantics m₂]
    [LawfulEvalDistSemantics m₁] [LawfulEvalDistSemantics m₂]
    {mx : m₁ α} {my : m₂ β} {R : α → β → Prop} {S : γ → δ → Prop}
    (hinit : RelWP mx my R) (f : α → m₁ γ) (g : β → m₂ δ)
    (hf : Measurable fun a => 𝒟[f a]) (hg : Measurable fun b => 𝒟[g b])
    {j : α × β → Measure (γ × δ)} (hj : Measurable j)
    (hS : MeasurableSet {z : γ × δ | S z.1 z.2})
    (hstep : ∀ z, R z.1 z.2 →
      Measure.IsCoupling (j z) 𝒟[f z.1] 𝒟[g z.2] ∧ ∀ᵐ out ∂j z, S out.1 out.2) :
    RelWP (mx >>= f) (my >>= g) S := by
  rw [RelWP, evalDist_bind mx f hf, evalDist_bind my g hg]
  exact hinit.bind hf hg hj hS hstep

/-- Sequential relational composition with a chosen initial witness only needs a conditional
joint family measurable under that witness. Countable concentration sets discharge this
obligation without assuming a discrete product measurable space. -/
theorem relWP_bind_of_aemeasurable {m₁ : Type u → Type w₁} {m₂ : Type v → Type w₂}
    [Monad m₁] [Monad m₂] [EvalDistSemantics m₁] [EvalDistSemantics m₂]
    [LawfulEvalDistSemantics m₁] [LawfulEvalDistSemantics m₂]
    (mx : m₁ α) (my : m₂ β) (c : Measure.Coupling 𝒟[mx] 𝒟[my])
    (f : α → m₁ γ) (g : β → m₂ δ)
    (hf : Measurable fun a ↦ 𝒟[f a]) (hg : Measurable fun b ↦ 𝒟[g b])
    {j : α × β → Measure (γ × δ)} (hj : AEMeasurable j c.1)
    {S : γ → δ → Prop} (hS : MeasurableSet {z : γ × δ | S z.1 z.2})
    (hstep : ∀ᵐ z ∂c.1,
      Measure.IsCoupling (j z) 𝒟[f z.1] 𝒟[g z.2] ∧ ∀ᵐ out ∂j z, S out.1 out.2) :
    RelWP (mx >>= f) (my >>= g) S := by
  rw [RelWP, evalDist_bind mx f hf, evalDist_bind my g hg]
  exact ⟨⟨c.1.bind j, c.2.bind_of_aemeasurable hf hg hj
    (hstep.mono fun _ h ↦ h.1)⟩,
    Measure.ae_bind_of_ae_of_aemeasurable hj hS (hstep.mono fun _ h ↦ h.2)⟩

/-- On countable concentration sets, pointwise conditional coupling witnesses suffice for bind.
The choice is made only on a countable set and extended by zero, so it is almost everywhere
measurable under the initial joint law. -/
theorem CouplingPost.bind_of_countable {γ : Type x} {δ : Type y}
    [MeasurableSpace γ] [MeasurableSpace δ] [MeasurableSingletonClass α]
    [MeasurableSingletonClass β] {μ : Measure α} {ν : Measure β}
    {R : α → β → Prop} {S : γ → δ → Prop} (hinit : CouplingPost μ ν R)
    {s : Set α} {t : Set β} (hs : s.Countable) (ht : t.Countable)
    (hμ : ∀ᵐ a ∂μ, a ∈ s) (hν : ∀ᵐ b ∂ν, b ∈ t)
    {k : α → Measure γ} {l : β → Measure δ} (hk : Measurable k) (hl : Measurable l)
    (hS : MeasurableSet {z : γ × δ | S z.1 z.2})
    (hstep : ∀ a ∈ s, ∀ b ∈ t, R a b → CouplingPost (k a) (l b) S) :
    CouplingPost (μ.bind k) (ν.bind l) S := by
  classical
  obtain ⟨c, hc⟩ := hinit
  let domain : Set (α × β) := (s ×ˢ t) ∩ {z | R z.1 z.2}
  have hcount : domain.Countable := (hs.prod ht).mono Set.inter_subset_left
  have hdomain : ∀ᵐ z ∂c.1, z ∈ domain :=
    (c.2.ae_mem_prod hs.measurableSet ht.measurableSet hμ hν).and hc
  have hconditional (z : α × β) (hz : z ∈ domain) : CouplingPost (k z.1) (l z.2) S :=
    hstep z.1 hz.1.1 z.2 hz.1.2 hz.2
  let j : α × β → Measure (γ × δ) := fun z ↦
    if hz : z ∈ domain then (hconditional z hz).choose.1 else 0
  have hj : AEMeasurable j c.1 := aemeasurable_of_ae_mem_countable hcount hdomain j
  have hcontract : ∀ᵐ z ∂c.1,
      Measure.IsCoupling (j z) (k z.1) (l z.2) ∧ ∀ᵐ out ∂j z, S out.1 out.2 := by
    filter_upwards [hdomain] with z hz
    simpa only [j, dite_eq_left hz] using
      And.intro (hconditional z hz).choose.2 (hconditional z hz).choose_spec
  exact ⟨⟨c.1.bind j, c.2.bind_of_aemeasurable hk hl hj
    (hcontract.mono fun _ h ↦ h.1)⟩,
    Measure.ae_bind_of_ae_of_aemeasurable hj hS (hcontract.mono fun _ h ↦ h.2)⟩

/-- Countable marginal concentration also permits arbitrary final relations: intersect the
relation with its countable concentration set before applying measurable bind composition. -/
theorem CouplingPost.bind_of_countable_of_ae_mem {γ : Type x} {δ : Type y}
    [MeasurableSpace γ] [MeasurableSpace δ]
    [MeasurableSingletonClass α] [MeasurableSingletonClass β]
    [MeasurableSingletonClass γ] [MeasurableSingletonClass δ]
    {μ : Measure α} {ν : Measure β} {R : α → β → Prop} {S : γ → δ → Prop}
    (hinit : CouplingPost μ ν R)
    {s : Set α} {t : Set β} {p : Set γ} {q : Set δ}
    (hs : s.Countable) (ht : t.Countable) (hp : p.Countable) (hq : q.Countable)
    (hμ : ∀ᵐ a ∂μ, a ∈ s) (hν : ∀ᵐ b ∂ν, b ∈ t)
    {k : α → Measure γ} {l : β → Measure δ}
    (hk : Measurable k) (hl : Measurable l)
    (hkp : ∀ a ∈ s, ∀ᵐ x ∂k a, x ∈ p) (hlq : ∀ b ∈ t, ∀ᵐ y ∂l b, y ∈ q)
    (hstep : ∀ a ∈ s, ∀ b ∈ t, R a b → CouplingPost (k a) (l b) S) :
    CouplingPost (μ.bind k) (ν.bind l) S := by
  have hpost : MeasurableSet {z : γ × δ | (z.1 ∈ p ∧ z.2 ∈ q) ∧ S z.1 z.2} :=
    ((hp.prod hq).mono fun _ hz ↦ hz.1).measurableSet
  have hstep' : ∀ a ∈ s, ∀ b ∈ t, R a b →
      CouplingPost (k a) (l b) (fun x y ↦ (x ∈ p ∧ y ∈ q) ∧ S x y) := by
    intro a ha b hb hR
    obtain ⟨c, hc⟩ := hstep a ha b hb hR
    exact ⟨c, (c.2.ae_mem_prod hp.measurableSet hq.measurableSet
      (hkp a ha) (hlq b hb)).and hc⟩
  exact (hinit.bind_of_countable hs ht hμ hν hk hl hpost hstep').mono
    fun _ _ h ↦ h.2


/-- Quantitative bind obtains a lower bound from any almost everywhere measurable family of
conditional couplings. No maximum or measurable choice of optimizers is assumed. -/
theorem lintegral_le_eRelWP_bind {m₁ : Type u → Type w₁} {m₂ : Type v → Type w₂}
    [Monad m₁] [Monad m₂] [EvalDistSemantics m₁] [EvalDistSemantics m₂]
    [LawfulEvalDistSemantics m₁] [LawfulEvalDistSemantics m₂]
    (mx : m₁ α) (my : m₂ β) (c : Measure.Coupling 𝒟[mx] 𝒟[my])
    (f : α → m₁ γ) (g : β → m₂ δ)
    (hf : Measurable fun a ↦ 𝒟[f a]) (hg : Measurable fun b ↦ 𝒟[g b])
    {j : α × β → Measure (γ × δ)} (hj : AEMeasurable j c.1)
    (hstep : ∀ᵐ z ∂c.1, Measure.IsCoupling (j z) 𝒟[f z.1] 𝒟[g z.2])
    (post : γ → δ → ENNReal) (hpost : Measurable fun z : γ × δ ↦ post z.1 z.2) :
    (∫⁻ z, ∫⁻ out, post out.1 out.2 ∂j z ∂c.1) ≤
      eRelWP (mx >>= f) (my >>= g) post := by
  rw [eRelWP, evalDist_bind mx f hf, evalDist_bind my g hg]
  have h := le_iSup
    (fun joint : Measure.Coupling (𝒟[mx].bind fun a ↦ 𝒟[f a])
        (𝒟[my].bind fun b ↦ 𝒟[g b]) ↦ ∫⁻ out, post out.1 out.2 ∂joint.1)
    ⟨c.1.bind j, c.2.bind_of_aemeasurable hf hg hj hstep⟩
  simpa only [Measure.lintegral_bind hj hpost.aemeasurable] using h

end MeasureProgramLogic
