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

universe u v w

namespace MeasureProgramLogic

variable {α γ : Type u} {β δ : Type v}
variable [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ] [MeasurableSpace δ]

/-- Compose a relational state law with measurable conditional couplings. -/
theorem CouplingPost.bind {μ : Measure α} {ν : Measure β}
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
theorem relWP_bind {m₁ : Type u → Type w} {m₂ : Type v → Type w}
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

end MeasureProgramLogic
