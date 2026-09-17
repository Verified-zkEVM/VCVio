/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module
public import ToMathlib.MeasureTheory.Measure.Coupling
public import ToMathlib.MeasureTheory.Measure.GiryMonad
public import ToMathlib.MeasureTheory.Measure.Monotone
public import ToMathlib.MeasureTheory.Function.AEMeasurable

/-!
# Sequential composition of measure couplings

A measurable family of joint measures composes with an initial coupling by Giry bind.
Marginal and postcondition obligations need only hold almost everywhere under the initial joint
law. The family is supplied as data: no measurable choice of pointwise coupling witnesses is
assumed. These laws apply to arbitrary measurable spaces and arbitrary measure mass.
-/

public section

open MeasureTheory

universe u v w x

namespace MeasureTheory.Measure

variable {α : Type u} {β : Type v} {γ : Type w} {δ : Type x}
variable [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ] [MeasurableSpace δ]

/-- Bind is additive in its initial measure. -/
theorem bind_add_left (μ ν : Measure α) {k : α → Measure β} (hk : Measurable k) :
    (μ + ν).bind k = μ.bind k + ν.bind k := by
  ext s hs
  simp only [bind_apply hs hk.aemeasurable, add_apply, lintegral_add_measure]

/-- Bind is additive in a measurable continuation. -/
theorem bind_add_right (μ : Measure α) {k l : α → Measure β}
    (hk : Measurable k) (hl : Measurable l) :
    μ.bind (fun a => k a + l a) = μ.bind k + μ.bind l := by
  ext s hs
  rw [bind_apply hs (show Measurable (fun a => k a + l a) from hk.add hl).aemeasurable,
    add_apply, bind_apply hs hk.aemeasurable, bind_apply hs hl.aemeasurable]
  simp only [add_apply]
  exact lintegral_add_left ((measurable_coe hs).comp hk) _

/-- Bind is monotone in its initial measure. -/
theorem bind_mono_left {μ ν : Measure α} (h : μ ≤ ν) {k : α → Measure β}
    (hk : Measurable k) : μ.bind k ≤ ν.bind k := by
  refine Measure.le_iff.2 fun s hs => ?_
  simp only [bind_apply hs hk.aemeasurable]
  exact lintegral_mono' h le_rfl

/-- An almost-everywhere postcondition is preserved by a measurable bind. -/
theorem ae_bind_of_ae {μ : Measure α} {k : α → Measure β} {p : β → Prop}
    (hk : Measurable k) (hp : MeasurableSet {b | p b})
    (h : ∀ᵐ a ∂μ, ∀ᵐ b ∂k a, p b) : ∀ᵐ b ∂μ.bind k, p b := by
  change (μ.bind k) {b | p b}ᶜ = 0
  rw [bind_apply hp.compl hk.aemeasurable]
  exact (lintegral_eq_zero_iff (measurable_coe hp.compl |>.comp hk)).2
    (h.mono fun _ ha => ha)

/-- Sequential composition couples the bound marginals. Conditional marginal identities are
required only for pairs reached by the initial coupling. -/
theorem IsCoupling.bind {c : Measure (α × β)} {μ : Measure α} {ν : Measure β}
    (hc : IsCoupling c μ ν) {k : α → Measure γ} {l : β → Measure δ}
    {j : α × β → Measure (γ × δ)} (hk : Measurable k) (hl : Measurable l)
    (hj : Measurable j) (h : ∀ᵐ z ∂c, IsCoupling (j z) (k z.1) (l z.2)) :
    IsCoupling (c.bind j) (μ.bind k) (ν.bind l) := by
  constructor
  · rw [Measure.fst, map_bind c hj measurable_fst]
    change c.bind (fun z => (j z).fst) = _
    rw [bind_congr_right (h.mono fun _ hz => hz.fst_eq)]
    rw [← bind_map c measurable_fst hk]
    exact congrArg (fun μ => μ.bind k) hc.fst_eq
  · rw [Measure.snd, map_bind c hj measurable_snd]
    change c.bind (fun z => (j z).snd) = _
    rw [bind_congr_right (h.mono fun _ hz => hz.snd_eq)]
    rw [← bind_map c measurable_snd hl]
    exact congrArg (fun ν => ν.bind l) hc.snd_eq

/-- Conditional joint families need only be measurable under the initial joint law. -/
theorem IsCoupling.bind_of_aemeasurable {c : Measure (α × β)} {μ : Measure α} {ν : Measure β}
    (hc : IsCoupling c μ ν) {k : α → Measure γ} {l : β → Measure δ}
    {j : α × β → Measure (γ × δ)} (hk : Measurable k) (hl : Measurable l)
    (hj : AEMeasurable j c) (h : ∀ᵐ z ∂c, IsCoupling (j z) (k z.1) (l z.2)) :
    IsCoupling (c.bind j) (μ.bind k) (ν.bind l) := by
  rw [bind_congr_right hj.ae_eq_mk]
  apply hc.bind hk hl hj.measurable_mk
  filter_upwards [h, hj.ae_eq_mk] with z hz heq
  rw [← heq]
  exact hz

/-- Almost everywhere measurable bind preserves measurable almost everywhere postconditions. -/
theorem ae_bind_of_ae_of_aemeasurable {μ : Measure α} {k : α → Measure β} {p : β → Prop}
    (hk : AEMeasurable k μ) (hp : MeasurableSet {b | p b})
    (h : ∀ᵐ a ∂μ, ∀ᵐ b ∂k a, p b) : ∀ᵐ b ∂μ.bind k, p b := by
  rw [bind_congr_right hk.ae_eq_mk]
  apply ae_bind_of_ae hk.measurable_mk hp
  filter_upwards [h, hk.ae_eq_mk] with a ha heq
  rw [← heq]
  exact ha

/-- Bind a coupling with a measurable conditional coupling family. -/
noncomputable def Coupling.bind {μ : Measure α} {ν : Measure β}
    (c : Coupling μ ν) {k : α → Measure γ} {l : β → Measure δ}
    {j : α × β → Measure (γ × δ)} (hk : Measurable k) (hl : Measurable l)
    (hj : Measurable j) (h : ∀ᵐ z ∂c.joint, IsCoupling (j z) (k z.1) (l z.2)) :
    Coupling (μ.bind k) (ν.bind l) :=
  ⟨c.joint.bind j, c.isCoupling.bind hk hl hj h⟩

/-- The joint measure of sequentially composed couplings is their Giry bind. -/
@[simp]
theorem Coupling.bind_joint {μ : Measure α} {ν : Measure β}
    (c : Coupling μ ν) {k : α → Measure γ} {l : β → Measure δ}
    {j : α × β → Measure (γ × δ)} (hk : Measurable k) (hl : Measurable l)
    (hj : Measurable j) (h : ∀ᵐ z ∂c.joint, IsCoupling (j z) (k z.1) (l z.2)) :
    (c.bind hk hl hj h).joint = c.joint.bind j := by
  rfl

end MeasureTheory.Measure
