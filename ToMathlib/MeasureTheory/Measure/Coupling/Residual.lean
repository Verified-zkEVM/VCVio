/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module
public import ToMathlib.MeasureTheory.Measure.Coupling.Bind

/-!
# Subcouplings with explicit unmatched mass

The first marginal together with a residual measure is the complete left law; the second
marginal is dominated by the right law. Sequential composition propagates the initial residual
through the left transition and adds the conditional residuals under the joint law. Thus loss
is accounted for without assuming equal success probabilities or subtracting infinite measures.
-/

public section

open MeasureTheory

namespace MeasureTheory.Measure

variable {α β γ δ : Type*}
variable [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ] [MeasurableSpace δ]

/-- A joint measure matches all of the left law except the specified residual. -/
structure IsSubcouplingWithResidual (c : Measure (α × β)) (residual μ : Measure α)
    (ν : Measure β) : Prop where
  /-- The matched and unmatched left mass together give the left law. -/
  fst_add_residual : c.fst + residual = μ
  /-- Matched right mass is contained in the right law. -/
  snd_le : c.snd ≤ ν

/-- Exact couplings have zero residual. -/
theorem IsCoupling.withResidual {c : Measure (α × β)} {μ : Measure α} {ν : Measure β}
    (h : IsCoupling c μ ν) : IsSubcouplingWithResidual c 0 μ ν :=
  ⟨by simpa using h.fst_eq, h.snd_eq.le⟩

namespace IsSubcouplingWithResidual

variable {c : Measure (α × β)} {r μ : Measure α} {ν : Measure β}

/-- Sequential substitution propagates old residual mass and accumulates conditional residuals.
All conditional obligations are relative to the actual joint initial-state law. -/
theorem bind (hc : IsSubcouplingWithResidual c r μ ν)
    {k : α → Measure γ} {l : β → Measure δ}
    {j : α × β → Measure (γ × δ)} {e : α × β → Measure γ}
    (hk : Measurable k) (hl : Measurable l) (hj : Measurable j) (he : Measurable e)
    (h : ∀ᵐ z ∂c, IsSubcouplingWithResidual (j z) (e z) (k z.1) (l z.2)) :
    IsSubcouplingWithResidual (c.bind j) (r.bind k + c.bind e) (μ.bind k) (ν.bind l) := by
  constructor
  · rw [Measure.fst, map_bind c hj measurable_fst]
    change c.bind (fun z => (j z).fst) + (r.bind k + c.bind e) = _
    rw [← add_assoc, add_right_comm, ← bind_add_right c (k := fun z => (j z).fst)
      ((measurable_map _ measurable_fst).comp hj) he]
    rw [bind_congr_right (h.mono fun _ hz => hz.fst_add_residual)]
    rw [← bind_map c measurable_fst hk, ← bind_add_left _ _ hk]
    exact congrArg (fun m => m.bind k) hc.fst_add_residual
  · rw [Measure.snd, map_bind c hj measurable_snd]
    change c.bind (fun z => (j z).snd) ≤ _
    calc
      _ ≤ c.bind (fun z => l z.2) := bind_mono_right
        ((measurable_map _ measurable_snd).comp hj).aemeasurable
        (hl.comp measurable_snd).aemeasurable (h.mono fun _ hz => hz.snd_le)
      _ = c.snd.bind l := (bind_map c measurable_snd hl).symm
      _ ≤ ν.bind l := bind_mono_left hc.snd_le hl

/-- A left event implies the right event outside a joint bad event, up to residual mass. -/
theorem event_le (hc : IsSubcouplingWithResidual c r μ ν)
    {s : Set α} {t : Set β} (hs : MeasurableSet s) (ht : MeasurableSet t)
    (bad : Set (α × β))
    (h : ∀ᵐ z ∂c, z.1 ∈ s → z.2 ∈ t ∨ z ∈ bad) :
    μ s ≤ ν t + c bad + r Set.univ := by
  have hmatched : c.fst s ≤ c.snd t + c bad := by
    rw [Measure.fst, Measure.snd, map_apply measurable_fst hs,
      map_apply measurable_snd ht]
    exact (measure_mono_ae h).trans (measure_union_le _ _)
  rw [← hc.fst_add_residual, add_apply]
  exact add_le_add (hmatched.trans (add_le_add (hc.snd_le t) le_rfl))
    (measure_mono (Set.subset_univ s))

/-- The unmatched left mass is an explicit bound on one-sided event loss when the matched
joint law satisfies the event implication almost everywhere. -/
theorem event_le_add_residual (hc : IsSubcouplingWithResidual c r μ ν)
    {s : Set α} {t : Set β} (hs : MeasurableSet s) (ht : MeasurableSet t)
    (h : ∀ᵐ z ∂c, z.1 ∈ s → z.2 ∈ t) :
    μ s ≤ ν t + r Set.univ := by
  simpa using hc.event_le hs ht ∅ (h.mono fun _ hz hmem => Or.inl (hz hmem))

end IsSubcouplingWithResidual

end MeasureTheory.Measure
