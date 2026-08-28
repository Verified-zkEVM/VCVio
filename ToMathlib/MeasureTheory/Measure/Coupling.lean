/-
Copyright (c) 2026 VCVio Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma, Quang Dao
-/

module

public import Mathlib.MeasureTheory.Measure.GiryMonad
public import Mathlib.MeasureTheory.Measure.Prod

/-!
# Couplings of measures

This file defines couplings directly at Mathlib's `Measure` boundary.  A coupling is a joint
measure whose first and second marginals are the requested measures.  No discreteness or
countability assumption is built into the definition.

The elementary constructors here are the measure-theoretic foundation for VCVio's relational
program logic. In particular, relational postconditions can be stated almost everywhere under
the joint measure instead of by quantifying over discrete point support.
-/

@[expose] public section

open MeasureTheory

universe u v w x

namespace MeasureTheory.Measure

variable {α : Type u} {β : Type v} {γ : Type w} {δ : Type x}
variable [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ] [MeasurableSpace δ]

/-- `c` is a coupling of `μ` and `ν` when its two marginals are exactly `μ` and `ν`. -/
class IsCoupling (c : Measure (α × β)) (μ : Measure α) (ν : Measure β) : Prop where
  /-- The first marginal of the joint measure. -/
  fst_eq : c.fst = μ
  /-- The second marginal of the joint measure. -/
  snd_eq : c.snd = ν

/-- Joint measures coupling `μ` and `ν`. -/
def Coupling (μ : Measure α) (ν : Measure β) :=
  {c : Measure (α × β) // IsCoupling c μ ν}

namespace IsCoupling

variable {c : Measure (α × β)} {μ : Measure α} {ν : Measure β}

/-- A coupling has the same total mass as its first marginal. -/
theorem joint_apply_univ_eq_left (h : IsCoupling c μ ν) : c Set.univ = μ Set.univ := by
  rw [← h.fst_eq, Measure.fst_univ]

/-- A coupling has the same total mass as its second marginal. -/
theorem joint_apply_univ_eq_right (h : IsCoupling c μ ν) : c Set.univ = ν Set.univ := by
  rw [← h.snd_eq, Measure.snd_univ]

/-- Measures admitting a coupling necessarily have equal total mass. -/
theorem apply_univ_eq (h : IsCoupling c μ ν) : μ Set.univ = ν Set.univ := by
  rw [← h.joint_apply_univ_eq_left, h.joint_apply_univ_eq_right]

/-- The diagonal pushforward is a self-coupling of any measure. -/
theorem refl (μ : Measure α) :
    IsCoupling (μ.map fun a => (a, a)) μ μ := by
  have hdiag : Measurable (fun a : α => (a, a)) :=
    measurable_id.prodMk measurable_id
  constructor
  · rw [Measure.fst, Measure.map_map measurable_fst hdiag]
    simp [Function.comp_def]
  · rw [Measure.snd, Measure.map_map measurable_snd hdiag]
    simp [Function.comp_def]

/-- The product of two probability measures is an independent coupling. -/
theorem prod (μ : Measure α) (ν : Measure β)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    IsCoupling (μ.prod ν) μ ν := by
  constructor <;> simp

/-- A Dirac measure at a pair couples the corresponding Dirac marginals. -/
theorem dirac (a : α) (b : β) :
    IsCoupling (Measure.dirac (a, b)) (Measure.dirac a) (Measure.dirac b) := by
  constructor
  · simpa [Measure.fst] using Measure.map_dirac' measurable_fst (a, b)
  · simpa [Measure.snd] using Measure.map_dirac' measurable_snd (a, b)

/-- Swapping the coordinates of a coupling swaps its marginals. -/
theorem swap (h : IsCoupling c μ ν) :
    IsCoupling (c.map Prod.swap) ν μ := by
  constructor
  · rw [Measure.fst, Measure.map_map measurable_fst measurable_swap]
    simpa [Function.comp_def, Measure.snd] using h.snd_eq
  · rw [Measure.snd, Measure.map_map measurable_snd measurable_swap]
    simpa [Function.comp_def, Measure.fst] using h.fst_eq

/-- Measurable maps of both coordinates transport a coupling to the pushed-forward marginals. -/
theorem map (h : IsCoupling c μ ν) (f : α → γ) (g : β → δ)
    (hf : Measurable f) (hg : Measurable g) :
    IsCoupling (c.map fun z => (f z.1, g z.2)) (μ.map f) (ν.map g) := by
  have hpair : Measurable (fun z : α × β => (f z.1, g z.2)) :=
    (hf.comp measurable_fst).prodMk (hg.comp measurable_snd)
  have hfst : c.map Prod.fst = μ := h.fst_eq
  have hsnd : c.map Prod.snd = ν := h.snd_eq
  constructor
  · rw [Measure.fst, Measure.map_map measurable_fst hpair]
    rw [show Prod.fst ∘ (fun z : α × β => (f z.1, g z.2)) = f ∘ Prod.fst by rfl,
      ← Measure.map_map hf measurable_fst, hfst]
  · rw [Measure.snd, Measure.map_map measurable_snd hpair]
    rw [show Prod.snd ∘ (fun z : α × β => (f z.1, g z.2)) = g ∘ Prod.snd by rfl,
      ← Measure.map_map hg measurable_snd, hsnd]

end IsCoupling

namespace Coupling

variable {μ : Measure α} {ν : Measure β}

/-- The joint measure underlying a coupling. -/
abbrev joint (c : Coupling μ ν) : Measure (α × β) := c.1

/-- Canonical diagonal self-coupling. -/
noncomputable def refl (μ : Measure α) : Coupling μ μ :=
  ⟨μ.map fun a => (a, a), IsCoupling.refl μ⟩

/-- Independent-product coupling of probability measures. -/
noncomputable def prod (μ : Measure α) (ν : Measure β)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] : Coupling μ ν :=
  ⟨μ.prod ν, IsCoupling.prod μ ν⟩

/-- Coupling of two pure outcomes. -/
noncomputable def dirac (a : α) (b : β) :
    Coupling (Measure.dirac a) (Measure.dirac b) :=
  ⟨Measure.dirac (a, b), IsCoupling.dirac a b⟩

/-- Swap the coordinates of a coupling. -/
noncomputable def swap (c : Coupling μ ν) : Coupling ν μ :=
  ⟨c.1.map Prod.swap, c.2.swap⟩

/-- Push a coupling forward through a pair of measurable functions. -/
noncomputable def map (c : Coupling μ ν) (f : α → γ) (g : β → δ)
    (hf : Measurable f) (hg : Measurable g) : Coupling (μ.map f) (ν.map g) :=
  ⟨c.1.map fun z => (f z.1, g z.2), c.2.map f g hf hg⟩

end Coupling

end MeasureTheory.Measure
