/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module
public import PolyFun.Interaction.Multiparty.Observation
public import ToMathlib.MeasureTheory.Measure.Observation

/-!
# The measurable content of a participant's observation

PolyFun observations describe which value a participant sees. A chosen measurable space on
that value induces a sub-σ-algebra on full states. The full state remains available for
execution: restricting an observer's information does not assert that the observed process
is itself Markov. Refinement of measurable information needs a measurable factor, whereas
PolyFun's underlying information preorder only requires a function.
-/

public section

open MeasureTheory

namespace Interaction.Multiparty.Observation

variable {X : Type*} (view : Observation X) [MeasurableSpace view.1]

/-- Events on full states that can be decided from the chosen observation. -/
@[instance_reducible]
def sigma : MeasurableSpace X := MeasurableSpace.comap view.2 inferInstance

/-- The law presented to this observer. -/
noncomputable def law [MeasurableSpace X] (μ : Measure X) : Measure view.1 := μ.map view.2

/-- A measurable observation pulls back a sub-σ-algebra of the full state space. -/
theorem sigma_le [MeasurableSpace X] (hview : Measurable view.2) :
    view.sigma ≤ ‹MeasurableSpace X› := hview.comap_le

/-- Two full-state laws are observationally equal precisely on the observer's σ-algebra. -/
theorem law_eq_iff_trim_eq [MeasurableSpace X] (hview : Measurable view.2) (μ ν : Measure X) :
    view.law μ = view.law ν ↔ μ.trim hview.comap_le = ν.trim hview.comap_le :=
  Measure.map_eq_iff_trim_comap_eq μ ν hview

/-- Measurable postprocessing preserves equality of observed laws. -/
theorem law_eq_of_factor [MeasurableSpace X] (hview : Measurable view.2)
    (coarse : Observation X) [MeasurableSpace coarse.1]
    (factor : view.1 → coarse.1) (hfactor : Measurable factor)
    (hcommute : ∀ x, coarse.2 x = factor (view.2 x))
    {μ ν : Measure X} (h : view.law μ = view.law ν) : coarse.law μ = coarse.law ν :=
  Measure.map_eq_of_factor μ ν hview hfactor (funext hcommute) h

end Interaction.Multiparty.Observation
