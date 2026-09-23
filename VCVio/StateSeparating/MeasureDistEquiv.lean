/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import VCVio.OracleComp.SimSemantics.StateT.StateSeparating
public import VCVio.OracleComp.SimSemantics.StateT.Measure
public import VCVio.OracleComp.EvalDist.Measure
public import VCVio.EvalDist.ProbabilityNotation
public import VCVio.StateSeparating.Advantage.Measure

/-!
# Measure equivalence of stateful handlers

Two handlers are equivalent when every adaptive client has the same successful-output measure.
The interpretation can be weighted and need not assign positive mass to each structurally possible
answer. Local contracts retain the joint response/state measure because later calls may observe
private state.
-/

public section

open OracleSpec OracleComp MeasureTheory

universe u v

namespace QueryImpl.Stateful

variable {ι : Type u} {I : OracleSpec.{u, 0} ι}
  {ε : Type v} {E : OracleSpec.{v, 0} ε} {σ σ₀ σ₁ σ₂ : Type}
  [EvalDistSemantics (OracleComp I)]

/-- Every adaptive client observes equal measures from the two initial handler states. -/
def MeasureDistEquiv (left : Stateful I E σ₀) (s₀ : σ₀)
    (right : Stateful I E σ₁) (s₁ : σ₁) : Prop :=
  ∀ {α : Type} [MeasurableSpace α] (client : OracleComp E α),
    𝒟[left.run s₀ client] = 𝒟[right.run s₁ client]

namespace MeasureDistEquiv

/-- Equivalent handlers have equal measures for each measurable client observation. -/
theorem run_evalDist_eq {left : Stateful I E σ₀} {right : Stateful I E σ₁}
    {s₀ : σ₀} {s₁ : σ₁} (h : MeasureDistEquiv left s₀ right s₁)
    {α : Type} [MeasurableSpace α] (client : OracleComp E α) :
    𝒟[left.run s₀ client] = 𝒟[right.run s₁ client] := h client

/-- Equality of all client observations establishes handler equivalence. -/
theorem of_run_evalDist_eq {left : Stateful I E σ₀} {right : Stateful I E σ₁}
    {s₀ : σ₀} {s₁ : σ₁}
    (h : ∀ {α : Type} [MeasurableSpace α] (client : OracleComp E α),
      𝒟[left.run s₀ client] = 𝒟[right.run s₁ client]) :
    MeasureDistEquiv left s₀ right s₁ := h

protected theorem refl (handler : Stateful I E σ) (state : σ) :
    MeasureDistEquiv handler state handler state := fun _ ↦ rfl

protected theorem symm {left : Stateful I E σ₀} {right : Stateful I E σ₁}
    {s₀ : σ₀} {s₁ : σ₁} (h : MeasureDistEquiv left s₀ right s₁) :
    MeasureDistEquiv right s₁ left s₀ := fun client ↦ (h client).symm

protected theorem trans {left : Stateful I E σ₀} {middle : Stateful I E σ₁}
    {right : Stateful I E σ₂} {s₀ : σ₀} {s₁ : σ₁} {s₂ : σ₂}
    (h₀ : MeasureDistEquiv left s₀ middle s₁)
    (h₁ : MeasureDistEquiv middle s₁ right s₂) :
    MeasureDistEquiv left s₀ right s₂ := fun client ↦ (h₀ client).trans (h₁ client)

/-- Equal executions induce equal observations. -/
theorem of_run_eq {left : Stateful I E σ₀} {right : Stateful I E σ₁}
    {s₀ : σ₀} {s₁ : σ₁}
    (h : ∀ {α : Type} (client : OracleComp E α),
      left.run s₀ client = right.run s₁ client) :
    MeasureDistEquiv left s₀ right s₁ := fun client ↦ congrArg evalDist (h client)

/-- Local equality of the joint response and state measures lifts through every client. -/
theorem of_step [LawfulEvalDistSemantics (OracleComp I)] {left right : Stateful I E σ}
    (h : ∀ operation state, ∀ [MeasurableSpace (E.Range operation × σ)],
      𝒟[(left operation).run state] = 𝒟[(right operation).run state])
    (state : σ) : MeasureDistEquiv left state right state := by
  intro α _ client
  let : MeasurableSpace σ := ⊤
  simp only [Stateful.run, StateT.run'_eq, _root_.evalDist_map _ measurable_fst]
  exact congrArg (Measure.map Prod.fst)
    (evalDist_simulateQ_run_congr_of_forall left right h client state)

/-- Equivalent handlers assign equal mass to every observable event. -/
theorem prEvent_eq [LawfulEvalDistSemantics (OracleComp I)]
    {left : Stateful I E σ₀} {right : Stateful I E σ₁}
    {s₀ : σ₀} {s₁ : σ₁} (h : MeasureDistEquiv left s₀ right s₁)
    {α : Type} (client : OracleComp E α) (event : α → Prop) :
    Pr{let output ← left.run s₀ client}[event output] =
      Pr{let output ← right.run s₁ client}[event output] := by
  let : MeasurableSpace α := ⊤
  rw [prEvent_eq_evalDist_of_discrete, prEvent_eq_evalDist_of_discrete, h client]

/-- Boolean distinguishing advantage vanishes for equivalent probability-only handlers. -/
theorem boolDistAdvantage_eq_zero
    {left : Stateful unifSpec E σ₀} {right : Stateful unifSpec E σ₁}
    {s₀ : σ₀} {s₁ : σ₁} (h : MeasureDistEquiv left s₀ right s₁)
    (client : OracleComp E Bool) :
    ProbComp.boolDistAdvantage (left.run s₀ client) (right.run s₁ client) = 0 := by
  simp [ProbComp.boolDistAdvantage, h client]

/-- Equivalent handlers may replace the left experiment in a distinguishing bound. -/
theorem advantage_left {left : Stateful unifSpec E σ₀} {left' : Stateful unifSpec E σ₂}
    {s₀ : σ₀} {s₀' : σ₂}
    (h : MeasureDistEquiv left s₀ left' s₀') (right : Stateful unifSpec E σ₁) (s₁ : σ₁)
    (client : OracleComp E Bool) :
    left.advantage s₀ right s₁ client = left'.advantage s₀' right s₁ client :=
  advantage_eq_of_evalDist_run_eq (h client)

/-- Equivalent handlers may replace the right experiment in a distinguishing bound. -/
theorem advantage_right (left : Stateful unifSpec E σ₀) (s₀ : σ₀)
    {right : Stateful unifSpec E σ₁} {right' : Stateful unifSpec E σ₂}
    {s₁ : σ₁} {s₁' : σ₂}
    (h : MeasureDistEquiv right s₁ right' s₁') (client : OracleComp E Bool) :
    left.advantage s₀ right s₁ client = left.advantage s₀ right' s₁' client :=
  advantage_eq_of_evalDist_run_eq_right (h client)

/-- Equivalent probability-only handlers have zero distinguishing advantage. -/
theorem advantage_eq_zero {left : Stateful unifSpec E σ₀} {right : Stateful unifSpec E σ₁}
    {s₀ : σ₀} {s₁ : σ₁} (h : MeasureDistEquiv left s₀ right s₁)
    (client : OracleComp E Bool) : left.advantage s₀ right s₁ client = 0 :=
  h.boolDistAdvantage_eq_zero client

/-- An equivalent inner handler preserves observations through a matching outer handler. -/
theorem link_inner_congr {μ : Type} {M : OracleSpec μ} {τ : Type}
    (outer : Stateful M E τ) (state : τ)
    {left : Stateful I M σ₀} {right : Stateful I M σ₁} {s₀ : σ₀} {s₁ : σ₁}
    (h : MeasureDistEquiv left s₀ right s₁) :
    MeasureDistEquiv (outer.link left) (state, s₀) (outer.link right) (state, s₁) := by
  intro α _ client
  rw [run_link_eq_run_shiftLeft, run_link_eq_run_shiftLeft]
  exact h (outer.shiftLeft state client)

end MeasureDistEquiv
end QueryImpl.Stateful
