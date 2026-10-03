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
public import VCVio.OracleComp.Coercions.SubSpec.Measure

/-!
# Measure equivalence of stateful handlers

Two handlers are equivalent when every adaptive client has the same successful-output measure.
The interpretation can be weighted and need not assign positive mass to each possible
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
@[expose] def MeasureDistEquiv (left : Stateful I E σ₀) (s₀ : σ₀)
    (right : Stateful I E σ₁) (s₁ : σ₁) : Prop :=
  ∀ {α : Type} [MeasurableSpace α] (client : OracleComp E α),
    𝒟[left.run s₀ client] = 𝒟[right.run s₁ client]

@[inherit_doc MeasureDistEquiv]
scoped notation:50 "(" h₀ ", " s₀ ")" " ≡ᵈ " "(" h₁ ", " s₁ ")" =>
  QueryImpl.Stateful.MeasureDistEquiv h₀ s₀ h₁ s₁

/-- Every adaptive client observes equal measures from the default initial handler states. -/
@[expose] def MeasureDistEquiv₀ [Inhabited σ₀] [Inhabited σ₁] (left : Stateful I E σ₀)
    (right : Stateful I E σ₁) : Prop :=
  MeasureDistEquiv left default right default

@[inherit_doc MeasureDistEquiv₀]
scoped infix:50 " ≡ᵈ₀ " => QueryImpl.Stateful.MeasureDistEquiv₀

namespace MeasureDistEquiv

/-- Equivalent handlers have equal measures for each measurable client observation. -/
theorem run_evalDist_eq {left : Stateful I E σ₀} {right : Stateful I E σ₁}
    {s₀ : σ₀} {s₁ : σ₁} (h : MeasureDistEquiv left s₀ right s₁)
    {α : Type} [MeasurableSpace α] (client : OracleComp E α) :
    𝒟[left.run s₀ client] = 𝒟[right.run s₁ client] := h client

/-- Equivalent handlers run every client to computations equal in distribution. -/
theorem run_evalDistEq [LawfulEvalDistSemantics (OracleComp I)] {left : Stateful I E σ₀}
    {right : Stateful I E σ₁} {s₀ : σ₀} {s₁ : σ₁} (h : MeasureDistEquiv left s₀ right s₁)
    {α : Type} (client : OracleComp E α) : left.run s₀ client =ᵈ right.run s₁ client :=
  letI : MeasurableSpace α := ⊤
  EvalDistEq.of_evalDist_eq (h client)

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
    (h : ∀ operation state, (left operation).run state =ᵈ (right operation).run state)
    (state : σ) : MeasureDistEquiv left state right state := by
  intro α _ client
  let : MeasurableSpace σ := ⊤
  simp only [Stateful.run, StateT.run'_eq, _root_.evalDist_map _ measurable_fst]
  exact congrArg (Measure.map Prod.fst)
    (evalDist_simulateQ_run_congr left right h client state)

omit [EvalDistSemantics (OracleComp I)] in
/-- Transporting a handler's state along an equivalence does not change what a client
observes: simulating with the transported handler is the original simulation with the final
state mapped back. -/
private theorem simulateQ_run_transport {left : Stateful I E σ₁} (φ : σ₀ ≃ σ₁)
    {α : Type} (client : OracleComp E α) (state : σ₀) :
    (simulateQ (fun operation ↦ StateT.mk fun s ↦
        Prod.map id φ.symm <$> (left operation).run (φ s)) client).run state =
      Prod.map id φ.symm <$> (simulateQ left client).run (φ state) := by
  induction client using OracleComp.inductionOn generalizing state with
  | pure value => simp
  | query_bind operation next ih =>
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.cont_query, OracleQuery.input_query,
      id_map, StateT.run_bind, StateT.run_mk, bind_map_left, map_bind, Prod.map_fst, id_eq,
      Prod.map_snd]
    refine congrArg _ (funext fun output ↦ ?_)
    rw [ih, Equiv.apply_symm_apply]

/-- Local measure equality up to a state equivalence lifts through every client. -/
theorem of_step_bij [LawfulEvalDistSemantics (OracleComp I)] {left : Stateful I E σ₀}
    {right : Stateful I E σ₁} (φ : σ₀ ≃ σ₁)
    (h : ∀ operation state,
      (left operation).run state =ᵈ Prod.map id φ.symm <$> (right operation).run (φ state))
    (state : σ₀) : MeasureDistEquiv left state right (φ state) := by
  let transported : Stateful I E σ₀ := fun operation ↦ StateT.mk fun s ↦
    Prod.map id φ.symm <$> (right operation).run (φ s)
  have hstep : MeasureDistEquiv left state transported state :=
    of_step (fun operation s ↦ h operation s) state
  intro α _ client
  refine (hstep client).trans (congrArg evalDist ?_)
  simp only [Stateful.run, StateT.run'_eq, transported, simulateQ_run_transport,
    Functor.map_map, Prod.map_fst, id_eq]

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
theorem boolDist_eq_zero
    {left : Stateful unifSpec E σ₀} {right : Stateful unifSpec E σ₁}
    {s₀ : σ₀} {s₁ : σ₁} (h : MeasureDistEquiv left s₀ right s₁)
    (client : OracleComp E Bool) :
    𝒟[left.run s₀ client].boolDist 𝒟[right.run s₁ client] = 0 := by
  simp [h client]

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
  h.boolDist_eq_zero client

/-- An equivalent inner handler preserves observations through a matching outer handler. -/
theorem link_inner_congr {μ : Type} {M : OracleSpec μ} {τ : Type}
    (outer : Stateful M E τ) (state : τ)
    {left : Stateful I M σ₀} {right : Stateful I M σ₁} {s₀ : σ₀} {s₁ : σ₁}
    (h : MeasureDistEquiv left s₀ right s₁) :
    MeasureDistEquiv (outer.link left) (state, s₀) (outer.link right) (state, s₁) := by
  intro α _ client
  rw [run_link_eq_run_shiftLeft, run_link_eq_run_shiftLeft]
  exact h (outer.shiftLeft state client)

section parSum

variable {ι₁ ι₂ : Type u} {I₁ : OracleSpec.{u, 0} ι₁} {I₂ : OracleSpec.{u, 0} ι₂}
  [OracleSpec.UniformAnswerMeasure I₁] [OracleSpec.UniformAnswerMeasure I₂]
  {ε₁ ε₂ : Type v} {E₁ : OracleSpec.{v, 0} ε₁} {E₂ : OracleSpec.{v, 0} ε₂}

/-- Parallel composition preserves local measure equality of both factors, over uniform import
interfaces. -/
theorem parSum_congr {h₁ h₁' : Stateful I₁ E₁ σ₁} {h₂ h₂' : Stateful I₂ E₂ σ₂}
    (hh₁ : ∀ operation state, (h₁ operation).run state =ᵈ (h₁' operation).run state)
    (hh₂ : ∀ operation state, (h₂ operation).run state =ᵈ (h₂' operation).run state)
    (s₁ : σ₁) (s₂ : σ₂) :
    MeasureDistEquiv (h₁.parSum h₂) (s₁, s₂) (h₁'.parSum h₂') (s₁, s₂) := by
  refine of_step (fun operation state ↦ ?_) (s₁, s₂)
  obtain ⟨a, b⟩ := state
  rcases operation with t | t
  · rw [parSum_apply_inl_run, parSum_apply_inl_run]
    exact EvalDistEq.map (((evalDistEq_liftComp_uniform _).trans (hh₁ t a)).trans
      (evalDistEq_liftComp_uniform _).symm) _
  · rw [parSum_apply_inr_run, parSum_apply_inr_run]
    exact EvalDistEq.map (((evalDistEq_liftComp_uniform _).trans (hh₂ t b)).trans
      (evalDistEq_liftComp_uniform _).symm) _

end parSum

end MeasureDistEquiv
end QueryImpl.Stateful
