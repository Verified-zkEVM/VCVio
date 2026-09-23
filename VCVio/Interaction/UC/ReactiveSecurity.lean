/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.Interaction.UC.ReactiveNetwork.HandledAssembly
public import VCVio.OracleComp.Constructions.SampleableType
public import VCVio.EvalDist.MeasureTVDist
public import VCVio.EvalDist.FailureMeasure

/-!
# Graded contextual comparison of executable reactive fragments

Every comparison executes the actual composed network with its intrinsic local interpreters.
The fixed observation retains unfinished prefixes, explicit aborts, and returned Booleans.
Local operations use total finite sampling computations. The finite observation space has its
canonical discrete measurable structure; callers cannot replace the observation by a constant.

The contextual relation is statistical and adds its error bounds under composition. Its
unrestricted form quantifies over executable closing contexts and finite horizons, with no
simulator. Computational UC additionally needs structural simulators, uniform admissibility,
and an explicit resource policy; this relation alone does not assert those properties.
-/

public section

namespace Interaction.UC.ReactiveSecurity

open PFunctor OracleComp ReactiveProcess ReactiveNetwork MeasureTheory
open scoped ENNReal

/-- Executable finite fragments with probabilistic local operations and private machine states. -/
abbrev System (boundary : PortBoundary) := HandledAssembly ProbComp boundary Bool

/-- `none` is unfinished, `some none` is aborted, and `some (some bit)` is a returned bit. -/
abbrev Result := Option (Option Bool)

/-- Encode all three runtime outcome forms without forgetting any terminal information. -/
@[expose] def observe : Option (Outcome Bool) → Result
  | none => none
  | some .aborted => some none
  | some (.returned bit) => some (some bit)

/-- The fixed observation retains every distinction in the runtime's Boolean outcome. -/
theorem observe_injective : Function.Injective observe := by
  intro x y h
  let decode : Result → Option (Outcome Bool) := fun
    | none => none
    | some none => some .aborted
    | some (some bit) => some (.returned bit)
  have inverse : ∀ value, decode (observe value) = value := by
    intro value
    rcases value with _ | value
    · rfl
    · cases value <;> rfl
  exact (inverse x).symm.trans ((congrArg decode h).trans (inverse y))

/-- A concrete closing fragment, its selected environment, and a finite execution horizon. -/
structure Context (boundary : PortBoundary) where
  /-- The actual environment and any other closing components. -/
  system : System (PortBoundary.swap boundary)
  /-- The single environment whose outcome is observed. -/
  environment : system.Node
  /-- Number of token activations afforded to the complete network. -/
  fuel : ℕ

variable {Δ Δ₁ Δ₂ Γ : PortBoundary}

/-- Execute the protocol and closing fragment using their actual local interpreters. -/
@[expose] def experiment (system : System Δ) (context : Context Δ) : ProbComp Result :=
  observe <$> (system.plug context.system).tokenObservation (.inr context.environment) context.fuel

/-- The measure of finite Boolean observations, including unfinished and aborted runs. -/
noncomputable def law (system : System Δ) (context : Context Δ) : Measure Result :=
  𝒟[experiment system context]

/-- The observation law is the measure denotation of the routed experiment. -/
theorem law_eq_evalDist (system : System Δ) (context : Context Δ) :
    law system context = 𝒟[experiment system context] := by
  unfold law
  rfl

/-- Total sampling retains unit mass, including aborted and unfinished observations. -/
theorem law_univ (system : System Δ) (context : Context Δ) :
    law system context Set.univ = 1 := by
  rw [law_eq_evalDist]
  exact OracleComp.evalDist_apply_univ_eq_one _

/-- The actual execution law has total mass at most one. -/
theorem law_univ_le_one (system : System Δ) (context : Context Δ) :
    law system context Set.univ ≤ 1 :=
  evalDist_apply_univ_le_one _

/-- Statistical distance between the two actual experiments against one fixed context. -/
noncomputable def advantage (real ideal : System Δ) (context : Context Δ) : ℝ≥0∞ :=
  (law real context).etvDist (law ideal context)

/-- The distinguishing advantage compares the actual observation measures. -/
theorem advantage_eq_etvDist (real ideal : System Δ) (context : Context Δ) :
    advantage real ideal context = (law real context).etvDist (law ideal context) := by
  unfold advantage
  rfl

/-- Reversing the two experiments preserves their statistical distance. -/
theorem advantage_comm (real ideal : System Δ) (context : Context Δ) :
    advantage real ideal context = advantage ideal real context := Measure.etvDist_comm _ _

/-- Sequential comparisons add their distinguishing-error bounds. -/
theorem advantage_triangle (first middle last : System Δ) (context : Context Δ) :
    advantage first last context ≤ advantage first middle context + advantage middle last context :=
  Measure.etvDist_triangle _ _ _

namespace Context

/-- Move the right parallel fragment into the closing context, retaining its actual interpreter. -/
@[expose] def parLeft (right : System Δ₂) (context : Context (PortBoundary.tensor Δ₁ Δ₂)) :
    Context Δ₁ where
  system := right.parContextLeft context.system
  environment := .inl context.environment
  fuel := context.fuel

/-- Move the left parallel fragment into the closing context. -/
@[expose] def parRight (left : System Δ₁) (context : Context (PortBoundary.tensor Δ₁ Δ₂)) :
    Context Δ₂ where
  system := left.parContextRight context.system
  environment := .inl context.environment
  fuel := context.fuel

/-- Retain the right wired fragment, including the original shared-boundary routes. -/
@[expose] def wireLeft (right : System (PortBoundary.tensor (PortBoundary.swap Γ) Δ₂))
    (context : Context (PortBoundary.tensor Δ₁ Δ₂)) : Context (PortBoundary.tensor Δ₁ Γ) where
  system := right.wireContextLeft context.system
  environment := .inl context.environment
  fuel := context.fuel

/-- Retain the left wired fragment, including the original shared-boundary routes. -/
@[expose] def wireRight (left : System (PortBoundary.tensor Δ₁ Γ))
    (context : Context (PortBoundary.tensor Δ₁ Δ₂)) :
    Context (PortBoundary.tensor (PortBoundary.swap Γ) Δ₂) where
  system := left.wireContextRight context.system
  environment := .inl context.environment
  fuel := context.fuel

end Context

/-- Parallel factorization preserves the probability experiment itself. -/
theorem experiment_par_left (left : System Δ₁) (right : System Δ₂)
    (context : Context (PortBoundary.tensor Δ₁ Δ₂)) :
    experiment left (context.parLeft right) = experiment (left.par right) context := by
  exact congrArg (Functor.map observe)
    (HandledAssembly.tokenObservation_close_par_left left right context.system
      context.environment context.fuel)

/-- The right parallel residual context preserves the probability experiment. -/
theorem experiment_par_right (left : System Δ₁) (right : System Δ₂)
    (context : Context (PortBoundary.tensor Δ₁ Δ₂)) :
    experiment right (context.parRight left) = experiment (left.par right) context := by
  exact congrArg (Functor.map observe)
    (HandledAssembly.tokenObservation_close_par_right left right context.system
      context.environment context.fuel)

/-- The left wired residual context preserves the probability experiment. -/
theorem experiment_wire_left (left : System (PortBoundary.tensor Δ₁ Γ))
    (right : System (PortBoundary.tensor (PortBoundary.swap Γ) Δ₂))
    (context : Context (PortBoundary.tensor Δ₁ Δ₂)) :
    experiment left (context.wireLeft right) = experiment (left.wire right) context := by
  exact congrArg (Functor.map observe)
    (HandledAssembly.tokenObservation_close_wire_left left right context.system
      context.environment context.fuel)

/-- The right wired residual context preserves the probability experiment. -/
theorem experiment_wire_right (left : System (PortBoundary.tensor Δ₁ Γ))
    (right : System (PortBoundary.tensor (PortBoundary.swap Γ) Δ₂))
    (context : Context (PortBoundary.tensor Δ₁ Δ₂)) :
    experiment right (context.wireRight left) = experiment (left.wire right) context := by
  exact congrArg (Functor.map observe)
    (HandledAssembly.tokenObservation_close_wire_right left right context.system
      context.environment context.fuel)

/-- Statistical comparison against an explicitly allowed class of executable contexts. -/
@[expose] def ContextualWithin (allowed : Context Δ → Prop) (error : ℝ≥0∞)
    (real ideal : System Δ) : Prop :=
  ∀ context, allowed context → advantage real ideal context ≤ error

/-- Statistical comparison against every finite executable closing context and horizon. -/
@[expose] def Contextual (error : ℝ≥0∞) (real ideal : System Δ) : Prop :=
  ∀ context, advantage real ideal context ≤ error

namespace Contextual

/-- A concrete system has zero advantage against itself at every finite horizon. -/
theorem refl (system : System Δ) : Contextual 0 system system := by
  intro context
  simp only [advantage, Measure.etvDist_self, le_refl]

/-- Sequential statistical comparisons add their error bounds. -/
theorem trans {first middle last : System Δ} {error₁ error₂ : ℝ≥0∞}
    (h₁ : Contextual error₁ first middle) (h₂ : Contextual error₂ middle last) :
    Contextual (error₁ + error₂) first last := fun context =>
  (advantage_triangle first middle last context).trans (add_le_add (h₁ context) (h₂ context))

/-- Replacement of the left parallel fragment uses its executable residual context. -/
theorem par_left {real ideal : System Δ₁} {error : ℝ≥0∞} (h : Contextual error real ideal)
    (right : System Δ₂) : Contextual error (real.par right) (ideal.par right) := by
  intro context
  simpa only [advantage, law, experiment_par_left] using h (context.parLeft right)

/-- Replacement of the right parallel fragment uses its executable residual context. -/
theorem par_right {real ideal : System Δ₂} {error : ℝ≥0∞} (left : System Δ₁)
    (h : Contextual error real ideal) : Contextual error (left.par real) (left.par ideal) := by
  intro context
  simpa only [advantage, law, experiment_par_right] using h (context.parRight left)

/-- Independent replacements in parallel add their statistical error bounds. -/
theorem par_compose {real₁ ideal₁ : System Δ₁} {real₂ ideal₂ : System Δ₂} {error₁ error₂ : ℝ≥0∞}
    (h₁ : Contextual error₁ real₁ ideal₁) (h₂ : Contextual error₂ real₂ ideal₂) :
    Contextual (error₁ + error₂) (real₁.par real₂) (ideal₁.par ideal₂) :=
  (h₁.par_left real₂).trans (par_right ideal₁ h₂)

/-- Replacement of the left wired fragment retains the actual shared-boundary traffic. -/
theorem wire_left {real ideal : System (PortBoundary.tensor Δ₁ Γ)} {error : ℝ≥0∞}
    (h : Contextual error real ideal)
    (right : System (PortBoundary.tensor (PortBoundary.swap Γ) Δ₂)) :
    Contextual error (real.wire right) (ideal.wire right) := by
  intro context
  simpa only [advantage, law, experiment_wire_left] using h (context.wireLeft right)

/-- Replacement of the right wired fragment retains the actual shared-boundary traffic. -/
theorem wire_right {real ideal : System (PortBoundary.tensor (PortBoundary.swap Γ) Δ₂)}
    {error : ℝ≥0∞} (left : System (PortBoundary.tensor Δ₁ Γ)) (h : Contextual error real ideal) :
    Contextual error (left.wire real) (left.wire ideal) := by
  intro context
  simpa only [advantage, law, experiment_wire_right] using h (context.wireRight left)

/-- Independent replacements across a shared boundary add their statistical error bounds. -/
theorem wire_compose {real₁ ideal₁ : System (PortBoundary.tensor Δ₁ Γ)}
    {real₂ ideal₂ : System (PortBoundary.tensor (PortBoundary.swap Γ) Δ₂)} {error₁ error₂ : ℝ≥0∞}
    (h₁ : Contextual error₁ real₁ ideal₁) (h₂ : Contextual error₂ real₂ ideal₂) :
    Contextual (error₁ + error₂) (real₁.wire real₂) (ideal₁.wire ideal₂) :=
  (h₁.wire_left real₂).trans (wire_right ideal₁ h₂)

end Contextual

namespace ContextualWithin

/-- Error bounds add when both comparisons admit the same executable contexts. -/
theorem trans {allowed : Context Δ → Prop} {first middle last : System Δ} {error₁ error₂ : ℝ≥0∞}
    (h₁ : ContextualWithin allowed error₁ first middle)
    (h₂ : ContextualWithin allowed error₂ middle last) :
    ContextualWithin allowed (error₁ + error₂) first last := fun context hallowed =>
  (advantage_triangle first middle last context).trans
    (add_le_add (h₁ context hallowed) (h₂ context hallowed))

/-- Allowed-context comparison composes on the left when the actual residual context is admitted. -/
theorem par_left {allowed : Context Δ₁ → Prop}
    {compositeAllowed : Context (PortBoundary.tensor Δ₁ Δ₂) → Prop}
    {real ideal : System Δ₁} {error : ℝ≥0∞} (h : ContextualWithin allowed error real ideal)
    (right : System Δ₂)
    (hcontext : ∀ context, compositeAllowed context → allowed (context.parLeft right)) :
    ContextualWithin compositeAllowed error (real.par right) (ideal.par right) := by
  intro context hallowed
  simpa only [advantage, law, experiment_par_left] using
    h (context.parLeft right) (hcontext context hallowed)

/-- Right parallel replacement requires admission of the executable residual context. -/
theorem par_right {allowed : Context Δ₂ → Prop}
    {compositeAllowed : Context (PortBoundary.tensor Δ₁ Δ₂) → Prop}
    {real ideal : System Δ₂} {error : ℝ≥0∞} (left : System Δ₁)
    (h : ContextualWithin allowed error real ideal)
    (hcontext : ∀ context, compositeAllowed context → allowed (context.parRight left)) :
    ContextualWithin compositeAllowed error (left.par real) (left.par ideal) := by
  intro context hallowed
  simpa only [advantage, law, experiment_par_right] using
    h (context.parRight left) (hcontext context hallowed)

/-- Left wired replacement requires admission of the executable residual context. -/
theorem wire_left {allowed : Context (PortBoundary.tensor Δ₁ Γ) → Prop}
    {compositeAllowed : Context (PortBoundary.tensor Δ₁ Δ₂) → Prop}
    {real ideal : System (PortBoundary.tensor Δ₁ Γ)} {error : ℝ≥0∞}
    (h : ContextualWithin allowed error real ideal)
    (right : System (PortBoundary.tensor (PortBoundary.swap Γ) Δ₂))
    (hcontext : ∀ context, compositeAllowed context → allowed (context.wireLeft right)) :
    ContextualWithin compositeAllowed error (real.wire right) (ideal.wire right) := by
  intro context hallowed
  simpa only [advantage, law, experiment_wire_left] using
    h (context.wireLeft right) (hcontext context hallowed)

/-- Right wired replacement requires admission of the executable residual context. -/
theorem wire_right {allowed : Context (PortBoundary.tensor (PortBoundary.swap Γ) Δ₂) → Prop}
    {compositeAllowed : Context (PortBoundary.tensor Δ₁ Δ₂) → Prop}
    {real ideal : System (PortBoundary.tensor (PortBoundary.swap Γ) Δ₂)} {error : ℝ≥0∞}
    (left : System (PortBoundary.tensor Δ₁ Γ)) (h : ContextualWithin allowed error real ideal)
    (hcontext : ∀ context, compositeAllowed context → allowed (context.wireRight left)) :
    ContextualWithin compositeAllowed error (left.wire real) (left.wire ideal) := by
  intro context hallowed
  simpa only [advantage, law, experiment_wire_right] using
    h (context.wireRight left) (hcontext context hallowed)

end ContextualWithin

end Interaction.UC.ReactiveSecurity
