/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import VCVio.ProgramLogic.Tactics

/-!
# Proof-Mode Entry / Exit Tactic Examples

This file validates proof-mode entry and exit tactics from
`VCVio.ProgramLogic.Tactics`: `game_trans`, `by_equiv`, `by_upto`, `by_dist`,
`rel_dist`, and relational simulation rules.
-/

@[expose] public section

open ENNReal OracleSpec OracleComp
open OracleComp.ProgramLogic
open OracleComp.ProgramLogic.Relational
open scoped OracleComp.ProgramLogic

universe u

variable {ι : Type u} {spec : OracleSpec ι}
variable [∀ t, Finite (spec.Range t)]
variable [OracleSpec.AnswerMeasure spec]
variable {α β γ : Type}

/-! ## Handler normalization -/

section HandlerNormalization

/-- `handler_step` consumes PolyFun's generic handler normal form. -/
example {m : Type → Type} [Monad m] [LawfulMonad m]
    (h : PFunctor.Handler.Stateful m Nat (PFunctor.monomial Bool Nat))
    (query : (PFunctor.monomial Bool Nat).A) (state : Nat) :
    h.run (PFunctor.FreeM.lift query) state = (h query).run state := by
  handler_step

end HandlerNormalization

/-! ## `game_trans` -/

example {g₁ g₂ g₃ : OracleComp spec α}
    (h₁ : g₁ =ᵈ g₂) (h₂ : g₂ =ᵈ g₃) :
    g₁ =ᵈ g₃ := by
  game_trans g₂
  · exact h₁
  · exact h₂

/-! ## `by_upto` -/

section ByUpto

variable {σ : Type} {ι : Type} {spec : OracleSpec ι}
variable [OracleSpec.AnswerMeasure spec]
variable {α : Type} [MeasurableSpace α]

example
    (impl₁ impl₂ : QueryImpl spec (StateT σ (OracleComp spec)))
    (bad : σ → Prop)
    (oa : OracleComp spec α) (s₀ : σ)
    (h_agree : ∀ (t : spec.Domain) (s : σ), ¬bad s →
      (impl₁ t).run s = (impl₂ t).run s)
    (h_mono₁ : ∀ (t : spec.Domain) (s : σ), bad s →
      ∀ x ∈ support ((impl₁ t).run s), bad x.2)
    (h_mono₂ : ∀ (t : spec.Domain) (s : σ), bad s →
      ∀ x ∈ support ((impl₂ t).run s), bad x.2) :
    measureETVDist ((simulateQ impl₁ oa).run' s₀) ((simulateQ impl₂ oa).run' s₀)
      ≤ Pr{let z ← (simulateQ impl₁ oa).run s₀}[bad z.2] := by
  by_upto bad
  · exact h_agree
  · exact h_mono₁
  · exact h_mono₂

end ByUpto

/-! ## Relational simulation -/

section RelSim

variable {σ₁ σ₂ : Type} {ι : Type} {spec : OracleSpec ι}
variable [∀ t, Finite (spec.Range t)]
variable [OracleSpec.AnswerMeasure spec]
variable {α : Type}

example
    (impl₁ : QueryImpl spec (StateT σ₁ (OracleComp spec)))
    (impl₂ : QueryImpl spec (StateT σ₂ (OracleComp spec)))
    (R_state : σ₁ → σ₂ → Prop)
    (oa : OracleComp spec α)
    (himpl : ∀ (t : spec.Domain) (s₁ : σ₁) (s₂ : σ₂),
      R_state s₁ s₂ →
      RelTriple ((impl₁ t).run s₁) ((impl₂ t).run s₂)
        (fun p₁ p₂ => p₁.1 = p₂.1 ∧ R_state p₁.2 p₂.2))
    (s₁ : σ₁) (s₂ : σ₂) (hs : R_state s₁ s₂) :
    ⟪(simulateQ impl₁ oa).run s₁
     ~ (simulateQ impl₂ oa).run s₂
     | fun p₁ p₂ => p₁.1 = p₂.1 ∧ R_state p₁.2 p₂.2⟫ := by
  rvcstep using R_state
  all_goals first | exact himpl | exact hs

example
    (impl₁ : QueryImpl spec (StateT σ₁ (OracleComp spec)))
    (impl₂ : QueryImpl spec (StateT σ₂ (OracleComp spec)))
    (R_state : σ₁ → σ₂ → Prop)
    (oa : OracleComp spec α)
    (himpl : ∀ (t : spec.Domain) (s₁ : σ₁) (s₂ : σ₂),
      R_state s₁ s₂ →
      RelTriple ((impl₁ t).run s₁) ((impl₂ t).run s₂)
        (fun p₁ p₂ => p₁.1 = p₂.1 ∧ R_state p₁.2 p₂.2))
    (s₁ : σ₁) (s₂ : σ₂) (hs : R_state s₁ s₂) :
    ⟪(simulateQ impl₁ oa).run' s₁
     ~ (simulateQ impl₂ oa).run' s₂
     | EqRel α⟫ := by
  rvcstep
  all_goals first | exact himpl | exact hs

end RelSim

/-! ## Relational simulation via exact distribution -/

section RelSimDist

variable {σ : Type} {ι : Type} {spec : OracleSpec ι}
variable [∀ t, Finite (spec.Range t)]
variable [OracleSpec.AnswerMeasure spec]
variable {α : Type}

example
    (impl₁ : QueryImpl spec (StateT σ (OracleComp spec)))
    (impl₂ : QueryImpl spec (StateT σ (OracleComp spec)))
    (oa : OracleComp spec α)
    (himpl : ∀ (t : spec.Domain) (s : σ), (impl₁ t).run s =ᵈ (impl₂ t).run s)
    (s₁ s₂ : σ) (hs : s₁ = s₂) :
    ⟪(simulateQ impl₁ oa).run' s₁
     ~ (simulateQ impl₂ oa).run' s₂
     | EqRel α⟫ := by
  rvcstep
  · exact himpl
  · exact hs

end RelSimDist

/-! ## `=ᵈ` / `by_equiv` -/

section EqualInDistribution

example (oa : OracleComp spec α) :
    oa =ᵈ oa := by
  rvcgen

/-
Using `rvcgen?` can explain the behavior of `rvcgen`:

example (oa : OracleComp spec α) :
    oa =ᵈ oa := by
  rvcgen?
-/

example [SampleableType α]
    (f : α → α) (hf : Function.Bijective f) :
    (f <$> ($ᵗ α : ProbComp α)) =ᵈ ($ᵗ α : ProbComp α) := by
  conv_rhs => rw [← id_map ($ᵗ α : ProbComp α)]
  by_equiv
  rvcstep using f
  exact hf

example {oa₁ oa₂ : OracleComp spec α}
    {f₁ f₂ : α → OracleComp spec β}
    {g₁ g₂ : β → OracleComp spec γ}
    {R : RelPost β β}
    (h12 : ⟪oa₁ >>= f₁ ~ oa₂ >>= f₂ | R⟫)
    (h23 : ∀ b₁ b₂, R b₁ b₂ → ⟪g₁ b₁ ~ g₂ b₂ | EqRel γ⟫) :
    (oa₁ >>= f₁ >>= g₁) =ᵈ (oa₂ >>= f₂ >>= g₂) := by
  rvcgen using R

end EqualInDistribution

/-! ## `by_dist` -/

section ByDist

example {game₁ game₂ : OracleComp spec Bool} {ε₁ ε₂ : ℝ≥0∞}
    (hbound : AdvBound game₁ ε₁) (htv : measureETVDist game₁ game₂ ≤ ε₂) :
    AdvBound game₂ (ε₁ + ε₂) := by
  by_dist ε₂
  · exact hbound
  · exact htv

end ByDist

/-! ## `rel_dist` -/

section RelDist

variable {ι : Type} {spec : OracleSpec ι} [∀ t, Finite (spec.Range t)]
variable [OracleSpec.AnswerMeasure spec]
variable {α : Type}

example {oa ob : OracleComp spec α} (h : oa =ᵈ ob) :
    ⟪oa ~ ob | EqRel α⟫ := by
  rel_dist
  exact h

end RelDist
