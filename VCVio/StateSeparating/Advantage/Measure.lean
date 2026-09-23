/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import VCVio.CryptoFoundations.SecExp.Measure
public import VCVio.OracleComp.SimSemantics.StateT.StateSeparating

/-!
# Measure-valued stateful-handler distinguishing advantage

Boolean observations define handler advantage, its triangle inequality, and congruence under
measure equality. The handler and its initial state remain explicit data.
-/

public section

universe uₑ

open OracleSpec OracleComp ProbComp ENNReal

namespace QueryImpl.Stateful

variable {ιₑ : Type uₑ} {E : OracleSpec.{uₑ, 0} ιₑ} {σ : Type}

/-! ## Bridging to `ProbComp` -/

/-- Run a probability-only stateful handler from an explicit initial state. -/
@[expose, reducible]
def runProb {α : Type} (h : QueryImpl.Stateful unifSpec E σ) (s₀ : σ)
    (A : OracleComp E α) : ProbComp α :=
  h.run s₀ A

/-- Run a probability-only stateful handler from the default initial state. -/
@[expose, reducible]
def runProb₀ {α : Type} [Inhabited σ] (h : QueryImpl.Stateful unifSpec E σ)
    (A : OracleComp E α) : ProbComp α :=
  h.run₀ A

@[simp]
lemma runProb_eq_run {α : Type} (h : QueryImpl.Stateful unifSpec E σ) (s₀ : σ)
    (A : OracleComp E α) :
    h.runProb s₀ A = h.run s₀ A := rfl

/-! ## Advantage and triangle inequality -/

/-- Boolean distinguishing advantage between two probability-only stateful
handlers, with explicit initial states. -/
@[expose]
noncomputable def advantage {σ₀ σ₁ : Type}
    (h₀ : QueryImpl.Stateful unifSpec E σ₀) (s₀ : σ₀)
    (h₁ : QueryImpl.Stateful unifSpec E σ₁) (s₁ : σ₁)
    (A : OracleComp E Bool) : ℝ≥0∞ :=
  𝒟[h₀.runProb s₀ A].boolDist 𝒟[h₁.runProb s₁ A]

/-- Boolean distinguishing advantage from default initial states. -/
@[expose]
noncomputable def advantage₀ {σ₀ σ₁ : Type} [Inhabited σ₀] [Inhabited σ₁]
    (h₀ : QueryImpl.Stateful unifSpec E σ₀)
    (h₁ : QueryImpl.Stateful unifSpec E σ₁)
    (A : OracleComp E Bool) : ℝ≥0∞ :=
  h₀.advantage default h₁ default A

@[simp]
lemma advantage_self (h : QueryImpl.Stateful unifSpec E σ) (s₀ : σ)
    (A : OracleComp E Bool) :
    h.advantage s₀ h s₀ A = 0 := by
  simp only [advantage, MeasureTheory.Measure.boolDist_self]

lemma advantage_symm {σ₀ σ₁ : Type}
    (h₀ : QueryImpl.Stateful unifSpec E σ₀) (s₀ : σ₀)
    (h₁ : QueryImpl.Stateful unifSpec E σ₁) (s₁ : σ₁)
    (A : OracleComp E Bool) :
    h₀.advantage s₀ h₁ s₁ A = h₁.advantage s₁ h₀ s₀ A := by
  exact MeasureTheory.Measure.boolDist_comm _ _

lemma advantage_triangle {σ₀ σ₁ σ₂ : Type}
    (h₀ : QueryImpl.Stateful unifSpec E σ₀) (s₀ : σ₀)
    (h₁ : QueryImpl.Stateful unifSpec E σ₁) (s₁ : σ₁)
    (h₂ : QueryImpl.Stateful unifSpec E σ₂) (s₂ : σ₂)
    (A : OracleComp E Bool) :
    h₀.advantage s₀ h₂ s₂ A ≤
      h₀.advantage s₀ h₁ s₁ A + h₁.advantage s₁ h₂ s₂ A :=
  MeasureTheory.Measure.boolDist_triangle _ _ _

/-- Equality of observed measures preserves the left distinguishing experiment. -/
lemma advantage_eq_of_evalDist_run_eq {σ₀ σ₀' σ₁ : Type}
    {h₀ : QueryImpl.Stateful unifSpec E σ₀} {s₀ : σ₀}
    {h₀' : QueryImpl.Stateful unifSpec E σ₀'} {s₀' : σ₀'}
    {h₁ : QueryImpl.Stateful unifSpec E σ₁} {s₁ : σ₁} {A : OracleComp E Bool}
    (h : 𝒟[h₀.run s₀ A] = 𝒟[h₀'.run s₀' A]) :
    h₀.advantage s₀ h₁ s₁ A = h₀'.advantage s₀' h₁ s₁ A := by
  simp [advantage, h]

/-- Equality of observed measures preserves the right distinguishing experiment. -/
lemma advantage_eq_of_evalDist_run_eq_right {σ₀ σ₁ σ₁' : Type}
    {h₀ : QueryImpl.Stateful unifSpec E σ₀} {s₀ : σ₀}
    {h₁ : QueryImpl.Stateful unifSpec E σ₁} {s₁ : σ₁}
    {h₁' : QueryImpl.Stateful unifSpec E σ₁'} {s₁' : σ₁'} {A : OracleComp E Bool}
    (h : 𝒟[h₁.run s₁ A] = 𝒟[h₁'.run s₁' A]) :
    h₀.advantage s₀ h₁ s₁ A = h₀.advantage s₀ h₁' s₁' A := by
  simp [advantage, h]

/-! ## Functoriality of `runProb` -/

lemma runProb_map {α β : Type} (h : QueryImpl.Stateful unifSpec E σ) (s₀ : σ)
    (f : α → β) (A : OracleComp E α) :
    h.runProb s₀ (f <$> A) = f <$> h.runProb s₀ A := by
  simp [QueryImpl.Stateful.run]

end QueryImpl.Stateful
