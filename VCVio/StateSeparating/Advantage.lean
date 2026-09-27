/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import VCVio.StateSeparating.Advantage.Measure
public import VCVio.CryptoFoundations.SecExp

/-!
# Discrete probability compatibility for stateful handlers

The measure-valued advantage API is public through `Advantage.Measure`. These equations bridge
uniform discrete handler observations to the measure-valued distinguishing advantage.
-/

public section

universe uₑ

open OracleSpec OracleComp ProbComp

namespace QueryImpl.Stateful

variable {ιₑ : Type uₑ} {E : OracleSpec.{uₑ, 0} ιₑ} {σ : Type}

lemma advantage_eq_of_evalSPMF_runProb_eq {σ₀ σ₀' σ₁ : Type}
    {h₀ : QueryImpl.Stateful unifSpec E σ₀} {s₀ : σ₀}
    {h₀' : QueryImpl.Stateful unifSpec E σ₀'} {s₀' : σ₀'}
    {h₁ : QueryImpl.Stateful unifSpec E σ₁} {s₁ : σ₁}
    {A : OracleComp E Bool}
    (h_eq : 𝒮[h₀.runProb s₀ A] = 𝒮[h₀'.runProb s₀' A]) :
    h₀.advantage s₀ h₁ s₁ A = h₀'.advantage s₀' h₁ s₁ A := by
  have hm : 𝒟[h₀.runProb s₀ A] {true} = 𝒟[h₀'.runProb s₀' A] {true} := by
    simpa only [evalDist_apply_singleton] using probOutput_congr rfl h_eq
  rw [advantage, advantage, MeasureTheory.Measure.boolDist, MeasureTheory.Measure.boolDist, hm]

lemma advantage_eq_of_evalSPMF_runProb_eq_right {σ₀ σ₁ σ₁' : Type}
    {h₀ : QueryImpl.Stateful unifSpec E σ₀} {s₀ : σ₀}
    {h₁ : QueryImpl.Stateful unifSpec E σ₁} {s₁ : σ₁}
    {h₁' : QueryImpl.Stateful unifSpec E σ₁'} {s₁' : σ₁'}
    {A : OracleComp E Bool}
    (h_eq : 𝒮[h₁.runProb s₁ A] = 𝒮[h₁'.runProb s₁' A]) :
    h₀.advantage s₀ h₁ s₁ A = h₀.advantage s₀ h₁' s₁' A := by
  have hm : 𝒟[h₁.runProb s₁ A] {true} = 𝒟[h₁'.runProb s₁' A] {true} := by
    simpa only [evalDist_apply_singleton] using probOutput_congr rfl h_eq
  rw [advantage, advantage, MeasureTheory.Measure.boolDist, MeasureTheory.Measure.boolDist, hm]

/-! ## `evalSPMF` congruence for handlers -/

lemma simulateQ_evalSPMF_congr {α : Type}
    {h₁ h₂ : QueryImpl E ProbComp}
    (hh : ∀ (q : E.Domain), 𝒮[h₁ q] = 𝒮[h₂ q])
    (A : OracleComp E α) :
    𝒮[simulateQ h₁ A] = 𝒮[simulateQ h₂ A] := by
  induction A using OracleComp.inductionOn with
  | pure x => simp [simulateQ_pure]
  | query_bind t k ih =>
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.cont_query, OracleQuery.input_query,
      id_map, evalSPMF_bind]
    rw [hh t]
    exact bind_congr ih

lemma simulateQ_StateT_evalSPMF_congr {α : Type}
    {h₁ h₂ : QueryImpl E (StateT σ ProbComp)}
    (hh : ∀ (q : E.Domain) (s : σ),
      𝒮[(h₁ q).run s] = 𝒮[(h₂ q).run s])
    (A : OracleComp E α) (s : σ) :
    𝒮[(simulateQ h₁ A).run s] = 𝒮[(simulateQ h₂ A).run s] := by
  induction A using OracleComp.inductionOn generalizing s with
  | pure x => simp [simulateQ_pure, StateT.run_pure]
  | query_bind t k ih =>
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.cont_query, OracleQuery.input_query,
      id_map, StateT.run_bind, evalSPMF_bind]
    rw [hh t s]
    exact bind_congr fun p => ih p.1 p.2

lemma simulateQ_StateT_evalSPMF_congr_of_bij {α : Type} {σ₁ σ₂ : Type}
    (h₁ : QueryImpl E (StateT σ₁ ProbComp))
    (h₂ : QueryImpl E (StateT σ₂ ProbComp))
    (φ : σ₁ ≃ σ₂)
    (hh : ∀ (q : E.Domain) (s : σ₁),
      𝒮[(h₁ q).run s] =
      𝒮[Prod.map id φ.symm <$> (h₂ q).run (φ s)])
    (A : OracleComp E α) (s : σ₁) :
    𝒮[(simulateQ h₁ A).run s] =
    𝒮[Prod.map id φ.symm <$> (simulateQ h₂ A).run (φ s)] := by
  induction A using OracleComp.inductionOn generalizing s with
  | pure x => simp
  | query_bind t k ih =>
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.cont_query, OracleQuery.input_query,
      id_map, StateT.run_bind, map_bind, evalSPMF_bind, hh t s, monad_norm]
    refine bind_congr fun ⟨x, s'⟩ => ?_
    simpa [Equiv.apply_symm_apply, Function.comp_def] using ih x (φ.symm s')


end QueryImpl.Stateful
