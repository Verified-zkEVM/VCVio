/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import VCVio.OracleComp.SimSemantics.StateT.Basic.Native
public import VCVio.OracleComp.EvalDist
public import VCVio.OracleComp.ProbComp

/-!
# Stateful oracle probability compatibility laws

Operational stateful-handler constructions are public through `StateT.Basic.Native`. This module
provides discrete probability equations for their compatibility interpretation.
-/

public section

universe u v w x

open OracleSpec

namespace OracleComp

variable {ι : Type*} {spec : OracleSpec ι}

open Option ENNReal
open scoped OracleSpec.PrimitiveQuery

section simulateQ_evalSPMF

variable [IsUniformSpec spec]

/-- If a `StateT` oracle implementation preserves distributions (each oracle query produces a
uniform distribution after discarding state), then `simulateQ` followed by `run'` preserves
`evalSPMF`. This is the key lemma for security proofs: it shows that stateful oracle
implementations (e.g. counting/logging oracles) don't change outcome probabilities. -/
lemma evalSPMF_simulateQ_run'_eq_evalSPMF {σ τ : Type u}
    (so : QueryImpl spec (StateT σ (OracleComp spec)))
    (h : ∀ (t : spec.Domain) (s : σ),
      𝒮[(so t).run' s] = OptionT.lift (PMF.uniformOfFintype (spec.Range t)))
    (s : σ) (oa : OracleComp spec τ) :
    𝒮[(simulateQ so oa).run' s] = 𝒮[oa] := by
  induction oa using OracleComp.inductionOn generalizing s with
  | pure x => simp
  | query_bind t mx ih =>
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.cont_query, id_map,
      OracleQuery.input_query, StateT.run'_eq, StateT.run_bind]
    rw [@map_bind (OracleComp spec), evalSPMF_bind]
    simp_rw [← StateT.run'_eq, ih]
    rw [← evalSPMF_bind, ← bind_map_left Prod.fst, ← StateT.run'_eq, evalSPMF_bind, h t s]
    exact (evalSPMF_query_bind t mx).symm

/-- If two stateful oracle implementations agree on the post-`run` distribution of every
query (`𝒮[(impl₁ t).run s] = 𝒮[(impl₂ t).run s]`), then simulating any computation through
either yields the same distribution on the run. -/
lemma evalSPMF_simulateQ_run_congr
    {ι' : Type} {spec' : OracleSpec ι'} {σ α : Type}
    (impl₁ impl₂ : QueryImpl spec' (StateT σ (OracleComp spec)))
    (h : ∀ (t : spec'.Domain) (s : σ),
      𝒮[(impl₁ t).run s] = 𝒮[(impl₂ t).run s])
    (comp : OracleComp spec' α) (s : σ) :
    𝒮[(simulateQ impl₁ comp).run s] =
      𝒮[(simulateQ impl₂ comp).run s] := by
  induction comp using OracleComp.inductionOn generalizing s <;> simp_all

end simulateQ_evalSPMF

end OracleComp

section probEventSimulateQ

open OracleComp

/-- If all outputs of the original `OracleComp` are successful (`some`) and satisfy `P`, then
the simulated `OptionT`-wrapped computation satisfies `P` with probability one. The success
hypothesis is at the level of the *original* computation's support, which bounds the simulated
support by `support_simulateQ_run'_subset`. -/
lemma OptionT.probEvent_eq_one_of_simulateQ_support
    {ι σ α : Type} {spec : OracleSpec ι}
    (impl : QueryImpl spec (StateT σ ProbComp))
    (oa : OracleComp spec (Option α)) (s₀ : σ) (P : α → Prop)
    (h : ∀ x ∈ support oa, ∃ a, x = some a ∧ P a) :
    Pr[P | OptionT.mk ((simulateQ impl oa).run' s₀)] = 1 := by
  let := Classical.decPred P
  rw [probEvent_eq_one_iff]
  constructor
  · rw [OptionT.probFailure_eq, OptionT.run_mk, probFailure_eq_zero, _root_.zero_add]
    exact probOutput_eq_zero_of_not_mem_support fun hnone ↦
      let ⟨_, hsome, _⟩ := h none (support_simulateQ_run'_subset impl oa s₀ hnone)
      by cases hsome
  · intro x hx
    rw [OptionT.mem_support_iff] at hx
    obtain ⟨a, ha, hP⟩ := h (some x) (support_simulateQ_run'_subset impl oa s₀ hx)
    cases ha
    exact hP

end probEventSimulateQ
