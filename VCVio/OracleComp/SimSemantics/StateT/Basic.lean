/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import VCVio.OracleComp.SimSemantics.StateT.Basic.Native
public import VCVio.OracleComp.EvalDist
public import VCVio.OracleComp.ProbComp.Basic
public import VCVio.OracleComp.Constructions.UniformFinMeasure

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

end probEventSimulateQ
