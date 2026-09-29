/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import VCVio.ProgramLogic.Relational.SimulateQ.UntilBad
public import VCVio.OracleComp.ProbComp.Basic

/-!
# Identical-until-bad canaries

The fundamental lemma needs no measurable structure on the simulation state and applies to
real-valued outputs with their Borel structure. It requires no discrete backend.
-/

public section

open OracleSpec OracleComp OracleComp.ProgramLogic.Relational

run_cmd do
  let env ← Lean.getEnv
  if env.contains `PMF then
    throwError "identical-until-bad unexpectedly imports PMF"

namespace VCVioTest.ProgramLogic.UntilBad

/-- A state carrying an unmeasured payload beside a bad flag: the handlers may disagree on the
step that sets the flag. -/
example (σ : Type) (impl₁ impl₂ : QueryImpl unifSpec (StateT ((ℝ → σ) × Bool) ProbComp))
    (oa : ProbComp ℝ) (s₀ : (ℝ → σ) × Bool)
    (h_agree : ∀ t s, ¬s.2 = true → ∀ q : unifSpec.Range t × ((ℝ → σ) × Bool) → Prop,
      Pr{let z ← (impl₁ t).run s}[q z ∧ ¬z.2.2 = true] =
        Pr{let z ← (impl₂ t).run s}[q z ∧ ¬z.2.2 = true])
    (h_mono₁ : ∀ t s, s.2 = true → ∀ z ∈ support ((impl₁ t).run s), z.2.2 = true)
    (h_mono₂ : ∀ t s, s.2 = true → ∀ z ∈ support ((impl₂ t).run s), z.2.2 = true) :
    measureETVDist ((simulateQ impl₁ oa).run' s₀) ((simulateQ impl₂ oa).run' s₀) ≤
      Pr{let z ← (simulateQ impl₁ oa).run s₀}[z.2.2 = true] :=
  measureETVDist_simulateQ_run'_le_prEvent_bad impl₁ impl₂ (fun s => s.2 = true) h_agree
    h_mono₁ h_mono₂ oa s₀

/-- Handlers that coincide off bad input states. -/
example (σ : Type) (impl₁ impl₂ : QueryImpl unifSpec (StateT σ ProbComp)) (bad : σ → Prop)
    (oa : ProbComp ℝ) (s₀ : σ) (h_agree : ∀ t s, ¬bad s → (impl₁ t).run s = (impl₂ t).run s)
    (h_mono₁ : ∀ t s, bad s → ∀ z ∈ support ((impl₁ t).run s), bad z.2)
    (h_mono₂ : ∀ t s, bad s → ∀ z ∈ support ((impl₂ t).run s), bad z.2) :
    measureETVDist ((simulateQ impl₁ oa).run' s₀) ((simulateQ impl₂ oa).run' s₀) ≤
      Pr{let z ← (simulateQ impl₁ oa).run s₀}[bad z.2] :=
  measureETVDist_simulateQ_run'_le_prEvent_bad_of_run_eq impl₁ impl₂ bad h_agree
    h_mono₁ h_mono₂ oa s₀

/-- Handlers within total variation `ε` on every query from a good state keep real-valued outputs
within `q * ε` plus the bad probability. -/
example (σ : Type) (impl₁ impl₂ : QueryImpl unifSpec (StateT σ ProbComp)) (bad : σ → Prop)
    (ε : ENNReal) (oa : ProbComp ℝ) (q : ℕ) (h_qb : oa.IsQueryBoundP (fun _ => True) q) (s₀ : σ)
    (h_step : ∀ t, True → ∀ s, ¬bad s →
      letI : MeasurableSpace (unifSpec.Range t × σ) := ⊤
      measureETVDist ((impl₁ t).run s) ((impl₂ t).run s) ≤ ε)
    (h_mono₁ : ∀ t s, bad s → ∀ z ∈ support ((impl₁ t).run s), bad z.2) :
    measureETVDist ((simulateQ impl₁ oa).run' s₀) ((simulateQ impl₂ oa).run' s₀) ≤
      q * ε + Pr{let z ← (simulateQ impl₁ oa).run s₀}[bad z.2] :=
  measureETVDist_simulateQ_run'_le_queryBoundP_mul_add_prEvent_bad impl₁ impl₂ bad _ h_step
    (fun _ h => absurd trivial h) h_mono₁ oa h_qb s₀

end VCVioTest.ProgramLogic.UntilBad
