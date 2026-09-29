/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import VCVio.ProgramLogic.Relational.SimulateQ
public import VCVio.StateSeparating.Advantage.Measure

/-!
# State-separating handlers: identical-until-bad

Identical-until-bad wrappers for `QueryImpl.Stateful` handlers whose state is
of the form `σ × Bool`, with the Boolean component acting as the bad flag.
-/

@[expose] public section

open ENNReal MeasureTheory OracleSpec OracleComp ProbComp
open OracleComp.ProgramLogic.Relational

namespace QueryImpl.Stateful

variable {ιₑ : Type} {E : OracleSpec.{0, 0} ιₑ} {σ : Type}

/-- A stateful handler preserves a state invariant as long as the bad flag has not fired. -/
def PreservesNoBadInvariant (h : QueryImpl.Stateful unifSpec E (σ × Bool))
    (Inv : σ → Prop) : Prop :=
  ∀ (t : E.Domain) (p : σ × Bool), p.2 = false → Inv p.1 →
    ∀ z ∈ support ((h t).run p), Inv z.2.1

/-- The Boolean distinguishing advantage is at most the total variation between the two runs. -/
theorem advantage_le_measureETVDist {σ₀ σ₁ : Type}
    (h₀ : QueryImpl.Stateful unifSpec E σ₀) (s₀ : σ₀)
    (h₁ : QueryImpl.Stateful unifSpec E σ₁) (s₁ : σ₁) (A : OracleComp E Bool) :
    h₀.advantage s₀ h₁ s₁ A ≤ measureETVDist (h₀.runProb s₀ A) (h₁.runProb s₁ A) :=
  measure_absDiff_apply_le_measureETVDist _ _ (measurableSet_singleton true)

/-- State-dependent ε-perturbed identical-until-bad with output bad flag. -/
theorem advantage_le_expectedQuerySlack_add_prEvent_bad
    (h₀ h₁ : QueryImpl.Stateful unifSpec E (σ × Bool))
    (s_init : σ)
    (chargedQuery : E.Domain → Prop) [DecidablePred chargedQuery]
    (querySlack : σ → ℝ≥0∞)
    (h_step_charged : ∀ (t : E.Domain), chargedQuery t → ∀ (s : σ),
      letI : MeasurableSpace (E.Range t × σ × Bool) := ⊤
      measureETVDist ((h₀ t).run (s, false)) ((h₁ t).run (s, false)) ≤ querySlack s)
    (h_step_uncharged : ∀ (t : E.Domain), ¬ chargedQuery t → ∀ (s : σ),
      (h₀ t).run (s, false) = (h₁ t).run (s, false))
    (h_mono₀ : ∀ (t : E.Domain) (p : σ × Bool), p.2 = true →
      ∀ z ∈ support ((h₀ t).run p), z.2.2 = true)
    (A : OracleComp E Bool) {queryBudget : ℕ}
    (h_bound : A.IsQueryBoundP chargedQuery queryBudget) :
    h₀.advantage (s_init, false) h₁ (s_init, false) A
      ≤ expectedQuerySlack h₀ chargedQuery querySlack A queryBudget (s_init, false)
        + Pr{let z ← (simulateQ h₀ A).run (s_init, false)}[z.2.2 = true] :=
  (advantage_le_measureETVDist h₀ _ h₁ _ A).trans
    (measureETVDist_simulateQ_run'_le_expectedQuerySlack_add_prEvent_bad h₀ h₁ chargedQuery
      querySlack h_step_charged h_step_uncharged h_mono₀ A h_bound (s_init, false))

/-- Constant-ε identical-until-bad with output bad flag. -/
theorem advantage_le_queryBound_mul_slack_add_prEvent_bad
    (h₀ h₁ : QueryImpl.Stateful unifSpec E (σ × Bool))
    (s_init : σ)
    (chargedQuery : E.Domain → Prop) [DecidablePred chargedQuery]
    (querySlack : ℝ≥0∞)
    (h_step_charged : ∀ (t : E.Domain), chargedQuery t → ∀ (s : σ),
      letI : MeasurableSpace (E.Range t × σ × Bool) := ⊤
      measureETVDist ((h₀ t).run (s, false)) ((h₁ t).run (s, false)) ≤ querySlack)
    (h_step_uncharged : ∀ (t : E.Domain), ¬ chargedQuery t → ∀ (s : σ),
      (h₀ t).run (s, false) = (h₁ t).run (s, false))
    (h_mono₀ : ∀ (t : E.Domain) (p : σ × Bool), p.2 = true →
      ∀ z ∈ support ((h₀ t).run p), z.2.2 = true)
    (A : OracleComp E Bool) {queryBudget : ℕ}
    (h_bound : A.IsQueryBoundP chargedQuery queryBudget) :
    h₀.advantage (s_init, false) h₁ (s_init, false) A
      ≤ queryBudget * querySlack
        + Pr{let z ← (simulateQ h₀ A).run (s_init, false)}[z.2.2 = true] := by
  refine (advantage_le_expectedQuerySlack_add_prEvent_bad
      h₀ h₁ s_init chargedQuery (fun _ => querySlack)
      h_step_charged h_step_uncharged h_mono₀ A h_bound).trans ?_
  gcongr
  exact expectedQuerySlack_const_le_queryBudget_mul h₀ chargedQuery querySlack A h_bound
    (s_init, false)

/-! ### Invariant-gated variants -/

/-- Invariant-gated state-dependent ε-perturbed identical-until-bad.

The costly-step total-variation hypothesis is required only for states satisfying `Inv`.
The generated query-slack function charges the intended `ε s` on invariant states and
the conservative fallback cost `1` elsewhere. -/
theorem advantage_le_expectedQuerySlack_add_prEvent_bad_of_inv
    (h₀ h₁ : QueryImpl.Stateful unifSpec E (σ × Bool))
    (s_init : σ)
    (Inv : σ → Prop) [DecidablePred Inv]
    (chargedQuery : E.Domain → Prop) [DecidablePred chargedQuery]
    (querySlack : σ → ℝ≥0∞)
    (h_step_charged : ∀ (t : E.Domain), chargedQuery t → ∀ (s : σ), Inv s →
      letI : MeasurableSpace (E.Range t × σ × Bool) := ⊤
      measureETVDist ((h₀ t).run (s, false)) ((h₁ t).run (s, false)) ≤ querySlack s)
    (h_step_uncharged : ∀ (t : E.Domain), ¬ chargedQuery t → ∀ (s : σ),
      (h₀ t).run (s, false) = (h₁ t).run (s, false))
    (h_mono₀ : ∀ (t : E.Domain) (p : σ × Bool), p.2 = true →
      ∀ z ∈ support ((h₀ t).run p), z.2.2 = true)
    (A : OracleComp E Bool) {queryBudget : ℕ}
    (h_bound : A.IsQueryBoundP chargedQuery queryBudget) :
    h₀.advantage (s_init, false) h₁ (s_init, false) A
      ≤ expectedQuerySlack h₀ chargedQuery
          (fun s => if Inv s then querySlack s else 1) A queryBudget (s_init, false)
        + Pr{let z ← (simulateQ h₀ A).run (s_init, false)}[z.2.2 = true] := by
  refine advantage_le_expectedQuerySlack_add_prEvent_bad
    h₀ h₁ s_init chargedQuery (fun s => if Inv s then querySlack s else 1) ?_
    h_step_uncharged h_mono₀ A h_bound
  intro t hSt s
  by_cases hs : Inv s
  · simpa only [hs, ↓reduceIte] using h_step_charged t hSt s hs
  · let : MeasurableSpace (E.Range t × σ × Bool) := ⊤
    simp only [hs, ↓reduceIte]
    exact measureETVDist_le_one _ _

/-- Invariant-preserving state-dependent ε-perturbed identical-until-bad.

If the real handler preserves `Inv` from the initial no-bad state, then the
fallback branch in the invariant-gated cost is unreachable, so the final
expected-cost term uses the tight query-slack function `ε`. -/
theorem advantage_le_expectedQuerySlack_add_prEvent_bad_of_inv_preserved
    (h₀ h₁ : QueryImpl.Stateful unifSpec E (σ × Bool))
    (s_init : σ)
    (Inv : σ → Prop)
    (h_init_inv : Inv s_init)
    (h_pres : h₀.PreservesNoBadInvariant Inv)
    (chargedQuery : E.Domain → Prop) [DecidablePred chargedQuery]
    (querySlack : σ → ℝ≥0∞)
    (h_step_charged : ∀ (t : E.Domain), chargedQuery t → ∀ (s : σ), Inv s →
      letI : MeasurableSpace (E.Range t × σ × Bool) := ⊤
      measureETVDist ((h₀ t).run (s, false)) ((h₁ t).run (s, false)) ≤ querySlack s)
    (h_step_uncharged : ∀ (t : E.Domain), ¬ chargedQuery t → ∀ (s : σ),
      (h₀ t).run (s, false) = (h₁ t).run (s, false))
    (h_mono₀ : ∀ (t : E.Domain) (p : σ × Bool), p.2 = true →
      ∀ z ∈ support ((h₀ t).run p), z.2.2 = true)
    (A : OracleComp E Bool) {queryBudget : ℕ}
    (h_bound : A.IsQueryBoundP chargedQuery queryBudget) :
    h₀.advantage (s_init, false) h₁ (s_init, false) A
      ≤ expectedQuerySlack h₀ chargedQuery querySlack A queryBudget (s_init, false)
        + Pr{let z ← (simulateQ h₀ A).run (s_init, false)}[z.2.2 = true] := by
  classical
  have h_cost_eq :
      expectedQuerySlack h₀ chargedQuery (fun s => if Inv s then querySlack s else 1)
          A queryBudget (s_init, false)
        = expectedQuerySlack h₀ chargedQuery querySlack A queryBudget (s_init, false) :=
    expectedQuerySlack_eq_of_inv h₀ chargedQuery Inv
      (ε := fun s => if Inv s then querySlack s else 1) (ε' := querySlack)
      (fun s hs => by simp [hs]) h_pres A queryBudget (s_init, false)
      (fun _ => h_init_inv)
  rw [← h_cost_eq]
  exact advantage_le_expectedQuerySlack_add_prEvent_bad_of_inv
    h₀ h₁ s_init Inv chargedQuery querySlack h_step_charged h_step_uncharged
      h_mono₀ A h_bound

end QueryImpl.Stateful
