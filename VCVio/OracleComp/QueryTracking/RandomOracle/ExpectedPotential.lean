/-
Copyright (c) 2026 VCVio Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: VCVio Contributors
-/

module

public import VCVio.OracleComp.QueryTracking.RandomOracle.FreshAnswer
public import VCVio.OracleComp.EvalDist.Sum
import VCVio.EvalDist.ProbabilityBounds

/-!
# Charging an adaptive event to its expected potential

A clean state holds one unit of credit. A step that can lose that credit raises the
potential by at least its probability of doing so. Keeping credit and potential together
lets a caller stop after any reply and pay for the steps it actually took.
-/

public section

namespace OracleComp

open OracleSpec
open scoped ENNReal

variable {ι σ α : Type} {spec : OracleSpec ι}

private theorem lower_mean {γ : Type} (m : ProbComp γ) (f : γ → ℝ≥0∞) (k : ℝ≥0∞)
    (lower : ∀ z ∈ support m, k ≤ f z) : k ≤ ∑' z, Pr{let u ← m}[u = z] * f z := by
  have mass := tsum_prEvent_mul_of_const_on_support m (f := fun _ => k) (fun _ _ => rfl)
  rw [← mass]
  apply tsum_le_tsum
  intro z
  by_cases hz : z ∈ support m
  · exact mul_le_mul_of_nonneg_left (lower z hz) zero_le
  · simp [prEvent_eq_zero_of_not_mem_support m hz]

private theorem mean_credit {γ : Type} (m : ProbComp γ) (f : γ → ℝ≥0∞) (p : γ → Prop)
    [DecidablePred p] :
    (∑' z, Pr{let u ← m}[u = z] * (f z + if p z then 0 else 1)) =
      (∑' z, Pr{let u ← m}[u = z] * f z) + Pr{let z ← m}[¬p z] := by
  rw [prEvent_eq_tsum_ite, ← tsum_add]
  exact tsum_congr fun z => by by_cases h : p z <;> simp [h, mul_add]

private theorem run_lower (so : QueryImpl spec (StateT σ ProbComp)) (f : σ → ℝ≥0∞)
    (step : ∀ t s, f s ≤ ∑' z, Pr{let u ← (so t).run s}[u = z] * f z.2)
    (oa : OracleComp spec α) (s : σ) :
    f s ≤ ∑' z, Pr{let u ← (simulateQ so oa).run s}[u = z] * f z.2 := by
  induction oa using OracleComp.inductionOn generalizing s with
  | pure a => simp only [simulateQ_pure, StateT.run_pure, tsum_prEvent_pure_mul, le_refl]
  | query_bind t k ih =>
    rw [simulateQ_query_bind, StateT.run_bind, tsum_prEvent_bind_mul]
    exact (step t s).trans (tsum_le_tsum fun z => mul_le_mul_of_nonneg_left (ih z.1 z.2) zero_le)

/-- A charge paid on every supported response covers its conditional first-hit probability. -/
theorem expected_credit_of_increments (so : QueryImpl spec (StateT σ ProbComp))
    (P : σ → Prop) (Φ : σ → ℝ≥0∞)
    (mono : ∀ t s z, z ∈ support ((so t).run s) → Φ s ≤ Φ z.2)
    (step : ∀ t s, ¬P s → ∃ w,
      Pr{let z ← (so t).run s}[P z.2] ≤ w ∧
        ∀ z ∈ support ((so t).run s), w + Φ s ≤ Φ z.2)
    (oa : OracleComp spec α) (s : σ) [DecidablePred P] :
    Φ s + (if P s then 0 else 1) ≤ ∑' z, Pr{let u ← (simulateQ so oa).run s}[u = z] *
      (Φ z.2 + if P z.2 then 0 else 1) := by
  classical
  let f (u : σ) := Φ u + if P u then 0 else 1
  apply run_lower so f
  intro t u
  by_cases bad : P u
  · simp only [f, bad, ite_true, add_zero]
    exact lower_mean _ _ _ fun z hz => (mono t u z hz).trans le_self_add
  obtain ⟨w, hit, fee⟩ := step t u bad
  let m := (so t).run u
  have mass := prEvent_add_prEvent_not_eq_prEvent_true m (fun z => P z.2)
  rw [prEvent_true_eq_one] at mass
  change f u ≤ ∑' z, Pr{let v ← m}[v = z] * (Φ z.2 + if P z.2 then 0 else 1)
  rw [mean_credit]
  calc
    f u = Φ u + 1 := by simp [f, bad]
    _ = (Pr{let z ← m}[P z.2] + Φ u) + Pr{let z ← m}[¬P z.2] := by rw [← mass]; ac_rfl
    _ ≤ _ := add_le_add ((add_le_add hit le_rfl).trans (lower_mean m _ (w + Φ u) fee)) le_rfl

/-- Potential together with the credit for a clean state has nondecreasing expectation. -/
theorem IsPotentialStep.expected_credit {so : QueryImpl spec (StateT σ ProbComp)}
    {P : σ → Prop} {Φ : σ → ℝ≥0∞} (h : IsPotentialStep so P Φ)
    (oa : OracleComp spec α) (s : σ) [DecidablePred P] :
    Φ s + (if P s then 0 else 1) ≤ ∑' z, Pr{let u ← (simulateQ so oa).run s}[u = z] *
      (Φ z.2 + if P z.2 then 0 else 1) := by
  classical
  refine expected_credit_of_increments so P Φ h.mono (fun t u bad => ?_) oa s
  rcases h.step t u bad with ⟨a, v, det, safe⟩ | ⟨draw, upd, w, sampled, rate, fee⟩
  · refine ⟨0, ?_, fun z hz => (zero_add (Φ u)).trans_le (h.mono t u z hz)⟩
    simp [det, safe]
  · refine ⟨w, by simpa [sampled] using rate, ?_⟩
    intro z hz
    rw [sampled, support_map] at hz
    obtain ⟨a, _, rfl⟩ := hz
    exact fee a

/-- A terminal clean-state credit of at least one bounds the hit by the expected charge. -/
theorem prEvent_le_expected_of_credit {γ : Type} (m : ProbComp γ) (P : γ → Prop)
    (Φ : γ → ℝ≥0∞) [DecidablePred P]
    (credit : 1 ≤ ∑' z, Pr{let u ← m}[u = z] * (Φ z + if P z then 0 else 1)) :
    Pr{let z ← m}[P z] ≤ ∑' z, Pr{let u ← m}[u = z] * Φ z := by
  rw [mean_credit] at credit
  refine ENNReal.le_of_add_le_add_right (a := Pr{let z ← m}[¬P z])
    (ne_top_of_le_ne_top ENNReal.one_ne_top (prEvent_le_one _)) ?_
  rw [prEvent_add_prEvent_not_eq_prEvent_true, prEvent_true_eq_one]
  exact credit

/-- The probability of a terminal hit is at most the expected final potential from a clean start. -/
theorem IsPotentialStep.prEvent_le_expected {so : QueryImpl spec (StateT σ ProbComp)}
    {P : σ → Prop} {Φ : σ → ℝ≥0∞} (h : IsPotentialStep so P Φ)
    (oa : OracleComp spec α) (s : σ) (clean : ¬ P s) :
    Pr{let z ← (simulateQ so oa).run s}[P z.2] ≤
      ∑' z, Pr{let u ← (simulateQ so oa).run s}[u = z] * Φ z.2 := by
  classical
  apply prEvent_le_expected_of_credit
  exact (by simp [clean] : 1 ≤ Φ s + (if P s then 0 else 1)).trans (h.expected_credit oa s)

end OracleComp
