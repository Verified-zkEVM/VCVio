/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module
public import VCVio.OracleComp.QueryTracking.RandomOracle.FreshAnswer

/-! # First-fire probability bounded by expected terminal potential -/

public section
open OracleComp OracleSpec MeasureTheory
open scoped ENNReal

namespace OracleComp

/-- A pathwise monotone potential has expectation at least its starting value. -/
private theorem initial_le_expected_monotone_potential
    {ι σ α : Type} {spec : OracleSpec ι}
    (handler : QueryImpl spec (StateT σ ProbComp)) (potential : σ → ℝ≥0∞)
    (monotone : ∀ (t : spec.Domain) (s : σ),
      ∀ z ∈ support ((handler t).run s), potential s ≤ potential z.2)
    (program : OracleComp spec α) (state : σ) :
    potential state ≤
      ∫⁻ r, r ∂𝒟[(fun z => potential z.2) <$> (simulateQ handler program).run state] := by
  let _ : MeasurableSpace (α × σ) := ⊤
  rw [lintegral_id_evalDist_map]
  calc
    potential state = ∫⁻ _z : α × σ, potential state
        ∂𝒟[(simulateQ handler program).run state] := by
      rw [lintegral_const, measure_univ, mul_one]
    _ ≤ _ := lintegral_mono_ae
      (evalDist.ae_of_forall_mem_support _ _ MeasurableSet.of_discrete
        (fun _ hz =>
          le_of_mem_support_run_simulateQ_of_step handler potential monotone program state hz))

/-- A funded first-fire hazard costs at most the expected increase of its potential. -/
theorem prEvent_run_add_initial_potential_le_expected_final
    {ι σ α : Type} {spec : OracleSpec ι}
    (handler : QueryImpl spec (StateT σ ProbComp))
    (bad : σ → Prop) (potential : σ → ℝ≥0∞)
    (charged : IsPotentialStep handler bad potential)
    (program : OracleComp spec α) (state : σ) (initiallyGood : ¬bad state) :
    Pr{let z ← (simulateQ handler program).run state}[bad z.2] + potential state ≤
      ∫⁻ r, r ∂𝒟[(fun z => potential z.2) <$> (simulateQ handler program).run state] :=
 by
  classical
  induction program using OracleComp.inductionOn generalizing state with
  | pure value =>
    simp [initiallyGood]
  | query_bind queried next ih =>
    rcases charged.step queried state initiallyGood with
      ⟨answer, post, step, postGood⟩ | ⟨sampler, update, weight, step, fireBound, funding⟩
    · rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, step, pure_bind]
      have grows : potential state ≤ potential post :=
        charged.mono queried state (answer, post)
          (by rw [step, support_pure]; exact Set.mem_singleton _)
      exact (add_le_add le_rfl grows).trans (ih answer post postGood)
    · rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, step, bind_map_left]
      let _ : MeasurableSpace (spec.Range queried) := ⊤
      let continuation (answer : spec.Range queried) :=
        (simulateQ handler (next answer)).run (update answer)
      let futureBad (answer : spec.Range queried) : ℝ≥0∞ :=
        Pr{let z ← continuation answer}[bad z.2]
      let finalPotential (answer : spec.Range queried) : ℝ≥0∞ :=
        ∫⁻ r, r ∂𝒟[(fun z => potential z.2) <$> continuation answer]
      let goodFuture (answer : spec.Range queried) : ℝ≥0∞ :=
        if bad (update answer) then 0 else futureBad answer
      have indicatorIntegral :
          (∫⁻ answer, (if bad (update answer) then (1 : ℝ≥0∞) else 0) ∂𝒟[sampler]) =
            Pr{let answer ← sampler}[bad (update answer)] := by
        change (∫⁻ answer, ({answer | bad (update answer)} : Set _).indicator
          (fun _ => (1 : ℝ≥0∞)) answer ∂𝒟[sampler]) = _
        rw [lintegral_indicator_const MeasurableSet.of_discrete, one_mul,
          prEvent_eq_evalDist_of_discrete]
      have badUpper : (∫⁻ answer, futureBad answer ∂𝒟[sampler]) ≤
          weight + ∫⁻ answer, goodFuture answer ∂𝒟[sampler] := by
        calc
          _ ≤ ∫⁻ answer, (if bad (update answer) then (1 : ℝ≥0∞) else 0) +
              goodFuture answer ∂𝒟[sampler] := by
            apply lintegral_mono
            intro answer
            by_cases postBad : bad (update answer)
            · simpa only [goodFuture, postBad, ↓reduceIte, add_zero] using
                (prEvent_le_one ((fun z => bad z.2) <$> continuation answer))
            · simp only [goodFuture, postBad, ↓reduceIte, zero_add, le_refl]
          _ = Pr{let answer ← sampler}[bad (update answer)] +
              ∫⁻ answer, goodFuture answer ∂𝒟[sampler] := by
            rw [lintegral_add_left Measurable.of_discrete, indicatorIntegral]
          _ ≤ _ := add_le_add fireBound le_rfl
      have chargeLower : potential state + weight +
          (∫⁻ answer, goodFuture answer ∂𝒟[sampler]) ≤
            ∫⁻ answer, finalPotential answer ∂𝒟[sampler] := by
        calc
          _ = ∫⁻ answer, (potential state + weight) + goodFuture answer ∂𝒟[sampler] := by
            rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one]
          _ ≤ _ := by
            apply lintegral_mono
            intro answer
            by_cases postBad : bad (update answer)
            · calc
                _ = weight + potential state := by simp [goodFuture, postBad, add_comm]
                _ ≤ potential (update answer) := funding answer
                _ ≤ _ := initial_le_expected_monotone_potential handler potential
                    charged.mono (next answer) (update answer)
            · calc
                _ = futureBad answer + (weight + potential state) := by
                  simp only [goodFuture, postBad, ↓reduceIte]
                  ac_rfl
                _ ≤ futureBad answer + potential (update answer) :=
                  add_le_add le_rfl (funding answer)
                _ ≤ _ := ih answer (update answer) postBad
      rw [prEvent_bind_eq_lintegral_of_discrete, lintegral_id_evalDist_map_bind,
        lintegral_id_evalDist_map]
      change (∫⁻ answer, futureBad answer ∂𝒟[sampler]) + potential state ≤
        ∫⁻ answer, finalPotential answer ∂𝒟[sampler]
      calc
        _ ≤ (weight + ∫⁻ answer, goodFuture answer ∂𝒟[sampler]) + potential state :=
          add_le_add badUpper le_rfl
        _ = potential state + weight + ∫⁻ answer, goodFuture answer ∂𝒟[sampler] := by
          ac_rfl
        _ ≤ _ := chargeLower

end OracleComp
#print axioms OracleComp.prEvent_run_add_initial_potential_le_expected_final
