/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import VCVio.EvalDist.MeasureTVDist.Event
public import VCVio.OracleComp.EvalDist.Measure
public import VCVio.OracleComp.SimSemantics.StateT.Basic.Native

/-!
# Identical until bad for simulations

Two stateful oracle implementations that give every event the same probability on steps that
start and end in good states, and that never leave the bad states, produce simulations that agree
on every event away from a bad final state. Their outputs are then within the probability of
ending in a bad state in total variation: the fundamental lemma of game playing.

The agreement is only required on good-to-good steps, so the two implementations may disagree on
the step that enters a bad state, as when a bad flag is set by the step that fires it. Agreement
off bad input states, whether as equal runs or equal output measures, is a special case.
-/

public section

open MeasureTheory OracleSpec OracleComp
open scoped ENNReal OracleSpec.PrimitiveQuery

universe u u'

namespace OracleComp.ProgramLogic.Relational

variable {ι : Type u} {spec : OracleSpec.{u, 0} ι} {ι' : Type u'} {spec' : OracleSpec.{u', 0} ι'}
  {α σ : Type}

/-- A simulation started from a bad state ends in a bad state whenever its handler keeps bad
states bad. -/
theorem forall_mem_support_simulateQ_run_of_bad
    (impl : QueryImpl spec (StateT σ (OracleComp spec'))) (bad : σ → Prop)
    (h_mono : ∀ t s, bad s → ∀ z ∈ support ((impl t).run s), bad z.2)
    (oa : OracleComp spec α) {s₀ : σ} (h_bad : bad s₀) :
    ∀ z ∈ support ((simulateQ impl oa).run s₀), bad z.2 := by
  induction oa using OracleComp.inductionOn generalizing s₀ with
  | pure a =>
    intro z hz
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    subst hz
    exact h_bad
  | query_bind t k ih =>
    intro z hz
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
      OracleQuery.cont_query, id_map, StateT.run_bind, mem_support_bind_iff] at hz
    obtain ⟨us, hus, hz⟩ := hz
    exact ih us.1 (h_mono t s₀ h_bad us hus) z hz

variable [∀ t, MeasurableSpace (spec'.Range t)] [∀ t, DiscreteMeasurableSpace (spec'.Range t)]
  [IsMeasureSpec spec']

/-- Two simulations whose handlers agree on good-to-good steps and keep bad states bad give every
event the same probability away from a bad final state. -/
theorem prEvent_simulateQ_run_and_not_bad_eq
    (impl₁ impl₂ : QueryImpl spec (StateT σ (OracleComp spec'))) (bad : σ → Prop)
    (h_agree : ∀ t s, ¬bad s → ∀ q : spec.Range t × σ → Prop,
      Pr{let z ← (impl₁ t).run s}[q z ∧ ¬bad z.2] =
        Pr{let z ← (impl₂ t).run s}[q z ∧ ¬bad z.2])
    (h_mono₁ : ∀ t s, bad s → ∀ z ∈ support ((impl₁ t).run s), bad z.2)
    (h_mono₂ : ∀ t s, bad s → ∀ z ∈ support ((impl₂ t).run s), bad z.2)
    (oa : OracleComp spec α) (s₀ : σ) (p : α × σ → Prop) :
    Pr{let z ← (simulateQ impl₁ oa).run s₀}[p z ∧ ¬bad z.2] =
      Pr{let z ← (simulateQ impl₂ oa).run s₀}[p z ∧ ¬bad z.2] := by
  induction oa using OracleComp.inductionOn generalizing s₀ with
  | pure a => simp only [simulateQ_pure, StateT.run_pure]
  | query_bind t k ih =>
    by_cases hb : bad s₀
    · rw [prEvent_eq_zero_of_forall_mem_support _ _ fun z hz h =>
          h.2 (forall_mem_support_simulateQ_run_of_bad impl₁ bad h_mono₁ _ hb z hz),
        prEvent_eq_zero_of_forall_mem_support _ _ fun z hz h =>
          h.2 (forall_mem_support_simulateQ_run_of_bad impl₂ bad h_mono₂ _ hb z hz)]
    · simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
        OracleQuery.cont_query, id_map, StateT.run_bind]
      let : MeasurableSpace (spec.Range t × σ) := ⊤
      let G : Set (spec.Range t × σ) := {us | ¬bad us.2}
      have hcont (impl : QueryImpl spec (StateT σ (OracleComp spec')))
          (h_mono : ∀ t s, bad s → ∀ z ∈ support ((impl t).run s), bad z.2)
          (us : spec.Range t × σ) :
          Pr{let z ← (simulateQ impl (k us.1)).run us.2}[p z ∧ ¬bad z.2] =
            G.indicator (fun us =>
              Pr{let z ← (simulateQ impl (k us.1)).run us.2}[p z ∧ ¬bad z.2]) us := by
        by_cases hus : bad us.2
        · rw [Set.indicator_of_notMem (by simpa [G] using hus),
            prEvent_eq_zero_of_forall_mem_support _ _ fun z hz h =>
              h.2 (forall_mem_support_simulateQ_run_of_bad impl bad h_mono _ hus z hz)]
        · rw [Set.indicator_of_mem (by simpa [G] using hus)]
      have hrestrict : 𝒟[(impl₁ t).run s₀].restrict G = 𝒟[(impl₂ t).run s₀].restrict G := by
        refine Measure.ext fun A hA => ?_
        rw [Measure.restrict_apply hA, Measure.restrict_apply hA]
        change 𝒟[(impl₁ t).run s₀] {z | z ∈ A ∧ ¬bad z.2} =
          𝒟[(impl₂ t).run s₀] {z | z ∈ A ∧ ¬bad z.2}
        rw [← prEvent_eq_evalDist_of_discrete, ← prEvent_eq_evalDist_of_discrete]
        exact h_agree t s₀ hb (· ∈ A)
      rw [prEvent_bind_eq_lintegral_of_discrete, prEvent_bind_eq_lintegral_of_discrete]
      calc ∫⁻ us, Pr{let z ← (simulateQ impl₁ (k us.1)).run us.2}[p z ∧ ¬bad z.2]
            ∂𝒟[(impl₁ t).run s₀]
          = ∫⁻ us, G.indicator (fun us =>
              Pr{let z ← (simulateQ impl₂ (k us.1)).run us.2}[p z ∧ ¬bad z.2]) us
              ∂𝒟[(impl₁ t).run s₀] := by
            refine lintegral_congr fun us => ?_
            rw [hcont impl₁ h_mono₁ us]
            by_cases hus : us ∈ G
            · rw [Set.indicator_of_mem hus, Set.indicator_of_mem hus, ih us.1 us.2]
            · rw [Set.indicator_of_notMem hus, Set.indicator_of_notMem hus]
        _ = ∫⁻ us, Pr{let z ← (simulateQ impl₂ (k us.1)).run us.2}[p z ∧ ¬bad z.2]
              ∂(𝒟[(impl₁ t).run s₀].restrict G) :=
            lintegral_indicator MeasurableSet.of_discrete _
        _ = ∫⁻ us, Pr{let z ← (simulateQ impl₂ (k us.1)).run us.2}[p z ∧ ¬bad z.2]
              ∂(𝒟[(impl₂ t).run s₀].restrict G) := by rw [hrestrict]
        _ = ∫⁻ us, Pr{let z ← (simulateQ impl₂ (k us.1)).run us.2}[p z ∧ ¬bad z.2]
              ∂𝒟[(impl₂ t).run s₀] := by
            rw [← lintegral_indicator MeasurableSet.of_discrete]
            exact lintegral_congr fun us => (hcont impl₂ h_mono₂ us).symm

/-- Two simulations whose handlers agree on good-to-good steps and keep bad states bad end in a
bad state with the same probability. -/
theorem prEvent_simulateQ_run_bad_eq
    (impl₁ impl₂ : QueryImpl spec (StateT σ (OracleComp spec'))) (bad : σ → Prop)
    (h_agree : ∀ t s, ¬bad s → ∀ q : spec.Range t × σ → Prop,
      Pr{let z ← (impl₁ t).run s}[q z ∧ ¬bad z.2] =
        Pr{let z ← (impl₂ t).run s}[q z ∧ ¬bad z.2])
    (h_mono₁ : ∀ t s, bad s → ∀ z ∈ support ((impl₁ t).run s), bad z.2)
    (h_mono₂ : ∀ t s, bad s → ∀ z ∈ support ((impl₂ t).run s), bad z.2)
    (oa : OracleComp spec α) (s₀ : σ) :
    Pr{let z ← (simulateQ impl₁ oa).run s₀}[bad z.2] =
      Pr{let z ← (simulateQ impl₂ oa).run s₀}[bad z.2] := by
  have hgood := prEvent_simulateQ_run_and_not_bad_eq impl₁ impl₂ bad h_agree h_mono₁ h_mono₂
    oa s₀ fun _ => True
  simp only [true_and] at hgood
  have h₁ := prEvent_add_prEvent_not_eq_prEvent_true ((simulateQ impl₁ oa).run s₀)
    fun z => bad z.2
  have h₂ := prEvent_add_prEvent_not_eq_prEvent_true ((simulateQ impl₂ oa).run s₀)
    fun z => bad z.2
  rw [OracleComp.prEvent_true_eq_one] at h₁ h₂
  have hne : Pr{let z ← (simulateQ impl₂ oa).run s₀}[¬bad z.2] ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top (prEvent_le_one _ _)
  rw [ENNReal.eq_sub_of_add_eq (hgood ▸ hne) h₁, ENNReal.eq_sub_of_add_eq hne h₂, hgood]

/-- Two simulations whose handlers agree on good-to-good steps and keep bad states bad have
output-state pairs within the probability of ending in a bad state in total variation. -/
theorem measureETVDist_simulateQ_run_le_prEvent_bad [MeasurableSpace (α × σ)]
    (impl₁ impl₂ : QueryImpl spec (StateT σ (OracleComp spec'))) (bad : σ → Prop)
    (h_agree : ∀ t s, ¬bad s → ∀ q : spec.Range t × σ → Prop,
      Pr{let z ← (impl₁ t).run s}[q z ∧ ¬bad z.2] =
        Pr{let z ← (impl₂ t).run s}[q z ∧ ¬bad z.2])
    (h_mono₁ : ∀ t s, bad s → ∀ z ∈ support ((impl₁ t).run s), bad z.2)
    (h_mono₂ : ∀ t s, bad s → ∀ z ∈ support ((impl₂ t).run s), bad z.2)
    (oa : OracleComp spec α) (s₀ : σ) :
    measureETVDist ((simulateQ impl₁ oa).run s₀) ((simulateQ impl₂ oa).run s₀) ≤
      Pr{let z ← (simulateQ impl₁ oa).run s₀}[bad z.2] := by
  have h := measureETVDist_map_le_prEvent_of_agree ((simulateQ impl₁ oa).run s₀)
    ((simulateQ impl₂ oa).run s₀) id (fun z => bad z.2)
    (prEvent_simulateQ_run_and_not_bad_eq impl₁ impl₂ bad h_agree h_mono₁ h_mono₂ oa s₀)
    (prEvent_simulateQ_run_bad_eq impl₁ impl₂ bad h_agree h_mono₁ h_mono₂ oa s₀).ge
  rwa [id_map, id_map] at h

/-- **Identical until bad.** Two simulations whose handlers agree on good-to-good steps and keep
bad states bad have outputs within the probability of ending in a bad state in total variation.

Both handlers must keep bad states bad: otherwise one could enter a bad state, diverge, and
return to a good state, giving different outputs with no final bad mass. -/
theorem measureETVDist_simulateQ_run'_le_prEvent_bad [MeasurableSpace α]
    (impl₁ impl₂ : QueryImpl spec (StateT σ (OracleComp spec'))) (bad : σ → Prop)
    (h_agree : ∀ t s, ¬bad s → ∀ q : spec.Range t × σ → Prop,
      Pr{let z ← (impl₁ t).run s}[q z ∧ ¬bad z.2] =
        Pr{let z ← (impl₂ t).run s}[q z ∧ ¬bad z.2])
    (h_mono₁ : ∀ t s, bad s → ∀ z ∈ support ((impl₁ t).run s), bad z.2)
    (h_mono₂ : ∀ t s, bad s → ∀ z ∈ support ((impl₂ t).run s), bad z.2)
    (oa : OracleComp spec α) (s₀ : σ) :
    measureETVDist ((simulateQ impl₁ oa).run' s₀) ((simulateQ impl₂ oa).run' s₀) ≤
      Pr{let z ← (simulateQ impl₁ oa).run s₀}[bad z.2] :=
  measureETVDist_map_le_prEvent_of_agree _ _ Prod.fst (fun z => bad z.2)
    (prEvent_simulateQ_run_and_not_bad_eq impl₁ impl₂ bad h_agree h_mono₁ h_mono₂ oa s₀)
    (prEvent_simulateQ_run_bad_eq impl₁ impl₂ bad h_agree h_mono₁ h_mono₂ oa s₀).ge

/-- **Identical until bad** for handlers whose runs coincide off bad input states. -/
theorem measureETVDist_simulateQ_run'_le_prEvent_bad_of_run_eq [MeasurableSpace α]
    (impl₁ impl₂ : QueryImpl spec (StateT σ (OracleComp spec'))) (bad : σ → Prop)
    (h_agree : ∀ t s, ¬bad s → (impl₁ t).run s = (impl₂ t).run s)
    (h_mono₁ : ∀ t s, bad s → ∀ z ∈ support ((impl₁ t).run s), bad z.2)
    (h_mono₂ : ∀ t s, bad s → ∀ z ∈ support ((impl₂ t).run s), bad z.2)
    (oa : OracleComp spec α) (s₀ : σ) :
    measureETVDist ((simulateQ impl₁ oa).run' s₀) ((simulateQ impl₂ oa).run' s₀) ≤
      Pr{let z ← (simulateQ impl₁ oa).run s₀}[bad z.2] :=
  measureETVDist_simulateQ_run'_le_prEvent_bad impl₁ impl₂ bad
    (fun t s hs q => by rw [h_agree t s hs]) h_mono₁ h_mono₂ oa s₀

/-- **Identical until bad** for handlers whose output measures coincide off bad input states. -/
theorem measureETVDist_simulateQ_run'_le_prEvent_bad_of_evalDist_eq [MeasurableSpace α]
    (impl₁ impl₂ : QueryImpl spec (StateT σ (OracleComp spec'))) (bad : σ → Prop)
    (h_agree : ∀ t s, ¬bad s → letI : MeasurableSpace (spec.Range t × σ) := ⊤;
      𝒟[(impl₁ t).run s] = 𝒟[(impl₂ t).run s])
    (h_mono₁ : ∀ t s, bad s → ∀ z ∈ support ((impl₁ t).run s), bad z.2)
    (h_mono₂ : ∀ t s, bad s → ∀ z ∈ support ((impl₂ t).run s), bad z.2)
    (oa : OracleComp spec α) (s₀ : σ) :
    measureETVDist ((simulateQ impl₁ oa).run' s₀) ((simulateQ impl₂ oa).run' s₀) ≤
      Pr{let z ← (simulateQ impl₁ oa).run s₀}[bad z.2] :=
  measureETVDist_simulateQ_run'_le_prEvent_bad impl₁ impl₂ bad
    (fun t s hs _ => prEvent_congr_of_evalDist_eq _ _ (h_agree t s hs) _) h_mono₁ h_mono₂ oa s₀

end OracleComp.ProgramLogic.Relational
