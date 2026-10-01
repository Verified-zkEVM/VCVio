/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import VCVio.EvalDist.MeasureTVDist.Event
public import VCVio.OracleComp.EvalDist.Measure
public import VCVio.OracleComp.SimSemantics.StateT.Basic
public import VCVio.OracleComp.QueryTracking.QueryBound.Basic
public import VCVio.EvalDist.MeasureTVDist.Bind
public import VCVio.OracleComp.EvalDist.Sum

/-!
# Identical until bad for simulations

Two stateful oracle implementations that give every event the same probability on steps that
start and end in good states, and that never leave the bad states, produce simulations that agree
on every event away from a bad final state. Their outputs are then within the probability of
ending in a bad state in total variation: the fundamental lemma of game playing.

The agreement is only required on good-to-good steps, so the two implementations may disagree on
the step that enters a bad state, as when a bad flag is set by the step that fires it. Agreement
off bad input states, whether as equal runs or equal output measures, is a special case.

The ε-perturbed refinement lets the two handlers differ by total variation `ε` on each charged
query from a good state, adding `ε` per charged query to the bound.
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

variable [AnswerMeasure spec']

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
        OracleQuery.cont_query, id_map, StateT.run_bind, prEvent_bind]
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
    ne_top_of_le_ne_top ENNReal.one_ne_top (prEvent_le_one _)
  rw [ENNReal.eq_sub_of_add_eq (hgood ▸ hne) h₁, ENNReal.eq_sub_of_add_eq hne h₂, hgood]

/-- Computations over flagged outputs that give each unflagged output the same mass agree on every
event of unflagged outputs. This supplies the good-to-good agreement of
`prEvent_simulateQ_run_bad_eq` and `measureETVDist_simulateQ_run_le_prEvent_bad` for the flag
`fun p => p.2 = true` from per-output agreement. -/
theorem prEvent_and_not_flag_eq_of_forall_prEvent_eq [∀ t, Finite (spec'.Range t)] {β : Type}
    {mx my : OracleComp spec' (β × σ × Bool)}
    (h : ∀ b s, Pr{let z ← mx}[z = (b, s, false)] = Pr{let z ← my}[z = (b, s, false)])
    (q : β × σ × Bool → Prop) :
    Pr{let z ← mx}[q z ∧ ¬z.2.2 = true] = Pr{let z ← my}[q z ∧ ¬z.2.2 = true] := by
  classical
  rw [OracleComp.prEvent_eq_tsum_ite, OracleComp.prEvent_eq_tsum_ite]
  refine tsum_congr fun z => ?_
  obtain ⟨b, s, f⟩ := z
  by_cases hq : q (b, s, f) ∧ ¬f = true
  · obtain rfl : f = false := by simpa using hq.2
    rw [ite_eq_left hq, ite_eq_left hq, h]
  · rw [ite_eq_right hq, ite_eq_right hq]

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

/-- **Identical until bad** for handlers equal in distribution off bad input states. -/
theorem measureETVDist_simulateQ_run'_le_prEvent_bad_of_evalDistEq [MeasurableSpace α]
    (impl₁ impl₂ : QueryImpl spec (StateT σ (OracleComp spec'))) (bad : σ → Prop)
    (h_agree : ∀ t s, ¬bad s → (impl₁ t).run s =ᵈ (impl₂ t).run s)
    (h_mono₁ : ∀ t s, bad s → ∀ z ∈ support ((impl₁ t).run s), bad z.2)
    (h_mono₂ : ∀ t s, bad s → ∀ z ∈ support ((impl₂ t).run s), bad z.2)
    (oa : OracleComp spec α) (s₀ : σ) :
    measureETVDist ((simulateQ impl₁ oa).run' s₀) ((simulateQ impl₂ oa).run' s₀) ≤
      Pr{let z ← (simulateQ impl₁ oa).run s₀}[bad z.2] :=
  measureETVDist_simulateQ_run'_le_prEvent_bad impl₁ impl₂ bad
    (fun t s hs _ => (h_agree t s hs).prEvent_eq _) h_mono₁ h_mono₂ oa s₀

/-! ## ε-perturbed identical until bad

The handlers may differ by total variation `ε`, measured in the discrete structure on their
answer-state pairs, on each query in a charged set `S` from a good state, and must coincide on
the other queries from good states. A computation making at most `qS` charged queries then keeps
the two runs within `qS * ε` plus the probability of ending in a bad state. The uniform form
charges every query, and taking no bad state gives a pure per-query budget. -/

section epsilon

variable {κ : Type} {specκ : OracleSpec.{0, 0} κ}

/-- **ε-perturbed identical until bad**, on output-state pairs from any starting state. -/
theorem measureETVDist_simulateQ_run_le_queryBoundP_mul_add_prEvent_bad
    [MeasurableSpace (α × σ)]
    (impl₁ impl₂ : QueryImpl specκ (StateT σ (OracleComp spec'))) (bad : σ → Prop)
    (S : κ → Prop) [DecidablePred S] {ε : ℝ≥0∞}
    (h_step_S : ∀ t, S t → ∀ s, ¬bad s →
      letI : MeasurableSpace (specκ.Range t × σ) := ⊤
      measureETVDist ((impl₁ t).run s) ((impl₂ t).run s) ≤ ε)
    (h_step_nS : ∀ t, ¬S t → ∀ s, ¬bad s → (impl₁ t).run s = (impl₂ t).run s)
    (h_mono₁ : ∀ t s, bad s → ∀ z ∈ support ((impl₁ t).run s), bad z.2)
    (oa : OracleComp specκ α) {qS : ℕ} (h_qb : oa.IsQueryBoundP S qS) (s₀ : σ) :
    measureETVDist ((simulateQ impl₁ oa).run s₀) ((simulateQ impl₂ oa).run s₀) ≤
      qS * ε + Pr{let z ← (simulateQ impl₁ oa).run s₀}[bad z.2] := by
  induction oa using OracleComp.inductionOn generalizing qS s₀ with
  | pure a => simp
  | query_bind t k ih =>
    by_cases hb : bad s₀
    · rw [prEvent_eq_one_of_forall_mem_support _ _ fun z hz =>
        forall_mem_support_simulateQ_run_of_bad impl₁ bad h_mono₁ _ hb z hz]
      exact (measureETVDist_le_one _ _).trans le_add_self
    · rw [isQueryBoundP_query_bind_iff] at h_qb
      obtain ⟨h_can, h_cont⟩ := h_qb
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
        OracleQuery.cont_query, id_map, StateT.run_bind]
      let : MeasurableSpace (specκ.Range t × σ) := ⊤
      set q' := if S t then qS - 1 else qS
      have hmx : IsProbabilityMeasure 𝒟[(impl₁ t).run s₀] :=
        ⟨evalDist_apply_univ_eq_one _⟩
      have hswap : measureETVDist ((impl₁ t).run s₀ >>= fun us =>
            (simulateQ impl₂ (k us.1)).run us.2)
          ((impl₂ t).run s₀ >>= fun us => (simulateQ impl₂ (k us.1)).run us.2) ≤
          if S t then ε else 0 := by
        refine (measureETVDist_bind_le _ _ _ Measurable.of_discrete).trans ?_
        split_ifs with hS
        · exact h_step_S t hS s₀ hb
        · rw [h_step_nS t hS s₀ hb, measureETVDist_self]
      have hcont : measureETVDist ((impl₁ t).run s₀ >>= fun us =>
            (simulateQ impl₁ (k us.1)).run us.2)
          ((impl₁ t).run s₀ >>= fun us => (simulateQ impl₂ (k us.1)).run us.2) ≤
          q' * ε + Pr{let z ← (impl₁ t).run s₀ >>= fun us =>
            (simulateQ impl₁ (k us.1)).run us.2}[bad z.2] := by
        refine (measureETVDist_bind_bind_le_lintegral _ _ _ Measurable.of_discrete
          Measurable.of_discrete (fun us => q' * ε +
            Pr{let z ← (simulateQ impl₁ (k us.1)).run us.2}[bad z.2])
          (Filter.Eventually.of_forall fun us => ih us.1 (h_cont us.1) us.2)).trans_eq ?_
        rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one,
          prEvent_bind, prEvent_bind_eq_lintegral_of_discrete]
      calc _ ≤ _ := measureETVDist_triangle _ _ _
        _ ≤ (q' * ε + Pr{let z ← (impl₁ t).run s₀ >>= fun us =>
              (simulateQ impl₁ (k us.1)).run us.2}[bad z.2]) + if S t then ε else 0 :=
            add_le_add hcont hswap
        _ ≤ _ := by
          split_ifs with hS
          · have hpos : 0 < qS := h_can.resolve_left (not_not.2 hS)
            have hq : ((qS - 1 : ℕ) : ℝ≥0∞) + 1 = qS := by
              exact_mod_cast Nat.sub_add_cancel hpos
            simp only [q', hS, ↓reduceIte]
            rw [add_right_comm, ← hq, add_mul, one_mul]
          · simp only [q', hS, ↓reduceIte, add_zero, le_refl]

/-- **ε-perturbed identical until bad**, on outputs. -/
theorem measureETVDist_simulateQ_run'_le_queryBoundP_mul_add_prEvent_bad [MeasurableSpace α]
    (impl₁ impl₂ : QueryImpl specκ (StateT σ (OracleComp spec'))) (bad : σ → Prop)
    (S : κ → Prop) [DecidablePred S] {ε : ℝ≥0∞}
    (h_step_S : ∀ t, S t → ∀ s, ¬bad s →
      letI : MeasurableSpace (specκ.Range t × σ) := ⊤
      measureETVDist ((impl₁ t).run s) ((impl₂ t).run s) ≤ ε)
    (h_step_nS : ∀ t, ¬S t → ∀ s, ¬bad s → (impl₁ t).run s = (impl₂ t).run s)
    (h_mono₁ : ∀ t s, bad s → ∀ z ∈ support ((impl₁ t).run s), bad z.2)
    (oa : OracleComp specκ α) {qS : ℕ} (h_qb : oa.IsQueryBoundP S qS) (s₀ : σ) :
    measureETVDist ((simulateQ impl₁ oa).run' s₀) ((simulateQ impl₂ oa).run' s₀) ≤
      qS * ε + Pr{let z ← (simulateQ impl₁ oa).run s₀}[bad z.2] := by
  let : MeasurableSpace (α × σ) := ⊤
  simp only [StateT.run'_eq]
  exact (measureETVDist_map_le _ _ Prod.fst Measurable.of_discrete).trans
    (measureETVDist_simulateQ_run_le_queryBoundP_mul_add_prEvent_bad impl₁ impl₂ bad S
      h_step_S h_step_nS h_mono₁ oa h_qb s₀)

/-- **Query-bounded total-variation budget.** Handlers that differ by `ε` on each charged query
and coincide on the others keep the runs of a computation making at most `qS` charged queries
within `qS * ε`. -/
theorem measureETVDist_simulateQ_run_le_queryBoundP_mul [MeasurableSpace (α × σ)]
    (impl₁ impl₂ : QueryImpl specκ (StateT σ (OracleComp spec')))
    (S : κ → Prop) [DecidablePred S] {ε : ℝ≥0∞}
    (h_step_S : ∀ t, S t → ∀ s,
      letI : MeasurableSpace (specκ.Range t × σ) := ⊤
      measureETVDist ((impl₁ t).run s) ((impl₂ t).run s) ≤ ε)
    (h_step_nS : ∀ t, ¬S t → ∀ s, (impl₁ t).run s = (impl₂ t).run s)
    (oa : OracleComp specκ α) {qS : ℕ} (h_qb : oa.IsQueryBoundP S qS) (s₀ : σ) :
    measureETVDist ((simulateQ impl₁ oa).run s₀) ((simulateQ impl₂ oa).run s₀) ≤ qS * ε := by
  have h := measureETVDist_simulateQ_run_le_queryBoundP_mul_add_prEvent_bad impl₁ impl₂
    (fun _ => False) S (fun t hS s _ => h_step_S t hS s) (fun t hS s _ => h_step_nS t hS s)
    (fun _ _ h => h.elim) oa h_qb s₀
  rwa [prEvent_eq_zero_of_forall_not _ _ fun _ h => h, add_zero] at h

end epsilon

end OracleComp.ProgramLogic.Relational
