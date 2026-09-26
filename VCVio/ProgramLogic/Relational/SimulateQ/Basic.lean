/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import VCVio.ProgramLogic.Relational.SimulateQ.Coupling
public import VCVio.EvalDist.TVDist
import VCVio.EvalDist.TVDist.Positivity
public import VCVio.OracleComp.EvalDist
public import VCVio.OracleComp.QueryTracking.QueryBound
public import VCVio.OracleComp.SimSemantics.StateT.StateProjection
public import VCVio.OracleComp.SimSemantics.StateT.Basic.Native

/-!
# Identical-until-bad rules for `simulateQ`

Two oracle implementations that agree until a bad event give output distributions within the
bad event's probability, together with the query-bounded exact-output transport. The coupling
rules for simulated computations live in `VCVio.ProgramLogic.Relational.SimulateQ.Coupling`.
-/

public section

open ENNReal OracleSpec OracleComp
open scoped OracleSpec.PrimitiveQuery

universe u

namespace OracleComp.ProgramLogic.Relational

variable {ι : Type u} {spec : OracleSpec ι}
variable {α : Type}

/-- Query-bounded exact-output transport for `simulateQ`.

If `oa` satisfies a structural query bound `IsQueryBound budget canQuery cost`, the two
implementations agree on every query that the bound permits, and the second implementation
preserves a budget-indexed invariant `Inv`, then the full simulated computations have identical
output-state probabilities from any initial state satisfying `Inv`. -/
theorem probOutput_simulateQ_run_eq_of_impl_eq_queryBound
    {ι : Type} {spec : OracleSpec ι} {σ : Type _} {B : Type _}
    (impl₁ impl₂ : QueryImpl spec (StateT σ ProbComp))
    (Inv : σ → B → Prop)
    (canQuery : spec.Domain → B → Prop)
    (cost : spec.Domain → B → B)
    (oa : OracleComp spec α)
    (budget : B)
    (hbound : oa.IsQueryBound budget canQuery cost)
    (himpl_eq : ∀ (t : spec.Domain) (s : σ) (b : B),
      Inv s b → canQuery t b → (impl₁ t).run s = (impl₂ t).run s)
    (hpres₂ : ∀ (t : spec.Domain) (s : σ) (b : B), Inv s b → canQuery t b →
      ∀ z ∈ support ((impl₂ t).run s), Inv z.2 (cost t b))
    (s : σ) (hs : Inv s budget) (z : α × σ) :
    Pr[= z | (simulateQ impl₁ oa).run s] = Pr[= z | (simulateQ impl₂ oa).run s] := by
  induction oa using OracleComp.inductionOn generalizing s budget z with
  | pure x =>
      simp
  | query_bind t oa ih =>
      rw [isQueryBound_query_bind_iff] at hbound
      rcases hbound with ⟨hcan, hcont⟩
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
        OracleQuery.cont_query, id_map, StateT.run_bind]
      rw [himpl_eq t s budget hs hcan]
      rw [probOutput_bind_eq_tsum, probOutput_bind_eq_tsum]
      refine tsum_congr fun p => ?_
      by_cases hp : p ∈ support ((impl₂ t).run s)
      · congr 1
        exact ih p.1 (cost t budget) (hcont p.1) p.2 (hpres₂ t s budget hs hcan p hp) z
      · simp [(probOutput_eq_zero_iff _ _).2 hp]

/-! ## "Identical until bad" fundamental lemma -/

variable [IsUniformSpec spec]

/-- Bad states are absorbing: if `bad` is closed under the oracle answers of `impl` and the
initial state `s₀` is bad, then `simulateQ impl oa` never returns a good final state. -/
private lemma probOutput_simulateQ_run_eq_zero_of_bad {σ : Type}
    (impl : QueryImpl spec (StateT σ (OracleComp spec))) (bad : σ → Prop)
    (h_mono : ∀ (t : spec.Domain) (s : σ), bad s → ∀ x ∈ support ((impl t).run s), bad x.2)
    (oa : OracleComp spec α) (s₀ : σ) (h_bad : bad s₀) (x : α) (s : σ) (hs : ¬bad s) :
    Pr[= (x, s) | (simulateQ impl oa).run s₀] = 0 := by
  induction oa using OracleComp.inductionOn generalizing s₀ with
  | pure a =>
    simp only [simulateQ_pure, StateT.run_pure, probOutput_eq_zero_iff, support_pure,
      Set.mem_singleton_iff, Prod.ext_iff, not_and]
    rintro rfl rfl
    exact hs h_bad
  | query_bind t oa ih =>
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
      id_map, StateT.run_bind, probOutput_eq_zero_iff, support_bind, Set.mem_iUnion, exists_prop,
      Prod.exists, not_exists, not_and]
    intro u s' h_mem
    exact (probOutput_eq_zero_iff _ _).1 (ih u s' (h_mono t s₀ h_bad (u, s') h_mem))

private lemma probOutput_simulateQ_run_eq_of_not_bad
    {σ : Type}
    (impl₁ impl₂ : QueryImpl spec (StateT σ (OracleComp spec))) (bad : σ → Prop)
    (h_agree : ∀ (t : spec.Domain) (s : σ), ¬bad s →
      (impl₁ t).run s = (impl₂ t).run s)
    (h_mono₁ : ∀ (t : spec.Domain) (s : σ), bad s →
      ∀ x ∈ support ((impl₁ t).run s), bad x.2)
    (h_mono₂ : ∀ (t : spec.Domain) (s : σ), bad s →
      ∀ x ∈ support ((impl₂ t).run s), bad x.2)
    (oa : OracleComp spec α) (s₀ : σ) (x : α) (s : σ) (hs : ¬bad s) :
    Pr[= (x, s) | (simulateQ impl₁ oa).run s₀] =
      Pr[= (x, s) | (simulateQ impl₂ oa).run s₀] := by
  induction oa using OracleComp.inductionOn generalizing s₀ with
  | pure a =>
    by_cases h_bad : bad s₀
    · rw [probOutput_simulateQ_run_eq_zero_of_bad impl₁ bad h_mono₁ (pure a) s₀ h_bad x s hs,
          probOutput_simulateQ_run_eq_zero_of_bad impl₂ bad h_mono₂ (pure a) s₀ h_bad x s hs]
    · rfl
  | query_bind t oa ih =>
    by_cases h_bad : bad s₀
    · rw [probOutput_simulateQ_run_eq_zero_of_bad impl₁ bad h_mono₁ _ s₀ h_bad x s hs,
          probOutput_simulateQ_run_eq_zero_of_bad impl₂ bad h_mono₂ _ s₀ h_bad x s hs]
    · simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
      id_map, StateT.run_bind]
      rw [probOutput_bind_eq_tsum, probOutput_bind_eq_tsum, h_agree t s₀ h_bad]
      exact tsum_congr (fun ⟨u, s'⟩ => by congr 1; exact ih u s')

/-- Two implementations that agree away from `bad` and can never leave `bad` assign the same
probability to the event that the simulation ends in a state that is not `bad`. -/
private lemma probEvent_not_bad_eq {σ : Type}
    (impl₁ impl₂ : QueryImpl spec (StateT σ (OracleComp spec))) (bad : σ → Prop)
    (h_agree : ∀ (t : spec.Domain) (s : σ), ¬bad s → (impl₁ t).run s = (impl₂ t).run s)
    (h_mono₁ : ∀ (t : spec.Domain) (s : σ), bad s → ∀ x ∈ support ((impl₁ t).run s), bad x.2)
    (h_mono₂ : ∀ (t : spec.Domain) (s : σ), bad s → ∀ x ∈ support ((impl₂ t).run s), bad x.2)
    (oa : OracleComp spec α) (s₀ : σ) : Pr[ fun x => ¬bad x.2 | (simulateQ impl₁ oa).run s₀] =
      Pr[ fun x => ¬bad x.2 | (simulateQ impl₂ oa).run s₀] := by
  rw [probEvent_eq_tsum_subtype, probEvent_eq_tsum_subtype]
  exact tsum_congr fun ⟨⟨a, s⟩, h⟩ =>
    probOutput_simulateQ_run_eq_of_not_bad impl₁ impl₂ bad h_agree h_mono₁ h_mono₂ oa s₀ a s h

private lemma probEvent_bad_eq {σ : Type}
    (impl₁ impl₂ : QueryImpl spec (StateT σ (OracleComp spec))) (bad : σ → Prop)
    (h_agree : ∀ (t : spec.Domain) (s : σ), ¬bad s → (impl₁ t).run s = (impl₂ t).run s)
    (h_mono₁ : ∀ (t : spec.Domain) (s : σ), bad s → ∀ x ∈ support ((impl₁ t).run s), bad x.2)
    (h_mono₂ : ∀ (t : spec.Domain) (s : σ), bad s → ∀ x ∈ support ((impl₂ t).run s), bad x.2)
    (oa : OracleComp spec α) (s₀ : σ) : Pr[bad ∘ Prod.snd | (simulateQ impl₁ oa).run s₀] =
      Pr[bad ∘ Prod.snd | (simulateQ impl₂ oa).run s₀] := by
  -- neither run can fail, so the flagged and unflagged masses sum to `1` on each side
  have h1 := probEvent_compl ((simulateQ impl₁ oa).run s₀) (bad ∘ Prod.snd)
  have h2 := probEvent_compl ((simulateQ impl₂ oa).run s₀) (bad ∘ Prod.snd)
  simp only [NeverFail.probFailure_eq_zero, tsub_zero, Function.comp_apply] at h1 h2
  -- the unflagged masses already agree; complementation transports that to the flagged ones
  rw [ENNReal.eq_sub_of_add_eq probEvent_ne_top h1, ENNReal.eq_sub_of_add_eq probEvent_ne_top h2,
    probEvent_not_bad_eq impl₁ impl₂ bad h_agree h_mono₁ h_mono₂ oa s₀]

/-- The fundamental lemma of game playing: if two oracle implementations agree whenever
a "bad" flag is unset, then the total variation distance between the two simulations
is bounded by the probability that bad gets set.

Both implementations must satisfy a monotonicity condition: once `bad s` holds, it must
remain true in all reachable successor states. Without this, the theorem is false — an
implementation could enter a bad state (where agreement is not required), diverge, and
then return to a non-bad state, producing different outputs with `Pr[bad] = 0`.
Monotonicity is needed on both sides because the proof establishes pointwise equality
`Pr[= (x,s) | sim₁] = Pr[= (x,s) | sim₂]` for all `¬bad s`, which requires ruling out
bad-to-non-bad transitions in each implementation independently. -/
theorem tvDist_simulateQ_le_probEvent_bad
    {σ : Type}
    (impl₁ impl₂ : QueryImpl spec (StateT σ (OracleComp spec)))
    (bad : σ → Prop)
    (oa : OracleComp spec α) (s₀ : σ)
    (h_init : ¬bad s₀)
    (h_agree : ∀ (t : spec.Domain) (s : σ), ¬bad s →
      (impl₁ t).run s = (impl₂ t).run s)
    (h_mono₁ : ∀ (t : spec.Domain) (s : σ), bad s →
      ∀ x ∈ support ((impl₁ t).run s), bad x.2)
    (h_mono₂ : ∀ (t : spec.Domain) (s : σ), bad s →
      ∀ x ∈ support ((impl₂ t).run s), bad x.2) :
    tvDist ((simulateQ impl₁ oa).run' s₀) ((simulateQ impl₂ oa).run' s₀)
      ≤ Pr[ bad ∘ Prod.snd | (simulateQ impl₁ oa).run s₀].toReal := by
  classical
  have := h_init -- unused in the bound: `bad s₀` would already force the right-hand side to `1`
  let sim₁ := (simulateQ impl₁ oa).run s₀
  let sim₂ := (simulateQ impl₂ oa).run s₀
  calc tvDist ((simulateQ impl₁ oa).run' s₀) ((simulateQ impl₂ oa).run' s₀)
      ≤ tvDist sim₁ sim₂ := by
        rw [StateT.run']
        exact tvDist_map_le (m := OracleComp spec) (α := α × σ) (β := α) Prod.fst sim₁ sim₂
    -- two-sided monotonicity rules out bad-to-non-bad transitions: the two runs put equal mass
    -- on every non-bad `(x, s)`
    _ ≤ Pr[ bad ∘ Prod.snd | sim₁].toReal :=
        tvDist_le_probEvent_of_probOutput_eq_of_not (mx := sim₁) (my := sim₂) (bad ∘ Prod.snd)
          (fun ⟨x, s⟩ hxs => by
            simpa using probOutput_simulateQ_run_eq_of_not_bad impl₁ impl₂ bad h_agree
              h_mono₁ h_mono₂ oa s₀ x s hxs)
          (probEvent_bad_eq impl₁ impl₂ bad h_agree h_mono₁ h_mono₂ oa s₀)

/-! ## Distributional "identical until bad"

The `_dist` variant weakens the agreement hypothesis from definitional equality
(`impl₁ t).run s = (impl₂ t).run s`) to distributional equality
(`∀ p, Pr[= p | (impl₁ t).run s] = Pr[= p | (impl₂ t).run s]`).
This is needed when the two implementations differ intensionally but agree on
output probabilities. -/

open scoped Classical in
private lemma probOutput_simulateQ_run_eq_of_not_bad_dist
    {σ : Type}
    (impl₁ impl₂ : QueryImpl spec (StateT σ (OracleComp spec))) (bad : σ → Prop)
    (h_agree_dist : ∀ (t : spec.Domain) (s : σ), ¬bad s →
      ∀ p, Pr[= p | (impl₁ t).run s] = Pr[= p | (impl₂ t).run s])
    (h_mono₁ : ∀ (t : spec.Domain) (s : σ), bad s →
      ∀ x ∈ support ((impl₁ t).run s), bad x.2)
    (h_mono₂ : ∀ (t : spec.Domain) (s : σ), bad s →
      ∀ x ∈ support ((impl₂ t).run s), bad x.2)
    (oa : OracleComp spec α) (s₀ : σ) (x : α) (s : σ) (hs : ¬bad s) :
    Pr[= (x, s) | (simulateQ impl₁ oa).run s₀] =
      Pr[= (x, s) | (simulateQ impl₂ oa).run s₀] := by
  induction oa using OracleComp.inductionOn generalizing s₀ with
  | pure a =>
    by_cases h_bad : bad s₀
    · rw [probOutput_simulateQ_run_eq_zero_of_bad impl₁ bad h_mono₁ (pure a) s₀ h_bad x s hs,
        probOutput_simulateQ_run_eq_zero_of_bad impl₂ bad h_mono₂ (pure a) s₀ h_bad x s hs]
    · rfl
  | query_bind t oa ih =>
    by_cases h_bad : bad s₀
    · rw [probOutput_simulateQ_run_eq_zero_of_bad impl₁ bad h_mono₁ _ s₀ h_bad x s hs,
        probOutput_simulateQ_run_eq_zero_of_bad impl₂ bad h_mono₂ _ s₀ h_bad x s hs]
    · simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
        OracleQuery.cont_query, id_map, StateT.run_bind]
      rw [probOutput_bind_eq_tsum, probOutput_bind_eq_tsum]
      have step1 : ∀ (p : spec.Range t × σ),
          Pr[= p | (impl₁ t).run s₀] *
            Pr[= (x, s) | (simulateQ impl₁ (oa p.1)).run p.2] =
          Pr[= p | (impl₁ t).run s₀] *
            Pr[= (x, s) | (simulateQ impl₂ (oa p.1)).run p.2] := by
        intro ⟨u, s'⟩; congr 1; exact ih u s'
      rw [show (∑' p, Pr[= p | (impl₁ t).run s₀] *
          Pr[= (x, s) | (simulateQ impl₁ (oa p.1)).run p.2]) =
          (∑' p, Pr[= p | (impl₁ t).run s₀] *
          Pr[= (x, s) | (simulateQ impl₂ (oa p.1)).run p.2]) from
        tsum_congr step1]
      exact tsum_congr (fun p => by rw [h_agree_dist t s₀ h_bad p])

open scoped Classical in
private lemma probEvent_not_bad_eq_dist
    {σ : Type}
    (impl₁ impl₂ : QueryImpl spec (StateT σ (OracleComp spec))) (bad : σ → Prop)
    (h_agree_dist : ∀ (t : spec.Domain) (s : σ), ¬bad s →
      ∀ p, Pr[= p | (impl₁ t).run s] = Pr[= p | (impl₂ t).run s])
    (h_mono₁ : ∀ (t : spec.Domain) (s : σ), bad s →
      ∀ x ∈ support ((impl₁ t).run s), bad x.2)
    (h_mono₂ : ∀ (t : spec.Domain) (s : σ), bad s →
      ∀ x ∈ support ((impl₂ t).run s), bad x.2)
    (oa : OracleComp spec α) (s₀ : σ) :
    Pr[fun x => ¬bad x.2 | (simulateQ impl₁ oa).run s₀] =
    Pr[fun x => ¬bad x.2 | (simulateQ impl₂ oa).run s₀] := by
  rw [probEvent_eq_tsum_ite, probEvent_eq_tsum_ite]
  refine tsum_congr (fun ⟨a, s⟩ => ?_)
  split_ifs with h
  · rfl
  · exact probOutput_simulateQ_run_eq_of_not_bad_dist impl₁ impl₂ bad h_agree_dist h_mono₁ h_mono₂
      oa s₀ a s h

private lemma probEvent_bad_eq_dist {σ : Type}
    (impl₁ impl₂ : QueryImpl spec (StateT σ (OracleComp spec))) (bad : σ → Prop)
    (h_agree_dist : ∀ (t : spec.Domain) (s : σ), ¬bad s →
      ∀ p, Pr[= p | (impl₁ t).run s] = Pr[= p | (impl₂ t).run s])
    (h_mono₁ : ∀ (t : spec.Domain) (s : σ), bad s → ∀ x ∈ support ((impl₁ t).run s), bad x.2)
    (h_mono₂ : ∀ (t : spec.Domain) (s : σ), bad s → ∀ x ∈ support ((impl₂ t).run s), bad x.2)
    (oa : OracleComp spec α) (s₀ : σ) : Pr[bad ∘ Prod.snd | (simulateQ impl₁ oa).run s₀] =
      Pr[bad ∘ Prod.snd | (simulateQ impl₂ oa).run s₀] := by
  -- neither run can fail, so the flagged and unflagged masses sum to `1` on each side
  have h1 := probEvent_compl ((simulateQ impl₁ oa).run s₀) (bad ∘ Prod.snd)
  have h2 := probEvent_compl ((simulateQ impl₂ oa).run s₀) (bad ∘ Prod.snd)
  simp only [NeverFail.probFailure_eq_zero, tsub_zero, Function.comp_apply] at h1 h2
  -- the unflagged masses already agree; complementation transports that to the flagged ones
  rw [ENNReal.eq_sub_of_add_eq probEvent_ne_top h1, ENNReal.eq_sub_of_add_eq probEvent_ne_top h2,
    probEvent_not_bad_eq_dist impl₁ impl₂ bad h_agree_dist h_mono₁ h_mono₂ oa s₀]

open scoped Classical in
/-- Distributional variant of `tvDist_simulateQ_le_probEvent_bad`:
weakens the agreement hypothesis from definitional equality to distributional equality
(pointwise equal output probabilities). -/
theorem tvDist_simulateQ_le_probEvent_bad_dist
    {σ : Type}
    (impl₁ impl₂ : QueryImpl spec (StateT σ (OracleComp spec)))
    (bad : σ → Prop)
    (oa : OracleComp spec α) (s₀ : σ)
    (_ : ¬bad s₀)
    (h_agree_dist : ∀ (t : spec.Domain) (s : σ), ¬bad s →
      ∀ p, Pr[= p | (impl₁ t).run s] = Pr[= p | (impl₂ t).run s])
    (h_mono₁ : ∀ (t : spec.Domain) (s : σ), bad s →
      ∀ x ∈ support ((impl₁ t).run s), bad x.2)
    (h_mono₂ : ∀ (t : spec.Domain) (s : σ), bad s →
      ∀ x ∈ support ((impl₂ t).run s), bad x.2) :
    tvDist ((simulateQ impl₁ oa).run' s₀) ((simulateQ impl₂ oa).run' s₀)
      ≤ Pr[bad ∘ Prod.snd | (simulateQ impl₁ oa).run s₀].toReal := by
  classical
  let sim₁ := (simulateQ impl₁ oa).run s₀
  let sim₂ := (simulateQ impl₂ oa).run s₀
  calc tvDist ((simulateQ impl₁ oa).run' s₀) ((simulateQ impl₂ oa).run' s₀)
      ≤ tvDist sim₁ sim₂ := by
        rw [StateT.run']
        exact tvDist_map_le (m := OracleComp spec) (α := α × σ) (β := α) Prod.fst sim₁ sim₂
    _ ≤ Pr[bad ∘ Prod.snd | sim₁].toReal :=
        tvDist_le_probEvent_of_probOutput_eq_of_not (mx := sim₁) (my := sim₂) (bad ∘ Prod.snd)
          (fun xs hxs => by
            rcases xs with ⟨x, s⟩
            simpa using probOutput_simulateQ_run_eq_of_not_bad_dist impl₁ impl₂ bad h_agree_dist
              h_mono₁ h_mono₂ oa s₀ x s hxs)
          (probEvent_bad_eq_dist impl₁ impl₂ bad h_agree_dist h_mono₁ h_mono₂ oa s₀)

/-! ## "Identical until bad" with an output bad flag

These variants record the bad event in the **output** state of each oracle step (not the input).
The state has shape `σ × Bool` with the second component a monotone bad flag, and the two
implementations may disagree on the very step that flips the flag. The standard pointwise
agreement hypothesis of `tvDist_simulateQ_le_probEvent_bad{,_dist}` is too strong here: at the
firing step, the input is non-bad but the outputs already differ. The output-bad pattern is the
exact shape of `QueryImpl.withProgramming` (which sets `bad := true` only on policy-firing
steps) and the `programming_collision_bound` argument that builds on it. -/

open scoped Classical in
private lemma probOutput_simulateQ_run_eq_of_not_output_bad
    {σ : Type}
    (impl₁ impl₂ : QueryImpl spec (StateT (σ × Bool) (OracleComp spec)))
    (h_agree_good : ∀ (t : spec.Domain) (s : σ) (u : spec.Range t) (s' : σ),
      Pr[= (u, (s', false)) | (impl₁ t).run (s, false)] =
        Pr[= (u, (s', false)) | (impl₂ t).run (s, false)])
    (h_mono₁ : ∀ (t : spec.Domain) (p : σ × Bool), p.2 = true →
      ∀ z ∈ support ((impl₁ t).run p), z.2.2 = true)
    (h_mono₂ : ∀ (t : spec.Domain) (p : σ × Bool), p.2 = true →
      ∀ z ∈ support ((impl₂ t).run p), z.2.2 = true)
    (oa : OracleComp spec α) (s₀ : σ) (x : α) (s : σ) :
    Pr[= (x, (s, false)) | (simulateQ impl₁ oa).run (s₀, false)] =
      Pr[= (x, (s, false)) | (simulateQ impl₂ oa).run (s₀, false)] := by
  induction oa using OracleComp.inductionOn generalizing s₀ with
  | pure a => rfl
  | query_bind t oa ih =>
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
      id_map, StateT.run_bind]
    rw [probOutput_bind_eq_tsum, probOutput_bind_eq_tsum]
    refine tsum_congr ?_
    rintro ⟨u, ⟨s', b⟩⟩
    cases b with
    | true =>
      have h₁ : Pr[= (x, (s, false)) | (simulateQ impl₁ (oa u)).run (s', true)] = 0 :=
        probOutput_simulateQ_run_eq_zero_of_bad impl₁ (fun p : σ × Bool => p.2 = true)
          h_mono₁ (oa u) (s', true) rfl x (s, false) (by simp)
      have h₂ : Pr[= (x, (s, false)) | (simulateQ impl₂ (oa u)).run (s', true)] = 0 :=
        probOutput_simulateQ_run_eq_zero_of_bad impl₂ (fun p : σ × Bool => p.2 = true)
          h_mono₂ (oa u) (s', true) rfl x (s, false) (by simp)
      simp [h₁, h₂]
    | false =>
      rw [h_agree_good t s₀ u s', ih u s']

open scoped Classical in
private lemma probEvent_output_bad_eq
    {σ : Type}
    (impl₁ impl₂ : QueryImpl spec (StateT (σ × Bool) (OracleComp spec)))
    (h_agree_good : ∀ (t : spec.Domain) (s : σ) (u : spec.Range t) (s' : σ),
      Pr[= (u, (s', false)) | (impl₁ t).run (s, false)] =
        Pr[= (u, (s', false)) | (impl₂ t).run (s, false)])
    (h_mono₁ : ∀ (t : spec.Domain) (p : σ × Bool), p.2 = true →
      ∀ z ∈ support ((impl₁ t).run p), z.2.2 = true)
    (h_mono₂ : ∀ (t : spec.Domain) (p : σ × Bool), p.2 = true →
      ∀ z ∈ support ((impl₂ t).run p), z.2.2 = true)
    (oa : OracleComp spec α) (s₀ : σ) :
    Pr[fun z : α × σ × Bool => z.2.2 = true | (simulateQ impl₁ oa).run (s₀, false)] =
      Pr[fun z : α × σ × Bool => z.2.2 = true | (simulateQ impl₂ oa).run (s₀, false)] := by
  set sim₁ := (simulateQ impl₁ oa).run (s₀, false)
  set sim₂ := (simulateQ impl₂ oa).run (s₀, false)
  have h₁ := probEvent_compl sim₁ (fun z : α × σ × Bool => z.2.2 = true)
  have h₂ := probEvent_compl sim₂ (fun z : α × σ × Bool => z.2.2 = true)
  simp only [NeverFail.probFailure_eq_zero, tsub_zero] at h₁ h₂
  have h_not_eq :
      Pr[fun z : α × σ × Bool => ¬z.2.2 = true | sim₁] =
        Pr[fun z : α × σ × Bool => ¬z.2.2 = true | sim₂] := by
    rw [probEvent_eq_tsum_ite, probEvent_eq_tsum_ite]
    refine tsum_congr ?_
    rintro ⟨a, s, b⟩
    by_cases hb : b = true
    · simp [hb]
    · have hb' : b = false := Bool.eq_false_of_not_eq_true hb
      subst hb'
      simpa using
        probOutput_simulateQ_run_eq_of_not_output_bad impl₁ impl₂ h_agree_good
          h_mono₁ h_mono₂ oa s₀ a s
  have hne₁ : Pr[fun z : α × σ × Bool => ¬z.2.2 = true | sim₁] ≠ ⊤ :=
    ne_top_of_le_ne_top one_ne_top probEvent_le_one
  calc Pr[fun z : α × σ × Bool => z.2.2 = true | sim₁]
      = 1 - Pr[fun z : α × σ × Bool => ¬z.2.2 = true | sim₁] := by
        rw [← h₁]; exact (ENNReal.add_sub_cancel_right hne₁).symm
    _ = 1 - Pr[fun z : α × σ × Bool => ¬z.2.2 = true | sim₂] := by rw [h_not_eq]
    _ = Pr[fun z : α × σ × Bool => z.2.2 = true | sim₂] := by
        rw [← h₂]; exact ENNReal.add_sub_cancel_right
          (ne_top_of_le_ne_top one_ne_top probEvent_le_one)

/-- "Identical until bad" with the bad flag tracked at the **output** of each oracle step.
TV-distance between two state-extended simulations is bounded by the probability of the flag
firing in the run of `impl₁`.

Compared to `tvDist_simulateQ_le_probEvent_bad{,_dist}`, this version weakens the
agreement hypothesis: the two implementations need only agree on **non-bad output transitions**
from non-bad input states. They may disagree arbitrarily on the very step that flips the flag.

Both implementations must satisfy bad-input monotonicity: once `b = true` in the input state of
a step, every reachable output also has `b = true`. -/
theorem tvDist_simulateQ_le_probEvent_output_bad
    {σ : Type}
    (impl₁ impl₂ : QueryImpl spec (StateT (σ × Bool) (OracleComp spec)))
    (oa : OracleComp spec α) (s₀ : σ)
    (h_agree_good : ∀ (t : spec.Domain) (s : σ) (u : spec.Range t) (s' : σ),
      Pr[= (u, (s', false)) | (impl₁ t).run (s, false)] =
        Pr[= (u, (s', false)) | (impl₂ t).run (s, false)])
    (h_mono₁ : ∀ (t : spec.Domain) (p : σ × Bool), p.2 = true →
      ∀ z ∈ support ((impl₁ t).run p), z.2.2 = true)
    (h_mono₂ : ∀ (t : spec.Domain) (p : σ × Bool), p.2 = true →
      ∀ z ∈ support ((impl₂ t).run p), z.2.2 = true) :
    tvDist ((simulateQ impl₁ oa).run' (s₀, false))
        ((simulateQ impl₂ oa).run' (s₀, false))
      ≤ Pr[fun z : α × σ × Bool => z.2.2 = true |
          (simulateQ impl₁ oa).run (s₀, false)].toReal := by
  classical
  set sim₁ := (simulateQ impl₁ oa).run (s₀, false)
  set sim₂ := (simulateQ impl₂ oa).run (s₀, false)
  have h_eq : ∀ (z : α × σ × Bool), ¬(z.2.2 = true) → Pr[= z | sim₁] = Pr[= z | sim₂] := by
    rintro ⟨x, s, b⟩ hb
    have hb' : b = false := Bool.eq_false_of_not_eq_true hb
    subst hb'
    exact probOutput_simulateQ_run_eq_of_not_output_bad impl₁ impl₂ h_agree_good
      h_mono₁ h_mono₂ oa s₀ x s
  have h_map :
      tvDist ((simulateQ impl₁ oa).run' (s₀, false))
          ((simulateQ impl₂ oa).run' (s₀, false))
        ≤ tvDist sim₁ sim₂ := by
    rw [StateT.run']
    exact tvDist_map_le (m := OracleComp spec) (α := α × σ × Bool) (β := α) Prod.fst sim₁ sim₂
  exact h_map.trans <|
    tvDist_le_probEvent_of_probOutput_eq_of_not (mx := sim₁) (my := sim₂)
      (fun z : α × σ × Bool => z.2.2 = true) h_eq
      (probEvent_output_bad_eq impl₁ impl₂ h_agree_good h_mono₁ h_mono₂ oa s₀)

/-- **Fundamental lemma of game playing**, in the "identical until bad" form where the
simulation state is `σ × Bool` and the `Bool` component is the bad flag: the TV distance between
the output marginals of the two simulations is at most the probability that the flag is set at
the end of the run of `impl₁`.

`h_agree_good` constrains only those single-step transitions that both start *and* end unflagged,
so the two implementations may disagree arbitrarily on the very step that raises the flag.
`h_mono₁` and `h_mono₂` say neither implementation ever lowers the flag again, which is what lets
an unflagged endpoint witness an entirely unflagged history.

Applying it: `impl₂` does not occur on the right-hand side, so instantiate `impl₁` as the world
whose flag mass you can bound; the remaining obligation is a `Pr[… z.2.2 = true …]` estimate in
that world alone. This is the shape the `QueryImpl.withProgramming` collision bound is stated in:
the two implementations agree on `(s, false)` inputs except on a programming-fired step, and the
bound is the probability that some policy hit occurs during the run.

`tvDist_simulateQ_le_probEvent_bad` instead takes an arbitrary state predicate `bad : σ → Prop`
and asks the implementations to agree *definitionally* on unflagged states, while
`tvDist_simulateQ_le_probEvent_output_bad` carries exactly the hypotheses and conclusion below
under a name spelling out the inequality rather than the cryptographic idiom. -/
theorem identical_until_bad_with_flag
    {σ : Type}
    (impl₁ impl₂ : QueryImpl spec (StateT (σ × Bool) (OracleComp spec)))
    (oa : OracleComp spec α) (s₀ : σ)
    (h_agree_good : ∀ (t : spec.Domain) (s : σ) (u : spec.Range t) (s' : σ),
      Pr[= (u, (s', false)) | (impl₁ t).run (s, false)] =
        Pr[= (u, (s', false)) | (impl₂ t).run (s, false)])
    (h_mono₁ : ∀ (t : spec.Domain) (p : σ × Bool), p.2 = true →
      ∀ z ∈ support ((impl₁ t).run p), z.2.2 = true)
    (h_mono₂ : ∀ (t : spec.Domain) (p : σ × Bool), p.2 = true →
      ∀ z ∈ support ((impl₂ t).run p), z.2.2 = true) :
    tvDist ((simulateQ impl₁ oa).run' (s₀, false))
        ((simulateQ impl₂ oa).run' (s₀, false))
      ≤ Pr[fun z : α × σ × Bool => z.2.2 = true |
          (simulateQ impl₁ oa).run (s₀, false)].toReal :=
  tvDist_simulateQ_le_probEvent_output_bad impl₁ impl₂ oa s₀ h_agree_good h_mono₁ h_mono₂

end OracleComp.ProgramLogic.Relational
