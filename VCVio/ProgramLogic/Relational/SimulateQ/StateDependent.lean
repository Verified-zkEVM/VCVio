/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import VCVio.ProgramLogic.Relational.SimulateQ.UntilBad
public import VCVio.ProgramLogic.Unary.HoareTriple

/-!
# State-dependent expected query slack

Two handlers on a state `σ × Bool`, whose flag records a bad event, may differ in total variation
by `ε s` on each charged query answered from a good state `(s, false)`. The two runs of a
computation then stay within the **expected accumulated slack** of the charged queries it fires,
plus the probability of ending in a bad state. `expectedQuerySlack` is that expectation, defined
by recursion on the computation with the unary expectation `wp` at each query.

A constant slack recovers the query-bounded `q · ε` estimate
(`expectedQuerySlack_const_le_queryBudget_mul`). A slack that grows with a resource carried in the
state is bounded by the resource folds `expectedQuerySlack_resource_le`,
`expectedQuerySlack_expected_resource_le` and
`expectedQuerySlack_charged_read_expected_growth_le`. The per-step slack of a Fiat-Shamir signing
oracle, `ζ_zk + |s.cache| · β`, is of the second kind.

## Main results

- `measureETVDist_simulateQ_run_le_expectedQuerySlack_add_prEvent_bad`: total variation of the
  joint runs is at most the expected slack plus the probability of a bad final state.
- `measureETVDist_simulateQ_run'_le_expectedQuerySlack_add_prEvent_bad`: the same on outputs.
-/

public section

open ENNReal MeasureTheory OracleSpec OracleComp
open scoped OracleSpec.PrimitiveQuery

namespace OracleComp.ProgramLogic.Relational

section expectedQuerySlack

variable {ι : Type} {spec : OracleSpec ι}
variable {ι' : Type} {spec' : OracleSpec ι'} [AnswerMeasure spec']
variable {α : Type} {σ : Type}

/-- A lossless computation has the constant expectation of a constant. -/
private lemma wp_const_eq {β : Type} (oa : OracleComp spec' β) (c : ℝ≥0∞) :
    (wp⟦oa⟧ fun _ => c) = c :=
  ExpectationWP.wp_const_of_oracle oa c

/-- Per-`query_bind` step of `expectedQuerySlack`. Given the handler, the charged-query predicate
`S`, the per-state query slack `ε`, the query symbol `t`, and the continuation
`k : Range t → ℕ → (σ × Bool) → ℝ≥0∞`, it returns the expected slack of performing `t` from the
state `p` with budget `qS`:

* if the bad flag is set in `p`, the step costs `0` (the bad-event term covers the rest);
* an uncharged query (`¬ S t`) forwards through the handler with the budget unchanged;
* a charged query with an exhausted budget costs `0` (the query bound rules it out);
* a charged query with budget left pays `ε p.1`, then forwards through the handler with budget
  `qS - 1`. -/
@[expose] noncomputable def expectedQuerySlackStep
    (impl : QueryImpl spec (StateT (σ × Bool) (OracleComp spec')))
    (S : spec.Domain → Prop) [DecidablePred S]
    (ε : σ → ℝ≥0∞) (t : spec.Domain)
    (k : spec.Range t → ℕ → (σ × Bool) → ℝ≥0∞)
    (qS : ℕ) (p : σ × Bool) : ℝ≥0∞ :=
  if p.2 then 0
  else
    if S t then
      if 0 < qS then
        ε p.1 + wp⟦(impl t).run (p.1, false)⟧ fun z => k z.1 (qS - 1) z.2
      else 0
    else
      wp⟦(impl t).run (p.1, false)⟧ fun z => k z.1 qS z.2

/-- Expected accumulated query slack over the charged queries fired during
`(simulateQ impl oa).run p`, defined by recursion on `oa` via `OracleComp.construct`. -/
@[expose] noncomputable def expectedQuerySlack
    (impl : QueryImpl spec (StateT (σ × Bool) (OracleComp spec')))
    (S : spec.Domain → Prop) [DecidablePred S] (ε : σ → ℝ≥0∞) :
    {α : Type} → OracleComp spec α → ℕ → (σ × Bool) → ℝ≥0∞ :=
  fun {_} oa => OracleComp.construct
    (C := fun _ => ℕ → (σ × Bool) → ℝ≥0∞)
    (fun _ _ _ => 0)
    (fun t _ ih => expectedQuerySlackStep impl S ε t ih)
    oa

@[simp]
lemma expectedQuerySlack_pure
    (impl : QueryImpl spec (StateT (σ × Bool) (OracleComp spec')))
    (S : spec.Domain → Prop) [DecidablePred S] (ε : σ → ℝ≥0∞) (x : α)
    (qS : ℕ) (p : σ × Bool) :
    expectedQuerySlack impl S ε (pure x : OracleComp spec α) qS p = 0 := rfl

/-- Defining equation of `expectedQuerySlack` at a query node: the slack of `query t >>= cont`
is a single `expectedQuerySlackStep` for the query symbol `t`, applied to the continuation
`fun u => expectedQuerySlack impl S ε (cont u)`; that continuation is left unapplied so the step
can feed it the post-query budget and state.

Together with `expectedQuerySlack_pure`, this pins `expectedQuerySlack` down on every computation.
The `expectedQuerySlackStep_*` lemmas then evaluate a single step by cases on the bad flag, on
`S t`, and on whether the budget `qS` is exhausted. -/
lemma expectedQuerySlack_query_bind
    (impl : QueryImpl spec (StateT (σ × Bool) (OracleComp spec')))
    (S : spec.Domain → Prop) [DecidablePred S] (ε : σ → ℝ≥0∞)
    (t : spec.Domain) (cont : spec.Range t → OracleComp spec α)
    (qS : ℕ) (p : σ × Bool) :
    expectedQuerySlack impl S ε (query t >>= cont) qS p =
      expectedQuerySlackStep impl S ε t (fun u => expectedQuerySlack impl S ε (cont u)) qS p := rfl

lemma expectedQuerySlack_bind_eq_of_right_zero
    (impl : QueryImpl spec (StateT (σ × Bool) (OracleComp spec')))
    (S : spec.Domain → Prop) [DecidablePred S] (ε : σ → ℝ≥0∞)
    {β : Type} (oa : OracleComp spec α) (ob : α → OracleComp spec β)
    (hzero : ∀ x qS p, expectedQuerySlack impl S ε (ob x) qS p = 0)
    (qS : ℕ) (p : σ × Bool) :
    expectedQuerySlack impl S ε (oa >>= ob) qS p =
      expectedQuerySlack impl S ε oa qS p := by
  induction oa using OracleComp.inductionOn generalizing qS p with
  | pure x =>
      simp [hzero x qS p]
  | query_bind t cont ih =>
      simp only [monad_norm]
      rw [expectedQuerySlack_query_bind, expectedQuerySlack_query_bind]
      congr; funext u qS' p'; exact ih u qS' p'

@[simp]
lemma expectedQuerySlackStep_bad_eq_zero
    (impl : QueryImpl spec (StateT (σ × Bool) (OracleComp spec')))
    (S : spec.Domain → Prop) [DecidablePred S] (ε : σ → ℝ≥0∞) (t : spec.Domain)
    (k : spec.Range t → ℕ → (σ × Bool) → ℝ≥0∞)
    (qS : ℕ) (s : σ) :
    expectedQuerySlackStep impl S ε t k qS (s, true) = 0 := rfl

@[simp]
lemma expectedQuerySlack_bad_eq_zero
    (impl : QueryImpl spec (StateT (σ × Bool) (OracleComp spec')))
    (S : spec.Domain → Prop) [DecidablePred S] (ε : σ → ℝ≥0∞)
    (oa : OracleComp spec α) (qS : ℕ) (s : σ) :
    expectedQuerySlack impl S ε oa qS (s, true) = 0 := by
  induction oa using OracleComp.inductionOn with
  | pure x => exact expectedQuerySlack_pure impl S ε x qS (s, true)
  | query_bind t cont _ =>
      rw [expectedQuerySlack_query_bind, expectedQuerySlackStep_bad_eq_zero]

/-- Unfolding of `expectedQuerySlackStep` at a *charged* query with budget left, reached with the
bad flag unset: the slack `ε s` is paid up front, then the continuation is averaged over the
handler's answer and successor state with the budget decremented. -/
lemma expectedQuerySlackStep_costly_pos
    (impl : QueryImpl spec (StateT (σ × Bool) (OracleComp spec')))
    (S : spec.Domain → Prop) [DecidablePred S] (ε : σ → ℝ≥0∞) (t : spec.Domain)
    (k : spec.Range t → ℕ → (σ × Bool) → ℝ≥0∞)
    (qS : ℕ) (s : σ) (hS : S t) (hqS : 0 < qS) :
    expectedQuerySlackStep impl S ε t k qS (s, false) =
      ε s + wp⟦(impl t).run (s, false)⟧ fun z => k z.1 (qS - 1) z.2 := by
  simp [expectedQuerySlackStep, hS, hqS]

/-- Unfolding of `expectedQuerySlackStep` at an *uncharged* query (`¬ S t`) reached with the
bad flag unset: no slack is paid, and the step is the expectation of the continuation `k` over
the handler's answer and successor state, with the budget `qS` forwarded unchanged.

This is the `¬ S t` half of the case split on the step function; the companions are
`expectedQuerySlackStep_costly_pos` and `expectedQuerySlackStep_bad_eq_zero`. The remaining case,
a charged query with exhausted budget, is also `0` and is reached by unfolding
`expectedQuerySlackStep` directly. -/
lemma expectedQuerySlackStep_free
    (impl : QueryImpl spec (StateT (σ × Bool) (OracleComp spec')))
    (S : spec.Domain → Prop) [DecidablePred S] (ε : σ → ℝ≥0∞) (t : spec.Domain)
    (k : spec.Range t → ℕ → (σ × Bool) → ℝ≥0∞)
    (qS : ℕ) (s : σ) (hS : ¬ S t) :
    expectedQuerySlackStep impl S ε t k qS (s, false) =
      wp⟦(impl t).run (s, false)⟧ fun z => k z.1 qS z.2 := by
  simp [expectedQuerySlackStep, hS]

/-! ### Monotonicity and congruence

`expectedQuerySlack` is monotone in the per-state slack, which bounds a state-dependent slack by a
constant one so that `expectedQuerySlack_const_le_queryBudget_mul` applies, and it only sees the
slack on states an execution can reach. -/

@[gcongr]
lemma expectedQuerySlackStep_mono
    (impl : QueryImpl spec (StateT (σ × Bool) (OracleComp spec')))
    (S : spec.Domain → Prop) [DecidablePred S] {ε ε' : σ → ℝ≥0∞}
    (hε : ∀ s, ε s ≤ ε' s)
    (t : spec.Domain) {k k' : spec.Range t → ℕ → (σ × Bool) → ℝ≥0∞}
    (hk : ∀ u qS p, k u qS p ≤ k' u qS p)
    (qS : ℕ) (p : σ × Bool) :
    expectedQuerySlackStep impl S ε t k qS p ≤ expectedQuerySlackStep impl S ε' t k' qS p := by
  rcases p with ⟨s, b⟩
  cases b with
  | true => simp
  | false =>
      by_cases hSt : S t
      · by_cases hqS : 0 < qS
        · rw [expectedQuerySlackStep_costly_pos impl S ε t k qS s hSt hqS,
              expectedQuerySlackStep_costly_pos impl S ε' t k' qS s hSt hqS]
          exact add_le_add (hε s) (wp_mono _ fun z => hk z.1 (qS - 1) z.2)
        · simp [expectedQuerySlackStep, hSt, hqS]
      · rw [expectedQuerySlackStep_free impl S ε t k qS s hSt,
            expectedQuerySlackStep_free impl S ε' t k' qS s hSt]
        exact wp_mono _ fun z => hk z.1 qS z.2

@[gcongr]
theorem expectedQuerySlack_mono
    (impl : QueryImpl spec (StateT (σ × Bool) (OracleComp spec')))
    (S : spec.Domain → Prop) [DecidablePred S] {ε ε' : σ → ℝ≥0∞}
    (hε : ∀ s, ε s ≤ ε' s)
    (oa : OracleComp spec α) (qS : ℕ) (p : σ × Bool) :
    expectedQuerySlack impl S ε oa qS p ≤ expectedQuerySlack impl S ε' oa qS p := by
  induction oa using OracleComp.inductionOn generalizing qS p with
  | pure x => simp
  | query_bind t cont ih =>
      exact expectedQuerySlackStep_mono impl S hε t (fun u qS' p' => ih u qS' p') qS p

/-- If two per-state query slack functions agree on an invariant `Inv`, and the handler preserves
`Inv` along the support of every query answered from a no-bad state, then `expectedQuerySlack`
cannot tell the two apart: only invariant-reachable states are ever charged.

Where `expectedQuerySlack_mono` compares two budgets that are ordered at *every* state, this
compares two budgets that merely agree on the states an execution can reach, so a budget may be
given arbitrary values off `Inv`. To apply it, instantiate `Inv` with whatever reachability
predicate `impl` maintains; `h_pres` is then the usual support-level preservation obligation.

The state hypotheses are phrased as `p.2 = false → Inv p.1` so that bad states stay vacuous:
`expectedQuerySlack` is definitionally zero once the bad flag is set. -/
theorem expectedQuerySlack_eq_of_inv
    (impl : QueryImpl spec (StateT (σ × Bool) (OracleComp spec')))
    (S : spec.Domain → Prop) [DecidablePred S] {ε ε' : σ → ℝ≥0∞}
    (Inv : σ → Prop)
    (hε : ∀ s, Inv s → ε s = ε' s) (h_pres : ∀ (t : spec.Domain) (p : σ × Bool),
      p.2 = false → Inv p.1 → ∀ z ∈ support ((impl t).run p), Inv z.2.1)
    (oa : OracleComp spec α) (qS : ℕ) (p : σ × Bool) (hp : p.2 = false → Inv p.1) :
    expectedQuerySlack impl S ε oa qS p = expectedQuerySlack impl S ε' oa qS p := by
  induction oa using OracleComp.inductionOn generalizing qS p with
  | pure x => simp
  | query_bind t cont ih =>
      rcases p with ⟨s, b⟩
      cases b with
      | true => simp
      | false =>
          have hInv : Inv s := hp rfl
          by_cases hSt : S t
          · by_cases hqS : 0 < qS
            · rw [expectedQuerySlack_query_bind, expectedQuerySlack_query_bind,
                expectedQuerySlackStep_costly_pos impl S ε t
                  (fun u => expectedQuerySlack impl S ε (cont u)) qS s hSt hqS,
                expectedQuerySlackStep_costly_pos impl S ε' t
                  (fun u => expectedQuerySlack impl S ε' (cont u)) qS s hSt hqS,
                hε s hInv]
              congr 1
              exact wp_congr_of_support _ fun z hz =>
                ih z.1 (qS - 1) z.2 fun _ => h_pres t (s, false) rfl hInv z hz
            · simp [expectedQuerySlack_query_bind, expectedQuerySlackStep, hSt, hqS]
          · rw [expectedQuerySlack_query_bind, expectedQuerySlack_query_bind,
              expectedQuerySlackStep_free impl S ε t
                (fun u => expectedQuerySlack impl S ε (cont u)) qS s hSt,
              expectedQuerySlackStep_free impl S ε' t
                (fun u => expectedQuerySlack impl S ε' (cont u)) qS s hSt]
            exact wp_congr_of_support _ fun z hz =>
              ih z.1 qS z.2 fun _ => h_pres t (s, false) rfl hInv z hz

/-! ### Identical until bad, up to the expected query slack -/

/-- **State-dependent ε-perturbed identical until bad**, on answer-state pairs.

The handlers may differ in total variation by `querySlack s` on each charged query answered from
a good state `(s, false)`, and must coincide on uncharged queries from good states; the first
handler keeps bad states bad. The joint runs of a computation making at most `queryBudget`
charged queries then stay within its expected accumulated slack plus the probability that the
first run ends in a bad state. -/
theorem measureETVDist_simulateQ_run_le_expectedQuerySlack_add_prEvent_bad
    [MeasurableSpace (α × σ × Bool)]
    (impl₁ impl₂ : QueryImpl spec (StateT (σ × Bool) (OracleComp spec')))
    (chargedQuery : spec.Domain → Prop) [DecidablePred chargedQuery]
    (querySlack : σ → ℝ≥0∞)
    (h_step_charged : ∀ (t : spec.Domain), chargedQuery t → ∀ (s : σ),
      letI : MeasurableSpace (spec.Range t × σ × Bool) := ⊤
      measureETVDist ((impl₁ t).run (s, false)) ((impl₂ t).run (s, false)) ≤ querySlack s)
    (h_step_uncharged : ∀ (t : spec.Domain), ¬ chargedQuery t → ∀ (s : σ),
      (impl₁ t).run (s, false) = (impl₂ t).run (s, false))
    (h_mono₁ : ∀ (t : spec.Domain) (p : σ × Bool), p.2 = true →
      ∀ z ∈ support ((impl₁ t).run p), z.2.2 = true)
    (oa : OracleComp spec α) {queryBudget : ℕ}
    (h_qb : oa.IsQueryBoundP chargedQuery queryBudget) (p : σ × Bool) :
    measureETVDist ((simulateQ impl₁ oa).run p) ((simulateQ impl₂ oa).run p) ≤
      expectedQuerySlack impl₁ chargedQuery querySlack oa queryBudget p +
        Pr{let z ← (simulateQ impl₁ oa).run p}[z.2.2 = true] := by
  induction oa using OracleComp.inductionOn generalizing queryBudget p with
  | pure a => simp
  | query_bind t k ih =>
    rcases p with ⟨s, b⟩
    cases b with
    | true =>
      rw [prEvent_eq_one_of_forall_mem_support _ _ fun z hz =>
        forall_mem_support_simulateQ_run_of_bad impl₁ (fun p : σ × Bool => p.2 = true)
          h_mono₁ _ rfl z hz]
      exact (measureETVDist_le_one _ _).trans le_add_self
    | false =>
      rw [isQueryBoundP_query_bind_iff] at h_qb
      obtain ⟨h_can, h_cont⟩ := h_qb
      rw [expectedQuerySlack_query_bind]
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
        OracleQuery.cont_query, id_map, StateT.run_bind]
      let : MeasurableSpace (spec.Range t × σ × Bool) := ⊤
      set q' := if chargedQuery t then queryBudget - 1 else queryBudget
      have hswap : measureETVDist ((impl₁ t).run (s, false) >>= fun us =>
            (simulateQ impl₂ (k us.1)).run us.2)
          ((impl₂ t).run (s, false) >>= fun us => (simulateQ impl₂ (k us.1)).run us.2) ≤
          if chargedQuery t then querySlack s else 0 := by
        refine (measureETVDist_bind_le _ _ _ Measurable.of_discrete).trans ?_
        split_ifs with hS
        · exact h_step_charged t hS s
        · rw [h_step_uncharged t hS s, measureETVDist_self]
      have hcont : measureETVDist ((impl₁ t).run (s, false) >>= fun us =>
            (simulateQ impl₁ (k us.1)).run us.2)
          ((impl₁ t).run (s, false) >>= fun us => (simulateQ impl₂ (k us.1)).run us.2) ≤
          (wp⟦(impl₁ t).run (s, false)⟧ fun us =>
              expectedQuerySlack impl₁ chargedQuery querySlack (k us.1) q' us.2) +
            Pr{let z ← ((impl₁ t).run (s, false) >>= fun us =>
              (simulateQ impl₁ (k us.1)).run us.2)}[z.2.2 = true] := by
        refine (measureETVDist_bind_bind_le_lintegral _ _ _ Measurable.of_discrete
          Measurable.of_discrete (fun us =>
            expectedQuerySlack impl₁ chargedQuery querySlack (k us.1) q' us.2 +
              Pr{let z ← (simulateQ impl₁ (k us.1)).run us.2}[z.2.2 = true])
          (Filter.Eventually.of_forall fun us => ih us.1 (h_cont us.1) us.2)).trans_eq ?_
        rw [lintegral_add_left Measurable.of_discrete, prEvent_bind,
          prEvent_bind_eq_lintegral_of_discrete, wp_eq_lintegral _ _ Measurable.of_discrete]
      calc _ ≤ _ := measureETVDist_triangle _ _ _
        _ ≤ ((wp⟦(impl₁ t).run (s, false)⟧ fun us =>
                expectedQuerySlack impl₁ chargedQuery querySlack (k us.1) q' us.2) +
              Pr{let z ← ((impl₁ t).run (s, false) >>= fun us =>
                (simulateQ impl₁ (k us.1)).run us.2)}[z.2.2 = true]) +
              if chargedQuery t then querySlack s else 0 :=
            add_le_add hcont hswap
        _ = _ := by
          split_ifs with hS
          · have hpos : 0 < queryBudget := h_can.resolve_left (not_not.2 hS)
            rw [expectedQuerySlackStep_costly_pos _ _ _ _ _ _ _ hS hpos]
            simp only [q', hS, ↓reduceIte]
            ring
          · rw [expectedQuerySlackStep_free _ _ _ _ _ _ _ hS]
            simp only [q', hS, ↓reduceIte, add_zero]

/-- **State-dependent ε-perturbed identical until bad**, on outputs. -/
theorem measureETVDist_simulateQ_run'_le_expectedQuerySlack_add_prEvent_bad
    [MeasurableSpace α]
    (impl₁ impl₂ : QueryImpl spec (StateT (σ × Bool) (OracleComp spec')))
    (chargedQuery : spec.Domain → Prop) [DecidablePred chargedQuery]
    (querySlack : σ → ℝ≥0∞)
    (h_step_charged : ∀ (t : spec.Domain), chargedQuery t → ∀ (s : σ),
      letI : MeasurableSpace (spec.Range t × σ × Bool) := ⊤
      measureETVDist ((impl₁ t).run (s, false)) ((impl₂ t).run (s, false)) ≤ querySlack s)
    (h_step_uncharged : ∀ (t : spec.Domain), ¬ chargedQuery t → ∀ (s : σ),
      (impl₁ t).run (s, false) = (impl₂ t).run (s, false))
    (h_mono₁ : ∀ (t : spec.Domain) (p : σ × Bool), p.2 = true →
      ∀ z ∈ support ((impl₁ t).run p), z.2.2 = true)
    (oa : OracleComp spec α) {queryBudget : ℕ}
    (h_qb : oa.IsQueryBoundP chargedQuery queryBudget) (p : σ × Bool) :
    measureETVDist ((simulateQ impl₁ oa).run' p) ((simulateQ impl₂ oa).run' p) ≤
      expectedQuerySlack impl₁ chargedQuery querySlack oa queryBudget p +
        Pr{let z ← (simulateQ impl₁ oa).run p}[z.2.2 = true] := by
  let : MeasurableSpace (α × σ × Bool) := ⊤
  simp only [StateT.run'_eq]
  exact (measureETVDist_map_le _ _ Prod.fst Measurable.of_discrete).trans
    (measureETVDist_simulateQ_run_le_expectedQuerySlack_add_prEvent_bad impl₁ impl₂
      chargedQuery querySlack h_step_charged h_step_uncharged h_mono₁ oa h_qb p)

/-! ### Closed-form bounds on the expected slack -/

/-- **Constant-ε query-budget bound for `expectedQuerySlack`.**

For the constant per-query slack `fun _ => ε`, a computation firing at most `queryBudget`
charged queries accumulates expected slack at most `queryBudget * ε`: the price of a charged
query does not depend on the simulation state, so the budget simply multiplies it. Free
queries and runs whose bad flag is already set contribute nothing.

A state-dependent slack that admits a uniform upper bound can be routed here through
`expectedQuerySlack_mono`. When the per-query price scales with a resource carried in the state,
use a resource fold instead: `expectedQuerySlack_resource_le` (the resource grows by at most one
in support), `expectedQuerySlack_expected_resource_le` (charged queries grow it by at most `g` in
expectation, at the cost of a binomial cross-term), or
`expectedQuerySlack_charged_read_expected_growth_le` (charged queries only read the resource,
while a separate class of queries grows it). -/
lemma expectedQuerySlack_const_le_queryBudget_mul
    (impl : QueryImpl spec (StateT (σ × Bool) (OracleComp spec')))
    (chargedQuery : spec.Domain → Prop) [DecidablePred chargedQuery] (ε : ℝ≥0∞)
    (oa : OracleComp spec α) {queryBudget : ℕ}
    (h_qb : oa.IsQueryBoundP chargedQuery queryBudget) (p : σ × Bool) :
    expectedQuerySlack impl chargedQuery (fun _ => ε) oa queryBudget p ≤ queryBudget * ε := by
  induction oa using OracleComp.inductionOn generalizing queryBudget p with
  | pure x => simp
  | query_bind t cont ih =>
      rcases p with ⟨s, b⟩
      cases b with
      | true => simp
      | false =>
          rw [isQueryBoundP_query_bind_iff] at h_qb
          obtain ⟨h_can, h_cont⟩ := h_qb
          by_cases hSt : chargedQuery t
          -- a charged query pays `ε` up front and passes on a budget one smaller
          · have hq_pos : 0 < queryBudget := h_can.resolve_left (· hSt)
            obtain ⟨n, rfl⟩ : ∃ n, queryBudget = n + 1 :=
              ⟨queryBudget - 1, (Nat.succ_pred_eq_of_pos hq_pos).symm⟩
            simp only [hSt, ite_true, Nat.add_sub_cancel] at h_cont
            rw [expectedQuerySlack_query_bind,
              expectedQuerySlackStep_costly_pos _ _ _ _ _ _ _ hSt hq_pos, Nat.add_sub_cancel]
            refine le_trans (add_le_add le_rfl (wp_le_const_of_support _
              fun z _ => ih z.1 (h_cont z.1) z.2)) (le_of_eq ?_)
            push_cast
            ring
          -- a free query costs nothing and passes on the whole budget
          · simp only [hSt, ite_false] at h_cont
            rw [expectedQuerySlack_query_bind, expectedQuerySlackStep_free _ _ _ _ _ _ _ hSt]
            exact wp_le_const_of_support _ fun z _ => ih z.1 (h_cont z.1) z.2

/-- State-dependent resource bound for `expectedQuerySlack`.

If each charged query pays `ζ + R s * β`, and the resource `R` can increase by
at most one on charged or growth queries and never increases otherwise, then a
computation with at most `qS` charged queries and at most `qH` growth queries
has accumulated slack at most
`qS * ζ + qS * (R s + qS + qH) * β`. -/
lemma expectedQuerySlack_resource_le
    (impl : QueryImpl spec (StateT (σ × Bool) (OracleComp spec')))
    (chargedQuery growthQuery : spec.Domain → Prop)
    [DecidablePred chargedQuery] [DecidablePred growthQuery]
    (R : σ → ℝ≥0∞) (ζ β : ℝ≥0∞)
    (h_growth : ∀ (t : spec.Domain) (p : σ × Bool), p.2 = false →
      chargedQuery t ∨ growthQuery t →
      ∀ z ∈ support ((impl t).run p), R z.2.1 ≤ R p.1 + 1)
    (h_free : ∀ (t : spec.Domain) (p : σ × Bool), p.2 = false →
      ¬ chargedQuery t → ¬ growthQuery t →
      ∀ z ∈ support ((impl t).run p), R z.2.1 ≤ R p.1)
    (oa : OracleComp spec α) {qS qH : ℕ}
    (h_qS : oa.IsQueryBoundP chargedQuery qS)
    (h_qH : oa.IsQueryBoundP growthQuery qH)
    (s : σ) :
    expectedQuerySlack impl chargedQuery (fun s => ζ + R s * β) oa qS (s, false)
      ≤ (qS : ℝ≥0∞) * ζ + (qS : ℝ≥0∞) * (R s + qS + qH) * β := by
  induction oa using OracleComp.inductionOn generalizing qS qH s with
  | pure x => simp
  | query_bind t cont ih =>
      rw [isQueryBoundP_query_bind_iff] at h_qS h_qH
      obtain ⟨hcanS, hcontS⟩ := h_qS
      obtain ⟨hcanH, hcontH⟩ := h_qH
      let qH' : ℕ := if growthQuery t then qH - 1 else qH
      let slackSum : ℕ → ℝ≥0∞ := fun n => wp⟦(impl t).run (s, false)⟧ fun z =>
        expectedQuerySlack impl chargedQuery (fun s => ζ + R s * β) (cont z.1) n z.2
      set B : ℝ≥0∞ := R s + qS + qH with hB
      suffices h_tail : ∀ (n : ℕ),
          (∀ u, (cont u).IsQueryBoundP chargedQuery n) →
          (∀ z ∈ support ((impl t).run (s, false)), R z.2.1 + n + qH' ≤ B) →
          slackSum n ≤ (n : ℝ≥0∞) * ζ + (n : ℝ≥0∞) * B * β from by
        by_cases hSt : chargedQuery t
        · let qS' : ℕ := qS - 1
          simp only [hSt, ite_true] at hcontS
          have hqS_pos : 0 < qS := hcanS.resolve_left (· hSt)
          have hqS_cast : (((qS - 1 : ℕ) : ℝ≥0∞) + 1) = (qS : ℝ≥0∞) := by
            exact_mod_cast Nat.sub_add_cancel hqS_pos
          rw [expectedQuerySlack_query_bind,
            expectedQuerySlackStep_costly_pos _ _ _ _ _ _ _ hSt hqS_pos]
          have hbudget : ∀ z ∈ support ((impl t).run (s, false)), R z.2.1 + qS' + qH' ≤ B := by
            intro z hz
            have hRz : R z.2.1 ≤ R s + 1 := h_growth t (s, false) rfl (Or.inl hSt) z hz
            calc R z.2.1 + qS' + qH'
                ≤ (R s + 1) + qS' + qH' := by
                  rw [add_assoc, add_assoc]; exact add_le_add_left hRz (qS' + qH')
              _ = R s + qS + qH' := by rw [add_assoc (R s), add_comm 1, hqS_cast]
              _ ≤ B := by
                dsimp only [B, qH']; gcongr; split_ifs
                · exact tsub_le_self
                · exact le_rfl
          calc ζ + R s * β + slackSum qS'
            ≤ ζ + B * β + ((qS' : ℝ≥0∞) * ζ + (qS' : ℝ≥0∞) * B * β) := by
                gcongr
                · exact (le_self_add : R s ≤ R s + (qS : ℝ≥0∞)).trans le_self_add
                · exact h_tail qS' hcontS hbudget
          _ = (qS : ℝ≥0∞) * ζ + (qS : ℝ≥0∞) * B * β := by rw [← hqS_cast]; ring
        · simp only [hSt, ite_false] at hcontS
          rw [expectedQuerySlack_query_bind, expectedQuerySlackStep_free _ _ _ _ _ _ _ hSt]
          have hbudget : ∀ z ∈ support ((impl t).run (s, false)), R z.2.1 + qS + qH' ≤ B := by
            intro z hz
            have hRz : R z.2.1 ≤ R s + if growthQuery t then (1 : ℝ≥0∞) else 0 := by
              by_cases hHt : growthQuery t <;> simp only [hHt, ↓reduceIte, add_zero]
              · exact h_growth t (s, false) rfl (Or.inr hHt) z hz
              · exact h_free t (s, false) rfl hSt hHt z hz
            calc R z.2.1 + qS + qH'
                ≤ (R s + if growthQuery t then (1 : ℝ≥0∞) else 0) + (qS + qH') := by
                  rw [add_assoc]; exact add_le_add_left hRz (qS + qH')
              _ = R s + qS + qH' + if growthQuery t then (1 : ℝ≥0∞) else 0 := by ring_nf
              _ ≤ B := by
                by_cases hHt : growthQuery t <;> simp only [qH', hHt, ↓reduceIte]
                · have hqH_cast : (((qH - 1 : ℕ) : ℝ≥0∞) + 1) = (qH : ℝ≥0∞) := by
                    exact_mod_cast Nat.sub_add_cancel (hcanH.resolve_left (· hHt))
                  rw [add_assoc, hqH_cast]
                · ring_nf; exact le_refl _
          exact h_tail qS hcontS hbudget
      intro n hcont' hRz_bound
      apply wp_le_const_of_support
      intro z hz
      rcases z with ⟨u, s', bad'⟩
      cases bad' with
      | false =>
          exact (ih u (hcont' u) (hcontH u) s').trans
            (by gcongr; exact hRz_bound _ hz)
      | true => simp

/-- Expected-growth resource bound for `expectedQuerySlack`.

Like `expectedQuerySlack_resource_le`, but a charged query may grow the resource by more
than one in support, as long as it grows by at most `g` **in expectation** under the
handler. Growth queries grow the resource by at most one in support, and free queries
never grow it. The accumulated slack of a computation with at most `qS` charged and `qH`
growth queries is then at most `qS·ζ + (qS·R s + qS·qH + C(qS,2)·g)·β`, the binomial
cross term coming from the expected resource increase of earlier charged queries. -/
lemma expectedQuerySlack_expected_resource_le
    (impl : QueryImpl spec (StateT (σ × Bool) (OracleComp spec')))
    (chargedQuery growthQuery : spec.Domain → Prop)
    [DecidablePred chargedQuery] [DecidablePred growthQuery]
    (R : σ → ℝ≥0∞) (ζ β g : ℝ≥0∞)
    (h_charged : ∀ (t : spec.Domain) (p : σ × Bool), p.2 = false → chargedQuery t →
      (wp⟦(impl t).run p⟧ fun z => R z.2.1) ≤ R p.1 + g)
    (h_growth : ∀ (t : spec.Domain) (p : σ × Bool), p.2 = false →
      ¬ chargedQuery t → growthQuery t →
      ∀ z ∈ support ((impl t).run p), R z.2.1 ≤ R p.1 + 1)
    (h_free : ∀ (t : spec.Domain) (p : σ × Bool), p.2 = false →
      ¬ chargedQuery t → ¬ growthQuery t →
      ∀ z ∈ support ((impl t).run p), R z.2.1 ≤ R p.1)
    (oa : OracleComp spec α) {qS qH : ℕ}
    (h_qS : oa.IsQueryBoundP chargedQuery qS)
    (h_qH : oa.IsQueryBoundP growthQuery qH)
    (s : σ) :
    expectedQuerySlack impl chargedQuery (fun s => ζ + R s * β) oa qS (s, false)
      ≤ (qS : ℝ≥0∞) * ζ +
        ((qS : ℝ≥0∞) * R s + (qS : ℝ≥0∞) * (qH : ℝ≥0∞) +
          (qS.choose 2 : ℝ≥0∞) * g) * β := by
  induction oa using OracleComp.inductionOn generalizing qS qH s with
  | pure x => simp only [expectedQuerySlack_pure, zero_le]
  | query_bind t cont ih =>
      rw [isQueryBoundP_query_bind_iff] at h_qS h_qH
      obtain ⟨hcanS, hcontS⟩ := h_qS
      obtain ⟨hcanH, hcontH⟩ := h_qH
      by_cases hSt : chargedQuery t
      · simp only [hSt, ite_true] at hcontS
        have hqS_pos : 0 < qS := hcanS.resolve_left (· hSt)
        obtain ⟨m, rfl⟩ : ∃ m, qS = m + 1 := ⟨qS - 1, by omega⟩
        rw [expectedQuerySlack_query_bind,
          expectedQuerySlackStep_costly_pos _ _ _ _ _ _ _ hSt hqS_pos]
        simp only [Nat.add_sub_cancel] at hcontS ⊢
        -- The continuation's slack is linear in the resource it starts from.
        have h_pt : ∀ z : spec.Range t × σ × Bool,
            expectedQuerySlack impl chargedQuery (fun s => ζ + R s * β) (cont z.1) m z.2
            ≤ ((m : ℝ≥0∞) * ζ +
                  ((m : ℝ≥0∞) * (qH : ℝ≥0∞) + (m.choose 2 : ℝ≥0∞) * g) * β)
              + (m : ℝ≥0∞) * β * R z.2.1 := by
          rintro ⟨u, s', bad'⟩
          cases bad' with
          | true => simp
          | false =>
              have hIH : expectedQuerySlack impl chargedQuery (fun s => ζ + R s * β)
                  (cont u) m (s', false)
                  ≤ (m : ℝ≥0∞) * ζ + ((m : ℝ≥0∞) * R s' + (m : ℝ≥0∞) * (qH : ℝ≥0∞)
                      + (m.choose 2 : ℝ≥0∞) * g) * β := by
                have hqH'_le : (if growthQuery t then qH - 1 else qH) ≤ qH := by
                  split_ifs <;> omega
                refine (ih u (hcontS u) (hcontH u) s').trans ?_
                gcongr
              refine hIH.trans (le_of_eq ?_)
              ring
        have h_wp : (wp⟦(impl t).run (s, false)⟧ fun z =>
              expectedQuerySlack impl chargedQuery (fun s => ζ + R s * β) (cont z.1) m z.2)
            ≤ ((m : ℝ≥0∞) * ζ +
                ((m : ℝ≥0∞) * (qH : ℝ≥0∞) + (m.choose 2 : ℝ≥0∞) * g) * β)
              + (m : ℝ≥0∞) * β * (R s + g) := by
          refine (wp_mono _ h_pt).trans ?_
          rw [ExpectationWP.wp_add, ExpectationWP.wp_const_mul, wp_const_eq]
          exact add_le_add le_rfl (mul_le_mul_right (h_charged t (s, false) rfl hSt) _)
        have hch : (((m + 1).choose 2 : ℕ) : ℝ≥0∞) = (m : ℝ≥0∞) + (m.choose 2 : ℝ≥0∞) := by
          have hch_nat : (m + 1).choose 2 = m + m.choose 2 := by
            rw [Nat.choose_succ_succ', Nat.choose_one_right]
          exact_mod_cast hch_nat
        calc ζ + R s * β + (wp⟦(impl t).run (s, false)⟧ fun z =>
              expectedQuerySlack impl chargedQuery (fun s => ζ + R s * β) (cont z.1) m z.2)
            ≤ ζ + R s * β
              + (((m : ℝ≥0∞) * ζ +
                  ((m : ℝ≥0∞) * (qH : ℝ≥0∞) + (m.choose 2 : ℝ≥0∞) * g) * β)
                + (m : ℝ≥0∞) * β * (R s + g)) := by gcongr
          _ = ((m : ℝ≥0∞) + 1) * ζ
              + (((m : ℝ≥0∞) + 1) * R s + (m : ℝ≥0∞) * (qH : ℝ≥0∞)
                + ((m : ℝ≥0∞) + (m.choose 2 : ℝ≥0∞)) * g) * β := by ring
          _ ≤ ((m : ℝ≥0∞) + 1) * ζ
              + (((m : ℝ≥0∞) + 1) * R s + ((m : ℝ≥0∞) + 1) * (qH : ℝ≥0∞)
                + ((m : ℝ≥0∞) + (m.choose 2 : ℝ≥0∞)) * g) * β := by
              gcongr
              exact le_self_add
          _ = ((m + 1 : ℕ) : ℝ≥0∞) * ζ
              + (((m + 1 : ℕ) : ℝ≥0∞) * R s + ((m + 1 : ℕ) : ℝ≥0∞) * (qH : ℝ≥0∞)
                + (((m + 1).choose 2 : ℕ) : ℝ≥0∞) * g) * β := by
              rw [Nat.cast_add_one, hch]
      · simp only [hSt, ite_false] at hcontS
        rw [expectedQuerySlack_query_bind, expectedQuerySlackStep_free _ _ _ _ _ _ _ hSt]
        have h_z : ∀ z ∈ support ((impl t).run (s, false)),
            expectedQuerySlack impl chargedQuery (fun s => ζ + R s * β) (cont z.1) qS z.2
              ≤ (qS : ℝ≥0∞) * ζ + ((qS : ℝ≥0∞) * R s + (qS : ℝ≥0∞) * (qH : ℝ≥0∞)
                  + (qS.choose 2 : ℝ≥0∞) * g) * β := by
          rintro ⟨u, s', bad'⟩ hz
          cases bad' with
          | true => simp
          | false =>
              refine (ih u (hcontS u) (hcontH u) s').trans ?_
              by_cases hHt : growthQuery t
              · have hqH_pos : 0 < qH := hcanH.resolve_left (· hHt)
                have hqH_cast : ((qH - 1 : ℕ) : ℝ≥0∞) + 1 = (qH : ℝ≥0∞) := by
                  exact_mod_cast Nat.sub_add_cancel hqH_pos
                have hRs' : R s' ≤ R s + 1 := h_growth t (s, false) rfl hSt hHt _ hz
                rw [ite_eq_left hHt]
                calc (qS : ℝ≥0∞) * ζ + ((qS : ℝ≥0∞) * R s'
                        + (qS : ℝ≥0∞) * ((qH - 1 : ℕ) : ℝ≥0∞)
                        + (qS.choose 2 : ℝ≥0∞) * g) * β
                    ≤ (qS : ℝ≥0∞) * ζ + ((qS : ℝ≥0∞) * (R s + 1)
                        + (qS : ℝ≥0∞) * ((qH - 1 : ℕ) : ℝ≥0∞)
                        + (qS.choose 2 : ℝ≥0∞) * g) * β := by gcongr
                  _ = (qS : ℝ≥0∞) * ζ + ((qS : ℝ≥0∞) * R s
                        + (qS : ℝ≥0∞) * (((qH - 1 : ℕ) : ℝ≥0∞) + 1)
                        + (qS.choose 2 : ℝ≥0∞) * g) * β := by ring
                  _ = (qS : ℝ≥0∞) * ζ + ((qS : ℝ≥0∞) * R s + (qS : ℝ≥0∞) * (qH : ℝ≥0∞)
                        + (qS.choose 2 : ℝ≥0∞) * g) * β := by rw [hqH_cast]
              · have hRs' : R s' ≤ R s := h_free t (s, false) rfl hSt hHt _ hz
                rw [ite_eq_right hHt]
                gcongr
        exact wp_le_const_of_support _ h_z

/-- **Charged-read / expected-growth resource bound for `expectedQuerySlack`.**

A variant of `expectedQuerySlack_expected_resource_le` for the situation where the
*charged* queries never grow the resource (they only read it), while a separate class of
*growth* queries grows the resource by at most `g` **in expectation** (and may grow it by
arbitrarily much in support). Free queries never grow it.

Each charged query pays `R s · β` at the state `s` reached when it fires. Since the
charged queries do not grow `R`, and the growth queries grow it by at most `g` in
expectation, the resource seen by any charged query is at most `R s₀ + qH · g` in
expectation, where `s₀` is the starting state and `qH` bounds the growth queries. Folding
the `qS` charged reads against this expected cap gives accumulated slack at most
`qS · (R s₀ + qH · g) · β`, with **no** `(qS choose 2)` cross-term and **no** dependence on
the in-support growth of the resource.

This is the fold used by the ghost-read collision charge of the Fiat-Shamir-with-aborts
Prog → Trans hop, where the charged queries are the adversary's random-oracle reads (which
only grow the *real* cache, leaving the *ghost* cache `R` untouched) and the growth queries
are the signing queries (which grow the ghost cache by the number of rejected attempts, up
to `maxAttempts − 1` in support but at most `∑_{a} p^a ≤ 1/(1−p)` in expectation). -/
lemma expectedQuerySlack_charged_read_expected_growth_le
    (impl : QueryImpl spec (StateT (σ × Bool) (OracleComp spec')))
    (chargedQuery growthQuery : spec.Domain → Prop)
    [DecidablePred chargedQuery] [DecidablePred growthQuery]
    (R : σ → ℝ≥0∞) (β g : ℝ≥0∞)
    (h_charged : ∀ (t : spec.Domain) (p : σ × Bool), p.2 = false → chargedQuery t →
      ∀ z ∈ support ((impl t).run p), R z.2.1 ≤ R p.1)
    (h_growth : ∀ (t : spec.Domain) (p : σ × Bool), p.2 = false →
      ¬ chargedQuery t → growthQuery t →
      (wp⟦(impl t).run p⟧ fun z => R z.2.1) ≤ R p.1 + g)
    (h_free : ∀ (t : spec.Domain) (p : σ × Bool), p.2 = false →
      ¬ chargedQuery t → ¬ growthQuery t →
      ∀ z ∈ support ((impl t).run p), R z.2.1 ≤ R p.1)
    (oa : OracleComp spec α) {qS qH : ℕ}
    (h_qS : oa.IsQueryBoundP chargedQuery qS)
    (h_qH : oa.IsQueryBoundP growthQuery qH)
    (s : σ) :
    expectedQuerySlack impl chargedQuery (fun s => R s * β) oa qS (s, false)
      ≤ (qS : ℝ≥0∞) * (R s + (qH : ℝ≥0∞) * g) * β := by
  induction oa using OracleComp.inductionOn generalizing qS qH s with
  | pure x => simp only [expectedQuerySlack_pure, zero_le]
  | query_bind t cont ih =>
      rw [isQueryBoundP_query_bind_iff] at h_qS h_qH
      obtain ⟨hcanS, hcontS⟩ := h_qS
      obtain ⟨hcanH, hcontH⟩ := h_qH
      by_cases hSt : chargedQuery t
      · -- Charged read: pays `R s · β`, does not grow `R`, continuation budget `qS - 1`.
        simp only [hSt, ite_true] at hcontS
        have hqS_pos : 0 < qS := hcanS.resolve_left (· hSt)
        obtain ⟨m, rfl⟩ : ∃ m, qS = m + 1 := ⟨qS - 1, by omega⟩
        rw [expectedQuerySlack_query_bind,
          expectedQuerySlackStep_costly_pos _ _ _ _ _ _ _ hSt hqS_pos]
        simp only [Nat.add_sub_cancel] at hcontS ⊢
        -- A charged query is not a growth query budget-wise: continuation keeps budget `qH`.
        have hqH'_le : (if growthQuery t then qH - 1 else qH) ≤ qH := by split_ifs <;> omega
        have h_wp_le : (wp⟦(impl t).run (s, false)⟧ fun z =>
              expectedQuerySlack impl chargedQuery (fun s => R s * β) (cont z.1) m z.2)
            ≤ (m : ℝ≥0∞) * (R s + (qH : ℝ≥0∞) * g) * β := by
          apply wp_le_const_of_support
          rintro ⟨u, s', bad'⟩ hz
          cases bad' with
          | true => simp
          | false =>
              refine (ih u (hcontS u) (hcontH u) s').trans ?_
              have hRs' : R s' ≤ R s := h_charged t (s, false) rfl hSt _ hz
              gcongr
        calc R s * β + (wp⟦(impl t).run (s, false)⟧ fun z =>
                expectedQuerySlack impl chargedQuery (fun s => R s * β) (cont z.1) m z.2)
            ≤ R s * β + (m : ℝ≥0∞) * (R s + (qH : ℝ≥0∞) * g) * β := by gcongr
          _ ≤ (R s + (qH : ℝ≥0∞) * g) * β + (m : ℝ≥0∞) * (R s + (qH : ℝ≥0∞) * g) * β := by
              gcongr
              exact le_self_add
          _ = ((m + 1 : ℕ) : ℝ≥0∞) * (R s + (qH : ℝ≥0∞) * g) * β := by push_cast; ring
      · -- Uncharged query: no charge. Split growth vs. free.
        simp only [hSt, ite_false] at hcontS
        rw [expectedQuerySlack_query_bind, expectedQuerySlackStep_free _ _ _ _ _ _ _ hSt]
        by_cases hHt : growthQuery t
        · -- Growth query: `R` grows by `≤ g` in expectation, charged budget unchanged.
          have hqH_pos : 0 < qH := hcanH.resolve_left (· hHt)
          obtain ⟨h, rfl⟩ : ∃ h, qH = h + 1 := ⟨qH - 1, by omega⟩
          simp only [hHt, ite_true] at hcontH
          simp only [Nat.add_sub_cancel] at hcontH
          calc (wp⟦(impl t).run (s, false)⟧ fun z =>
                expectedQuerySlack impl chargedQuery (fun s => R s * β) (cont z.1) qS z.2)
              ≤ wp⟦(impl t).run (s, false)⟧ fun z =>
                  (qS : ℝ≥0∞) * β * (R z.2.1 + (h : ℝ≥0∞) * g) :=
                wp_mono _ fun z => by
                  obtain ⟨u, s', bad'⟩ := z
                  cases bad' with
                  | true => simp
                  | false => exact (ih u (hcontS u) (hcontH u) s').trans (le_of_eq (by ring))
            _ = (qS : ℝ≥0∞) * β *
                  ((wp⟦(impl t).run (s, false)⟧ fun z => R z.2.1) + (h : ℝ≥0∞) * g) := by
                rw [ExpectationWP.wp_const_mul, ExpectationWP.wp_add, wp_const_eq]
            _ ≤ (qS : ℝ≥0∞) * β * ((R s + g) + (h : ℝ≥0∞) * g) := by
                gcongr
                exact h_growth t (s, false) rfl hSt hHt
            _ = (qS : ℝ≥0∞) * (R s + ((h + 1 : ℕ) : ℝ≥0∞) * g) * β := by push_cast; ring
        · -- Free query: `R` does not grow, budgets unchanged.
          simp only [hHt, ite_false] at hcontH
          apply wp_le_const_of_support
          rintro ⟨u, s', bad'⟩ hz
          cases bad' with
          | true => simp
          | false =>
              refine (ih u (hcontS u) (hcontH u) s').trans ?_
              have hRs' : R s' ≤ R s := h_free t (s, false) rfl hSt hHt _ hz
              gcongr

end expectedQuerySlack

end OracleComp.ProgramLogic.Relational
