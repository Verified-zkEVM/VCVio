/-
Copyright (c) 2026 Emile. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Emile
-/

module

public import VCVio.OracleComp.QueryTracking.QueryBound
public import VCVio.OracleComp.ProbComp
public import VCVio.EvalDist.Monad.Measure
public import VCVio.OracleComp.EvalDist.MeasureSpec

/-!
# Expected number of charged queries under a stateful probabilistic simulation

The construction is that of `formal/xmss/XmssSecurity/Proof/ExpectedQueryCount.lean` in
`github.com/leanEthereum/leanVM`, restated in the successful-output measure API.

`expectedSimulatedQueryCount so charged oa s` averages, over the runs of `oa` interpreted by
`so` from state `s`, the number of queries whose index satisfies `charged`.  The recursion is
structural in `oa`, and the average over one interpreted step is an integral against that
step's successful-output measure, so nothing here needs the interpretation to be lossless.

The point of the definition is `expectedSimulatedQueryCount_le_of_isQueryBoundP`: a *pathwise*
charged-query budget `IsQueryBoundP oa charged q`, which is a syntactic property of `oa` alone,
already bounds the expected charged-query count in *every* stateful probabilistic
interpretation.  `lintegral_resource_le_add_expectedSimulatedQueryCount` then converts that
count into a bound on any resource that a charged step increases by at most one, which is the
shape a charging argument consumes.

## Averaging without a measurable space on the state

Every public statement here takes its averages in the form `∫⁻ r, r ∂𝒟[f <$> mx]`: the scalar `f`
is pushed through the computation first, and the identity is integrated against the resulting
measure on `ℝ≥0∞`.  Only `ℝ≥0∞` carries a measurable space, so no statement about
`expectedSimulatedQueryCount` constrains the state type `σ`, the output type `α` or the query
ranges, and none pins a measurable-space instance.  Integrating `fun z => f z` against `𝒟[mx]`
directly would instead demand an instance on the intermediate type, and a statement that fixed
one by a `letI` could not be used directly at a concrete state type: there the ambient
`Prod.instMeasurableSpace` is a different term from `⊤` even where both of its components are
themselves `⊤`, so a consumer would have to bridge through `lintegral_evalDist_map`.  The form
used here needs no bridge.  The laws of the average are stated for any lawful measure
semantics: `lintegral_id_evalDist_map`, `lintegral_id_evalDist_map_le_of_le`,
`lintegral_id_evalDist_map_mono`, `lintegral_id_evalDist_map_add`,
`lintegral_id_evalDist_map_zero` and `lintegral_id_evalDist_map_bind` in
`VCVio.EvalDist.Defs.Measure.Core`, and `lintegral_id_evalDist_map_le_of_le_of_mem_support`,
which also needs a lawful `MonadAttach`, in `VCVio.EvalDist.Monad.Measure`.
Under `MeasureProgramLogic.toMAlgOrdered` the same average is the quantitative weakest
precondition `wp mx f`; its laws are stated at a discrete measurable space on the output type,
which is the constraint the form used here avoids.

## Related charging interfaces

This is not the only charged-query accounting in the library, and the others are not instances
of it.  `OracleComp.ProgramLogic.Relational.expectedQuerySlack` performs the same recursion, but
over `StateT (σ × Bool) (OracleComp spec')` rather than `StateT σ ProbComp`, and with three
further pieces of structure: a state-dependent per-query charge, a residual budget, and a bad
flag.  Its step returns zero both when the flag is set and when a charged query meets an
exhausted budget, where the count here returns at least the charged indicator, so it is not a
generalisation of `expectedSimulatedQueryCount` along the charge alone.  Its resource lemma
`expectedQuerySlack_resource_le` bounds the slack itself by the query budgets, for a charge
that depends on a resource growing by at most one on each charged or growth query and not at
all otherwise — closer to `expectedSimulatedQueryCount_le_of_isQueryBoundP` than to
`lintegral_resource_le_add_expectedSimulatedQueryCount`, which bounds an expected resource by
its initial value plus the expected count — and
`probEvent_bad_simulateQ_run_le_expectedQuerySlack` bounds a bad event by that slack.
`probOutput_simulateQ_run'_le_add_bad_add_slack` instead consumes `IsQueryBoundP oa charged q`
directly, by induction on `oa`, with no counting function.  No lemma relates
`expectedSimulatedQueryCount` to either sibling.  `expectedQuerySlack` is defined in the
`∑' z, Pr[= z | …] *` spelling rather than the measure API used here.
-/

public section

open MeasureTheory OracleSpec
open scoped ENNReal

namespace OracleComp

variable {ι : Type} {spec : OracleSpec ι} {α β σ : Type}

/-! ### The expected charged-query count -/

/-- The expected number of queries with a `charged` index made by `oa` when it is interpreted by
the stateful probabilistic implementation `so` started from state `s`.  Each interpreted step
contributes the indicator of its index and the average of the remaining count over that step's
successful outputs.

The step average pushes the remaining count through the interpreted step before integrating, so
the definition and its equations constrain neither `σ` nor the query ranges with a
measurable-space instance. -/
@[expose]
noncomputable def expectedSimulatedQueryCount (so : QueryImpl spec (StateT σ ProbComp))
    (charged : spec.Domain → Prop) [DecidablePred charged] (oa : OracleComp spec α)
    (s : σ) : ℝ≥0∞ :=
  OracleComp.recOn (motive := fun _ => σ → ℝ≥0∞) oa (fun _ _ => 0)
    (fun t _ tail s' =>
      (if charged t then 1 else 0) +
        ∫⁻ r, r ∂𝒟[(fun z => tail z.1 z.2) <$> (so t).run s']) s

variable (so : QueryImpl spec (StateT σ ProbComp)) (charged : spec.Domain → Prop)
  [DecidablePred charged]

@[simp]
theorem expectedSimulatedQueryCount_pure (x : α) (s : σ) :
    expectedSimulatedQueryCount so charged (pure x : OracleComp spec α) s = 0 :=
  rfl

/-- The defining equation of `expectedSimulatedQueryCount` on a query step. -/
@[simp]
theorem expectedSimulatedQueryCount_query_bind (t : spec.Domain)
    (k : spec.Range t → OracleComp spec α) (s : σ) :
    expectedSimulatedQueryCount so charged (liftM (spec.query t) >>= k) s =
      (if charged t then 1 else 0) +
        ∫⁻ r, r ∂𝒟[(fun z => expectedSimulatedQueryCount so charged (k z.1) z.2) <$>
          (so t).run s] :=
  rfl

/-- A single query contributes exactly the indicator of its index.  This is the `pure`-free
companion of `expectedSimulatedQueryCount_query_bind`, which `simp` cannot reach on its own
because `bind_pure` normalises away the `>>= k` shape that equation matches. -/
@[simp]
theorem expectedSimulatedQueryCount_query (t : spec.Domain) (s : σ) :
    expectedSimulatedQueryCount so charged
        (liftM (spec.query t) : OracleComp spec (spec.Range t)) s =
      if charged t then 1 else 0 := by
  rw [show (liftM (spec.query t) : OracleComp spec (spec.Range t)) =
      liftM (spec.query t) >>= pure from (bind_pure _).symm,
    expectedSimulatedQueryCount_query_bind]
  simp

/-- **A pathwise charged-query bound controls the expected count in every interpretation.**
`IsQueryBoundP oa charged q` constrains `oa` alone, yet bounds the expected charged-query count
of `oa` under an arbitrary stateful probabilistic implementation started from an arbitrary
state. -/
theorem expectedSimulatedQueryCount_le_of_isQueryBoundP (oa : OracleComp spec α) (s : σ) (q : ℕ)
    (hq : oa.IsQueryBoundP charged q) :
    expectedSimulatedQueryCount so charged oa s ≤ q := by
  induction oa using OracleComp.inductionOn generalizing s q with
  | pure x => simp
  | query_bind t k ih =>
    rw [isQueryBoundP_query_bind_iff] at hq
    rw [expectedSimulatedQueryCount_query_bind]
    by_cases ht : charged t
    · have hq1 : 1 ≤ q := hq.1.resolve_left (not_not.mpr ht)
      simp only [ht, ite_true]
      rw [← Nat.cast_one (R := ℝ≥0∞), ← Nat.add_sub_of_le hq1, Nat.cast_add]
      exact add_le_add le_rfl (lintegral_id_evalDist_map_le_of_le ((so t).run s) fun z =>
        ih z.1 z.2 (q - 1) (by simpa [ht] using hq.2 z.1))
    · simp only [ht, ite_false, zero_add]
      exact lintegral_id_evalDist_map_le_of_le ((so t).run s) fun z =>
        ih z.1 z.2 q (by simpa [ht] using hq.2 z.1)

/-- Enlarging the charged predicate can only increase the expected count. -/
theorem expectedSimulatedQueryCount_mono (left right : spec.Domain → Prop) [DecidablePred left]
    [DecidablePred right] (hsub : ∀ t, left t → right t) (oa : OracleComp spec α) (s : σ) :
    expectedSimulatedQueryCount so left oa s ≤ expectedSimulatedQueryCount so right oa s := by
  induction oa using OracleComp.inductionOn generalizing s with
  | pure x => simp
  | query_bind t k ih =>
    rw [expectedSimulatedQueryCount_query_bind, expectedSimulatedQueryCount_query_bind]
    refine add_le_add ?_ (lintegral_id_evalDist_map_mono _ fun z => ih z.1 z.2)
    by_cases hl : left t
    · simp [hl, hsub t hl]
    · simp [hl]

/-- The tower law: the expected count of a bind is the count of its head plus the average
continuation count over the head's interpreted outputs. -/
theorem expectedSimulatedQueryCount_bind (oa : OracleComp spec α) (ob : α → OracleComp spec β)
    (s : σ) :
    expectedSimulatedQueryCount so charged (oa >>= ob) s =
      expectedSimulatedQueryCount so charged oa s +
        ∫⁻ r, r ∂𝒟[(fun z => expectedSimulatedQueryCount so charged (ob z.1) z.2) <$>
          (simulateQ so oa).run s] := by
  induction oa using OracleComp.inductionOn generalizing s with
  | pure x => simp [simulateQ_pure]
  | query_bind t k ih =>
    rw [bind_assoc, expectedSimulatedQueryCount_query_bind,
      expectedSimulatedQueryCount_query_bind, simulateQ_bind, simulateQ_spec_query,
      StateT.run_bind, lintegral_id_evalDist_map_bind]
    simp only [ih]
    rw [lintegral_id_evalDist_map_add, add_assoc]

@[simp]
theorem expectedSimulatedQueryCount_map (f : α → β) (oa : OracleComp spec α) (s : σ) :
    expectedSimulatedQueryCount so charged (f <$> oa) s =
      expectedSimulatedQueryCount so charged oa s := by
  rw [map_eq_bind_pure_comp, expectedSimulatedQueryCount_bind]
  simp only [Function.comp_apply, expectedSimulatedQueryCount_pure,
    lintegral_id_evalDist_map_zero, add_zero]

/-- **Charging a resource against the expected count.**  A resource that grows by at most one on
each interpreted charged step, and not at all on an uncharged one, has expected final value at
most its initial value plus the expected charged-query count.  The left-hand side averages the
resource read off the final state of an interpreted run. -/
theorem lintegral_resource_le_add_expectedSimulatedQueryCount (resource : σ → ℝ≥0∞)
    (hstep : ∀ (t : spec.Domain) (s : σ), ∀ z ∈ support ((so t).run s),
      resource z.2 ≤ resource s + if charged t then 1 else 0)
    (oa : OracleComp spec α) (s : σ) :
    ∫⁻ r, r ∂𝒟[(fun z => resource z.2) <$> (simulateQ so oa).run s] ≤
      resource s + expectedSimulatedQueryCount so charged oa s := by
  induction oa using OracleComp.inductionOn generalizing s with
  | pure x => simp [simulateQ_pure]
  | query_bind t k ih =>
    rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind,
      lintegral_id_evalDist_map_bind, expectedSimulatedQueryCount_query_bind]
    calc ∫⁻ r, r ∂𝒟[(fun z => ∫⁻ r, r
              ∂𝒟[(fun w => resource w.2) <$> (simulateQ so (k z.1)).run z.2]) <$> (so t).run s]
        ≤ ∫⁻ r, r ∂𝒟[(fun z => resource z.2 +
            expectedSimulatedQueryCount so charged (k z.1) z.2) <$> (so t).run s] :=
          lintegral_id_evalDist_map_mono _ fun z => ih z.1 z.2
      _ = (∫⁻ r, r ∂𝒟[(fun z => resource z.2) <$> (so t).run s]) +
            ∫⁻ r, r ∂𝒟[(fun z => expectedSimulatedQueryCount so charged (k z.1) z.2) <$>
              (so t).run s] := lintegral_id_evalDist_map_add _ _ _
      _ ≤ (resource s + if charged t then 1 else 0) +
            ∫⁻ r, r ∂𝒟[(fun z => expectedSimulatedQueryCount so charged (k z.1) z.2) <$>
              (so t).run s] :=
          add_le_add (lintegral_id_evalDist_map_le_of_le_of_mem_support _ (hstep t s)) le_rfl
      _ = resource s + ((if charged t then 1 else 0) +
            ∫⁻ r, r ∂𝒟[(fun z => expectedSimulatedQueryCount so charged (k z.1) z.2) <$>
              (so t).run s]) := add_assoc _ _ _

/-- Expected counts add exactly over disjoint charged predicates. -/
theorem expectedSimulatedQueryCount_or_of_disjoint (left right : spec.Domain → Prop)
    [DecidablePred left] [DecidablePred right] (hdisj : ∀ t, ¬(left t ∧ right t))
    (oa : OracleComp spec α) (s : σ) :
    expectedSimulatedQueryCount so (fun t => left t ∨ right t) oa s =
      expectedSimulatedQueryCount so left oa s + expectedSimulatedQueryCount so right oa s := by
  induction oa using OracleComp.inductionOn generalizing s with
  | pure x => simp
  | query_bind t k ih =>
    rw [expectedSimulatedQueryCount_query_bind, expectedSimulatedQueryCount_query_bind,
      expectedSimulatedQueryCount_query_bind]
    have hind : (if left t ∨ right t then (1 : ℝ≥0∞) else 0) =
        (if left t then 1 else 0) + (if right t then 1 else 0) := by
      by_cases hl : left t <;> by_cases hr : right t
      · exact absurd ⟨hl, hr⟩ (hdisj t)
      all_goals simp [hl, hr]
    simp only [ih, hind]
    rw [lintegral_id_evalDist_map_add]
    ac_rfl

end OracleComp
