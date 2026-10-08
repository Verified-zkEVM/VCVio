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
public import VCVio.OracleComp.SimSemantics.StateT.StateProjection

/-!
# Expected charged-query count of a simulated computation

`expectedSimulatedQueryCount so charged oa s` is the expected number of queries of `oa` whose
index satisfies `charged` when `oa` is interpreted by a stateful implementation
`so : QueryImpl spec (StateT σ m)` started from state `s`, for any monad `m` with a lawful
successful-output measure semantics. It is defined by structural recursion on `oa`: each
interpreted step contributes the indicator of its index plus the expectation, under the step's
successful-output measure, of the count of the continuation. The implementation need not be
lossless; a run that fails contributes the charged queries made up to and including the failing
step. Expectations are written `∫⁻ r, r ∂𝒟[f <$> mx]`, so no statement places a measurable-space
instance on the state type, the output type or the query ranges.

## Main results

* `expectedSimulatedQueryCount_le_of_isQueryBoundP`: a pathwise bound `IsQueryBoundP oa charged q`
  bounds the expected count by `q` under every implementation and from every initial state;
  `mul_expectedSimulatedQueryCount_le_of_isQueryBoundP` is its form for a loss `ε` per query.
* `expectedSimulatedQueryCount_bind`: the expected count of a bind is the count of its head plus
  the expected count of its continuation over the head's interpreted run.
* `lintegral_resource_le_add_expectedSimulatedQueryCount`: a resource on the state that grows by
  at most one on each charged step and not at all on an uncharged one has expected final value at
  most its initial value plus the expected count.
* `expectedSimulatedQueryCount_extendState`: extending the implementation by a passive auxiliary
  state (`QueryImpl.extendState`) does not change the expected count, so a count of the extended
  implementation is the count of the base one.
* `expectedSimulatedQueryCount_mono` and `expectedSimulatedQueryCount_or_of_disjoint`:
  monotonicity in the charged predicate, and additivity over disjoint charged predicates.
* `lintegral_run_le_of_isQueryBoundP`: a potential `Φ n` on the state, indexed by a remaining
  budget `n` of charged queries, whose expectation a charged step raises by at most one budget
  level and an uncharged step not at all, has expected final `Φ 0` at most `Φ n` of the initial
  state when the computation makes at most `n` charged queries.
  `prEvent_run_le_of_isQueryBoundP` is its Markov form, for an event on which `Φ 0` is at least
  `1`. A potential that does not depend on `n` gives the plain supermartingale bound, and
  `Φ n s = resource s + n` gives the expected-resource bound that
  `lintegral_resource_le_add_expectedSimulatedQueryCount` and
  `expectedSimulatedQueryCount_le_of_isQueryBoundP` combine to. It bounds products of per-query
  lotteries,
  such as the probability that `u` designated values are all hit by at most `n` fresh uniform
  draws from `Y`: the potential is `n ^ u / |Y| ^ u` with `u` the number of values still
  pending, and its step inequality `n ^ u + u * n ^ (u - 1) ≤ (n + 1) ^ u` is
  `pow_add_mul_le_add_pow`.

## Related notions

`HasQuery.expectedQueryCost` is the expected weighted query cost of a computation run in a
runtime monad with `[EvalDistSemantics m]`, which `StateT σ m` is not.
`OracleComp.ProgramLogic.Relational.expectedQuerySlack` accumulates a state-dependent charge over
`StateT (σ × Bool) (OracleComp spec')` against a residual budget and a bad flag.
`OracleComp.IsPotentialStep` charges the first firing of a bad state predicate to a potential that
grows along every path, against a budget on that potential rather than on the number of queries;
it bounds sums of per-step firing masses, not products.

The construction follows `formal/xmss/XmssSecurity/Proof/ExpectedQueryCount.lean` in
`github.com/leanEthereum/leanVM`.
-/

public section

open MeasureTheory OracleSpec
open scoped ENNReal

universe v

namespace OracleComp

variable {ι : Type} {spec : OracleSpec ι} {α β σ : Type} {m : Type → Type v} [Monad m]
  [EvalDistSemantics m]

/-! ## The expected charged-query count -/

/-- The expected number of queries with a `charged` index made by `oa` when it is interpreted by
the stateful implementation `so` started from state `s`. Each interpreted step contributes the
indicator of its index plus the expectation, under that step's successful-output measure, of the
expected count of the continuation. -/
@[expose]
noncomputable def expectedSimulatedQueryCount (so : QueryImpl spec (StateT σ m))
    (charged : spec.Domain → Prop) [DecidablePred charged] (oa : OracleComp spec α)
    (s : σ) : ℝ≥0∞ :=
  OracleComp.recOn (motive := fun _ => σ → ℝ≥0∞) oa (fun _ _ => 0)
    (fun t _ tail s' =>
      (if charged t then 1 else 0) +
        ∫⁻ r, r ∂𝒟[(fun z => tail z.1 z.2) <$> (so t).run s']) s

variable (so : QueryImpl spec (StateT σ m)) (charged : spec.Domain → Prop)
  [DecidablePred charged]

/-- A pure computation makes no charged queries. -/
@[simp]
theorem expectedSimulatedQueryCount_pure (x : α) (s : σ) :
    expectedSimulatedQueryCount so charged (pure x : OracleComp spec α) s = 0 :=
  rfl

/-- The expected count of a query followed by a continuation is the indicator of the query's
index plus the expectation of the continuation's expected count over the interpreted query. -/
@[simp]
theorem expectedSimulatedQueryCount_query_bind (t : spec.Domain)
    (k : spec.Range t → OracleComp spec α) (s : σ) :
    expectedSimulatedQueryCount so charged (liftM (spec.query t) >>= k) s =
      (if charged t then 1 else 0) +
        ∫⁻ r, r ∂𝒟[(fun z => expectedSimulatedQueryCount so charged (k z.1) z.2) <$>
          (so t).run s] :=
  rfl

variable [LawfulMonad m] [LawfulEvalDistSemantics m]

/-- The expected count of a single query is the indicator of its index. -/
@[simp]
theorem expectedSimulatedQueryCount_query (t : spec.Domain) (s : σ) :
    expectedSimulatedQueryCount so charged
        (liftM (spec.query t) : OracleComp spec (spec.Range t)) s =
      if charged t then 1 else 0 := by
  rw [← bind_pure (liftM (spec.query t) : OracleComp spec (spec.Range t)),
    expectedSimulatedQueryCount_query_bind]
  simp only [expectedSimulatedQueryCount_pure, lintegral_id_evalDist_map_zero, add_zero]

/-- A pathwise bound of `q` charged queries on `oa` bounds its expected charged-query count by `q`
under every stateful implementation and from every initial state. -/
theorem expectedSimulatedQueryCount_le_of_isQueryBoundP (oa : OracleComp spec α) (s : σ) (q : ℕ)
    (hq : oa.IsQueryBoundP charged q) :
    expectedSimulatedQueryCount so charged oa s ≤ q := by
  induction oa using OracleComp.inductionOn generalizing s q with
  | pure x => simp only [expectedSimulatedQueryCount_pure, zero_le]
  | query_bind t k ih =>
    rw [isQueryBoundP_query_bind_iff] at hq
    rw [expectedSimulatedQueryCount_query_bind]
    by_cases ht : charged t
    · obtain _ | q := q
      · exact absurd (hq.1.resolve_left (not_not_intro ht)) (lt_irrefl 0)
      simp only [ht, ↓reduceIte, Nat.add_sub_cancel] at hq ⊢
      rw [Nat.cast_succ, add_comm (q : ℝ≥0∞)]
      exact add_le_add le_rfl
        (lintegral_id_evalDist_map_le_of_le _ fun z => ih z.1 z.2 q (hq.2 z.1))
    · simp only [ht, ↓reduceIte, zero_add] at hq ⊢
      exact lintegral_id_evalDist_map_le_of_le _ fun z => ih z.1 z.2 q (hq.2 z.1)

/-- Under a pathwise bound of `q` charged queries on `oa`, `ε` times its expected charged-query
count under any stateful implementation and from any initial state is at most `q * ε`. -/
theorem mul_expectedSimulatedQueryCount_le_of_isQueryBoundP {oa : OracleComp spec α} {q : ℕ}
    (hq : oa.IsQueryBoundP charged q) (s : σ) (ε : ℝ≥0∞) :
    ε * expectedSimulatedQueryCount so charged oa s ≤ q * ε := by
  rw [mul_comm]
  gcongr
  exact expectedSimulatedQueryCount_le_of_isQueryBoundP so charged oa s q hq

/-- The expected charged-query count is monotone in the charged predicate. -/
theorem expectedSimulatedQueryCount_mono {left right : spec.Domain → Prop} [DecidablePred left]
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

/-- The expected count of a bind is the expected count of its head plus the expectation, over
the head's interpreted run, of the expected count of the continuation. -/
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

/-- Mapping over the output does not change the expected count. -/
@[simp]
theorem expectedSimulatedQueryCount_map (f : α → β) (oa : OracleComp spec α) (s : σ) :
    expectedSimulatedQueryCount so charged (f <$> oa) s =
      expectedSimulatedQueryCount so charged oa s := by
  rw [map_eq_bind_pure_comp, expectedSimulatedQueryCount_bind]
  simp only [Function.comp_apply, expectedSimulatedQueryCount_pure,
    lintegral_id_evalDist_map_zero, add_zero]

omit [LawfulEvalDistSemantics m] in
/-- Extending the implementation by a passive auxiliary state does not change the expected
charged-query count: under `so.extendState aux`, from any auxiliary value `r`, it is the count
under `so` from the base state. -/
theorem expectedSimulatedQueryCount_extendState {Q : Type}
    (aux : (t : spec.Domain) → σ → spec.Range t → σ → Q → Q) (oa : OracleComp spec α) (s : σ)
    (r : Q) :
    expectedSimulatedQueryCount (so.extendState aux) charged oa (s, r) =
      expectedSimulatedQueryCount so charged oa s := by
  induction oa using OracleComp.inductionOn generalizing s r with
  | pure x => simp only [expectedSimulatedQueryCount_pure]
  | query_bind t k ih =>
    rw [expectedSimulatedQueryCount_query_bind, expectedSimulatedQueryCount_query_bind,
      QueryImpl.extendState_apply]
    congr 1
    simp only [map_bind, map_pure, ih]
    rw [map_eq_bind_pure_comp]
    rfl

/-- A resource on the state that grows by at most one on each interpreted charged step, and not
at all on an uncharged one, has expected value on the final state of the interpreted run at most
its value on the initial state plus the expected charged-query count. -/
theorem lintegral_resource_le_add_expectedSimulatedQueryCount [MonadAttach m]
    [WeaklyLawfulMonadAttach m] (resource : σ → ℝ≥0∞)
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

/-- The expected count for the disjunction of two disjoint charged predicates is the sum of
their expected counts. -/
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

/-! ## A potential indexed by the remaining budget -/

/-- **The budgeted expected-potential bound.**  `Φ n s` is a potential on the state, indexed by a
remaining budget `n` of charged queries and monotone in it.  If one interpreted step at index `t`
from state `s` has expected `Φ n` on its final state at most `Φ (n + 1) s` when `t` is charged
and at most `Φ n s` otherwise, then a computation making at most `n` charged queries has
expected `Φ 0` on the final state of its interpreted run at most `Φ n s`.

The potential is spent along the run: each charged step may raise the expectation by the
difference between two consecutive budget levels, and an uncharged step may not raise it at all.
-/
theorem lintegral_run_le_of_isQueryBoundP (Φ : ℕ → σ → ℝ≥0∞)
    (hmono : ∀ s, Monotone fun n => Φ n s)
    (hstep : ∀ (t : spec.Domain) (s : σ) (n : ℕ),
      ∫⁻ r, r ∂𝒟[(fun z => Φ n z.2) <$> (so t).run s] ≤
        Φ (n + if charged t then 1 else 0) s)
    (oa : OracleComp spec α) (n : ℕ) (hq : oa.IsQueryBoundP charged n) (s : σ) :
    ∫⁻ r, r ∂𝒟[(fun z => Φ 0 z.2) <$> (simulateQ so oa).run s] ≤ Φ n s := by
  induction oa using OracleComp.inductionOn generalizing s n with
  | pure x =>
    simpa [simulateQ_pure] using hmono s (Nat.zero_le n)
  | query_bind t k ih =>
    rw [isQueryBoundP_query_bind_iff] at hq
    rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, lintegral_id_evalDist_map_bind]
    by_cases ht : charged t
    · obtain _ | n := n
      · exact absurd (hq.1.resolve_left (not_not_intro ht)) (lt_irrefl 0)
      simp only [ht, ↓reduceIte, Nat.add_sub_cancel] at hq
      refine (lintegral_id_evalDist_map_mono _ fun z : spec.Range t × σ =>
        ih z.1 n (hq.2 z.1) z.2).trans ?_
      simpa only [ht, ↓reduceIte] using hstep t s n
    · simp only [ht, ↓reduceIte] at hq
      refine (lintegral_id_evalDist_map_mono _ fun z : spec.Range t × σ =>
        ih z.1 n (hq.2 z.1) z.2).trans ?_
      simpa only [ht, ↓reduceIte, add_zero] using hstep t s n

/-- **The budgeted expected-potential bound, as an event probability.**  `Φ n s` is a potential
on the state, indexed by a remaining budget `n` of charged queries and monotone in it, whose
expectation one interpreted step raises from `Φ n` to at most `Φ (n + 1)` when its index is
charged and not at all otherwise.  Then an event `E` of the output and final state on which
`Φ 0` is at least `1` has probability at most `Φ n s` after a computation making at most `n`
charged queries. -/
theorem prEvent_run_le_of_isQueryBoundP (Φ : ℕ → σ → ℝ≥0∞)
    (hmono : ∀ s, Monotone fun n => Φ n s)
    (hstep : ∀ (t : spec.Domain) (s : σ) (n : ℕ),
      ∫⁻ r, r ∂𝒟[(fun z => Φ n z.2) <$> (so t).run s] ≤
        Φ (n + if charged t then 1 else 0) s)
    (E : α × σ → Prop) (hE : ∀ z, E z → 1 ≤ Φ 0 z.2)
    (oa : OracleComp spec α) (n : ℕ) (hq : oa.IsQueryBoundP charged n) (s : σ) :
    Pr{let z ← (simulateQ so oa).run s}[E z] ≤ Φ n s :=
  (prEvent_le_lintegral_id_evalDist_map _ hE).trans
    (lintegral_run_le_of_isQueryBoundP so charged Φ hmono hstep oa n hq s)

end OracleComp
