/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module

public import VCVio.OracleComp.QueryTracking.QueryBound.Simulation
public import VCVio.OracleComp.SimSemantics.QueryImpl.Tagged

/-!
# Query bounds through tagging

Predicate-targeted query bounds (`IsQueryBoundP`) transported along the tagging handlers of
`VCVio.OracleComp.SimSemantics.QueryImpl.Tagged`. A computation tagged with `k` makes a query
`(k', t)` exactly when `k' = k` and the computation makes the query `t`, so a bound on the
tagged computation is a bound on the original one for the predicate read at the tag `k`
(`isQueryBoundP_simulateQ_tagWith_iff`). In particular a computation tagged `k` spends nothing
on a predicate that no `k`-tagged query satisfies (`isQueryBoundP_simulateQ_tagWith_zero`).

In a composed program whose parties are tagged differently, these two facts turn the budget of
one party into a budget of the whole program for the predicate selecting that party's tag.
-/

public section

open OracleSpec QueryImpl

universe u

namespace OracleComp

variable {ι K : Type u} {spec : OracleSpec.{u, u} ι} {α : Type u}

/-- A computation tagged with `k` is `p`-bounded by `n` exactly when the computation is bounded
by `n` for the predicate `p` read at the tag `k`. -/
theorem isQueryBoundP_simulateQ_tagWith_iff (k : K) (p : K × ι → Prop) [DecidablePred p]
    (oa : OracleComp spec α) (n : ℕ) :
    IsQueryBoundP (simulateQ (tagWith k) oa) p n ↔ IsQueryBoundP oa (fun t => p (k, t)) n := by
  induction oa using OracleComp.inductionOn generalizing n with
  | pure x => simp
  | query_bind t mx ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, tagWith_apply, isQueryBoundP_query_bind_iff,
      ih]

/-- Forgetting the tags of a computation, the result is `p`-bounded by `n` exactly when the
tagged computation is bounded by `n` for `p` read on the untagged query. -/
theorem isQueryBoundP_simulateQ_untag_iff (p : ι → Prop) [DecidablePred p]
    (oa : OracleComp (spec.tagged K) α) (n : ℕ) :
    IsQueryBoundP (simulateQ untag oa) p n ↔ IsQueryBoundP oa (fun kt => p kt.2) n := by
  induction oa using OracleComp.inductionOn generalizing n with
  | pure x => simp
  | query_bind t mx ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, untag_apply, isQueryBoundP_query_bind_iff,
      ih]

/-- A `p`-bound on a computation is a `q`-bound on the computation tagged with `k`, whenever
every `k`-tagged `q`-query is a `p`-query. -/
theorem IsQueryBoundP.simulateQ_tagWith {k : K} {p : ι → Prop} [DecidablePred p]
    {q : K × ι → Prop} [DecidablePred q] {oa : OracleComp spec α} {n : ℕ}
    (h : IsQueryBoundP oa p n) (hq : ∀ t, q (k, t) → p t) :
    IsQueryBoundP (simulateQ (tagWith k) oa) q n :=
  (isQueryBoundP_simulateQ_tagWith_iff k q oa n).2 (h.of_imp hq)

/-- A computation tagged with `k` makes no `q`-query when no `k`-tagged query satisfies `q`. -/
theorem isQueryBoundP_simulateQ_tagWith_zero {k : K} {q : K × ι → Prop} [DecidablePred q]
    (hq : ∀ t, ¬ q (k, t)) (oa : OracleComp spec α) :
    IsQueryBoundP (simulateQ (tagWith k) oa) q 0 :=
  (isQueryBoundP_false oa 0).simulateQ_tagWith fun t h => hq t h

end OracleComp
