/-
Copyright (c) 2026 VCVio Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: VCVio Contributors
-/

module

public import VCVio.OracleComp.SimSemantics.StateT.StateProjection
public import VCVio.OracleComp.QueryTracking.QueryBound.Basic
public import VCVio.OracleComp.EvalDist.Measure

/-!
# Projecting the state of an adaptive oracle computation

`AllQueriesSatisfy p P` restricts the one-step comparison to requests permitted by `P`.
The source handler must preserve the initial invariant on every supported response.
The resulting equality in distribution covers both the caller's reply and the projected final state.
-/

public section

open OracleSpec

namespace OracleComp

/-- Project the entire result and final state of an adaptive caller.
Only its permitted queries and supported intermediate states need matching simulations. -/
theorem AllQueriesSatisfy.evalDist_map_run
    {ι σ τ α : Type} {spec : OracleSpec ι} {P : ι → Prop}
    {p : OracleComp spec α} (queries : AllQueriesSatisfy p P)
    (source : QueryImpl spec (StateT σ ProbComp)) (target : QueryImpl spec (StateT τ ProbComp))
    (proj : σ → τ) (I : σ → Prop)
    (preserves : ∀ t, P t → ∀ s, I s → ∀ z ∈ support ((source t).run s), I z.2)
    (same : ∀ t, P t → ∀ s, I s →
      (Prod.map id proj <$> (source t).run s) =ᵈ (target t).run (proj s))
    (s : σ) (initial : I s) :
    (Prod.map id proj <$> (simulateQ source p).run s) =ᵈ (simulateQ target p).run (proj s) := by
  induction p using OracleComp.inductionOn generalizing s with
  | pure x => simp
  | query_bind t k ih =>
    obtain ⟨allowed, next⟩ := (allQueriesSatisfy_query_bind_iff t k P).mp queries
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, map_bind]
    refine (OracleComp.EvalDistEq.bind_congr_of_support ((source t).run s) (fun z hz =>
      ih z.1 (next z.1) z.2 (preserves t allowed s initial z hz))).trans ?_
    have eq := (same t allowed s initial).bind_left
      (fun z => (simulateQ target (k z.1)).run z.2)
    simpa only [bind_map_left, Prod.map, id_eq] using eq

end OracleComp
