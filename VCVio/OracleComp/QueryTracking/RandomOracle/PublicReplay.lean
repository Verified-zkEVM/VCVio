/-
Copyright (c) 2026 VCVio Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: VCVio Contributors
-/

module

public import VCVio.OracleComp.QueryTracking.RandomOracle.Defer
public import VCVio.OracleComp.QueryTracking.RandomOracle.CachePartial

/-!
# Replaying public computations before the final draw

A verifier that uses only public hash queries can run in the partial public table of the
deferred game. The table need only be clean and extend the end of that verifier's run.
In particular, this does not require first filling any of the pending cells.
-/

public section
open OracleComp OracleSpec

namespace CanonicalGraph

variable {ι X K R : Type} {pub : OracleSpec ι}

/-- The graph query corresponding to a raw public input. -/
def publicRequests : QueryImpl pub (OracleComp (pub.withLabels X K R)) :=
  fun t => query (spec := pub.withLabels X K R) (.inl (.inl (.inr t)))

/-- A public request forwards its input to the public port of the graph oracle. -/
theorem publicRequests_apply (row : ι) :
    publicRequests (pub := pub) (X := X) (K := K) (R := R) row =
      query (spec := pub.withLabels X K R) (.inl (.inl (.inr row))) := by
  rw [publicRequests]

variable {α : Type} (G : CanonicalGraph pub X K R)
  [DecidableEq ι] [DecidableEq X] [DecidableEq K] [SampleableType R]
  [∀ t, SampleableType (pub.Range t)]

/-- A public reply remains available in a later conflict-free merged table. -/
theorem merged_public_reply (row : ι) (s : RelabelState pub X K R × List (X ⊕ K)) {z}
    (read : z ∈ support ((G.deferredImpl (.inl (.inl (.inr row)))).run s))
    {later : RelabelState pub X K R} (extendsState : z.2.1 ≤ later)
    (clean : ¬ G.Conflict later) : G.merge later row = some z.1 := by
  rw [G.deferredImpl_run_inl, support_map] at read
  obtain ⟨_, step, rfl⟩ := read
  by_cases ready : ∃ k vs, G.childVals s.1 k = some vs ∧ G.pt k vs = row
  · obtain ⟨k, vs, shape, rfl⟩ := ready
    rw [G.relabelImpl_run_pt shape, support_map] at step
    obtain ⟨u, hu, rfl⟩ := step
    obtain ⟨ext, stored⟩ := RelabelState.le_and_cell_eq_of_mem_support_drawCell hu
    rw [G.merge_apply_pt (G.childVals_mono (ext.trans extendsState) shape), extendsState.2 stored]
    rfl
  · rw [G.relabelImpl_run_pub_of_not_exists ready, support_map] at step
    obtain ⟨u, hu, rfl⟩ := step
    have stored := extendsState.1 (QueryImpl.withCaching_run_caches uniformSampleImpl _ _ _ hu)
    have ordinary : ¬∃ k vs, G.childVals later k = some vs ∧ G.pt k vs = row := by
      rintro ⟨k, vs, shape, rfl⟩
      exact clean ⟨k, vs, shape, by rw [stored]; rfl⟩
    exact (G.merge_apply_of_not_exists ordinary).trans stored

/-- A clean later merged table replays the original adaptive public caller. -/
theorem deferred_public_replay (oa : OracleComp pub α)
    {s : RelabelState pub X K R × List (X ⊕ K)} {z}
    (run : z ∈ support ((simulateQ G.deferredImpl (simulateQ publicRequests oa)).run s))
    {later : RelabelState pub X K R} (extendsState : z.2.1 ≤ later) (clean : ¬G.Conflict later) :
    simulateQ (G.merge later).toPartialImpl oa = some z.1 := by
  induction oa using OracleComp.inductionOn generalizing s z with
  | pure a =>
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at run
    subst z
    rfl
  | query_bind t k ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, publicRequests, simulateQ_HasQuery_query,
      StateT.run_bind, mem_support_bind_iff] at run
    obtain ⟨w, head, tail⟩ := run
    have ext := (G.le_of_mem_support_simulateQ_deferredImpl _ tail).trans extendsState
    rw [simulateQ_bind, simulateQ_spec_query, QueryCache.toPartialImpl_apply,
      G.merged_public_reply t s head ext clean]
    exact ih w.1 tail extendsState

end CanonicalGraph
