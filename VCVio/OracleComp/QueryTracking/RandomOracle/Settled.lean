/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module

public import VCVio.OracleComp.QueryTracking.RandomOracle.Defer
public import VCVio.OracleComp.QueryTracking.RandomOracle.CachePartial

/-!
# Settled public programs in the deferred relabelled game

A program over the public oracle of a canonical graph `G`, run inside the deferred game
`CanonicalGraph.deferredImpl`, issues each of its queries as a public query of the relabelled game.
Such a query is answered either by the label of a node whose children are drawn at their values,
or by the public cache; in both cases the answer is then the entry of the merged cache
`CanonicalGraph.merge` at the query's point. Every later step and the end fill
`RelabelState.endFill` only extend the state, and off a conflict of the larger state extending
the state only adds entries to the merged cache (`CanonicalGraph.merge_le_merge`). So, off a
conflict of any state extending the final state, the merged cache settles the whole program:
reading it through `QueryCache.toPartialImpl` replays the program to the output of the run. None
of this needs every drawn label to belong to a node with drawn children
(`CanonicalGraph.LabelsComplete`), which fails in the deferred game once a label is read before
its children are drawn.

The replay is an instance of `OracleComp.simulateQ_toPartialImpl_of_mem_support_run_simulateQ`,
with the merged caches of the conflict-free states extending a state as its admissible caches.

## Main statements

- `CanonicalGraph.simulateQ_toPartialImpl_merge_fst_of_mem_support_deferredImpl`: for a public
  oracle `spec₁ + spec₂`, a program over `spec₁`, run in the deferred game from any state, is
  replayed to its output by the `spec₁` part of the merged cache of every conflict-free state
  extending the final state.
- `CanonicalGraph.simulateQ_toPartialImpl_of_mem_support_deferredImpl`: the same replay for any
  handler into the deferred game whose every query leaves its answer in a cache read off the
  conflict-free states extending the post-state.
- `CanonicalGraph.merge_apply_of_mem_support_relabelImpl_pub`: a public query of the relabelled
  game leaves its answer in the merged cache of the post-state.
- `CanonicalGraph.fst_apply_of_mem_support_deferredImpl_pub`: a public query of the deferred game
  at a point that is no node's point leaves its answer in the public cache.
-/

public section

open OracleComp OracleSpec

namespace CanonicalGraph

section

variable {ι : Type} {pub : OracleSpec ι} {X K R : Type} (G : CanonicalGraph pub X K R)
  [DecidableEq ι] [DecidableEq X] [DecidableEq K] [SampleableType R]
  [∀ t, SampleableType (pub.Range t)]

/-- A public query of the relabelled game leaves its answer at its point in the merged cache of
the post-state. -/
theorem merge_apply_of_mem_support_relabelImpl_pub {t : ι} {st : RelabelState pub X K R}
    {z : pub.Range t × RelabelState pub X K R}
    (hz : z ∈ support ((G.relabelImpl (.inl (.inr t))).run st)) : G.merge z.2 t = some z.1 := by
  by_cases ht : ∃ k vs, G.childVals st k = some vs ∧ G.pt k vs = t
  · obtain ⟨k, vs, hk, rfl⟩ := ht
    rw [G.relabelImpl_run_pt hk, support_map] at hz
    obtain ⟨w, hw, rfl⟩ := hz
    obtain ⟨hle, hw⟩ := RelabelState.le_and_cell_eq_of_mem_support_drawCell hw
    rw [Prod.map_snd, Prod.map_fst, id_eq, G.merge_apply_pt (G.childVals_mono hle hk), hw]
    rfl
  · rw [G.relabelImpl_run_pub_of_not_exists ht, support_map] at hz
    obtain ⟨w, hw, rfl⟩ := hz
    have hcv : ∀ k, G.childVals (w.2, st.2) k = G.childVals st k :=
      fun _ ↦ G.childVals_congr fun _ _ ↦ rfl
    rw [G.merge_apply_of_not_exists (st := (w.2, st.2)) (by simpa only [hcv] using ht)]
    exact QueryImpl.withCaching_run_caches _ _ _ _ hw

/-- A public query of the deferred game at a point that is no node's point leaves its answer at
that point in the public cache. -/
theorem fst_apply_of_mem_support_deferredImpl_pub {t : ι} (ht : ∀ k vs, G.pt k vs ≠ t)
    {s : RelabelState pub X K R × List (X ⊕ K)} {z}
    (hz : z ∈ support ((G.deferredImpl (.inl (.inl (.inr t)))).run s)) :
    z.2.1.1 t = some z.1 := by
  rw [deferredImpl_run_inl, G.relabelImpl_run_pub_of_not_exists fun ⟨k, vs, _, h⟩ ↦ ht k vs h,
    Functor.map_map, support_map] at hz
  obtain ⟨w, hw, rfl⟩ := hz
  exact QueryImpl.withCaching_run_caches _ _ _ _ hw

/-- If every query `t` of a handler `h`, run in the deferred game, returns an answer that `rd st`
holds at `t` for every conflict-free state `st` extending its post-state, then a program run
through `h` returns its replay on `rd st` for every conflict-free state `st` extending its final
state. -/
theorem simulateQ_toPartialImpl_of_mem_support_deferredImpl {κ : Type} {spec : OracleSpec κ}
    (h : QueryImpl spec (OracleComp (pub.withLabels X K R)))
    (rd : RelabelState pub X K R → spec.QueryCache)
    (hstep : ∀ t s z, z ∈ support ((simulateQ G.deferredImpl (h t)).run s) →
      ∀ st, z.2.1 ≤ st → ¬G.Conflict st → rd st t = some z.1)
    {α : Type} (oa : OracleComp spec α) {s : RelabelState pub X K R × List (X ⊕ K)}
    {z : α × (RelabelState pub X K R × List (X ⊕ K))}
    (hz : z ∈ support ((simulateQ G.deferredImpl (simulateQ h oa)).run s))
    {st : RelabelState pub X K R} (hle : z.2.1 ≤ st) (hc : ¬G.Conflict st) :
    simulateQ (rd st).toPartialImpl oa = some z.1 := by
  rw [← QueryImpl.simulateQ_compose] at hz
  exact simulateQ_toPartialImpl_of_mem_support_run_simulateQ _
    (fun s ↦ rd '' {st | s.1 ≤ st ∧ ¬G.Conflict st})
    (fun t s z hz _ ⟨st, ⟨hle, hc⟩, hst⟩ ↦
      ⟨⟨st, ⟨(G.le_of_mem_support_simulateQ_deferredImpl (h t) hz).trans hle, hc⟩, hst⟩,
        hst ▸ hstep t s z hz st hle hc⟩)
    oa hz ⟨st, ⟨hle, hc⟩, rfl⟩

end

section LeftSummand

variable {X K R : Type} [DecidableEq X] [DecidableEq K] [SampleableType R] {κ₁ κ₂ : Type}
  [DecidableEq κ₁] [DecidableEq κ₂] {spec₁ : OracleSpec κ₁} {spec₂ : OracleSpec κ₂}
  [∀ t, SampleableType ((spec₁ + spec₂).Range t)] (G : CanonicalGraph (spec₁ + spec₂) X K R)

/-- **Settledness.** For a public oracle `spec₁ + spec₂`, a program over `spec₁`, run in the
deferred game, returns its replay on the `spec₁` part of the merged cache of every conflict-free
state extending the final state. -/
theorem simulateQ_toPartialImpl_merge_fst_of_mem_support_deferredImpl {α : Type}
    (oa : OracleComp spec₁ α)
    {s : RelabelState (spec₁ + spec₂) X K R × List (X ⊕ K)}
    {z : α × (RelabelState (spec₁ + spec₂) X K R × List (X ⊕ K))}
    (hz : z ∈ support ((simulateQ G.deferredImpl (simulateQ (HasQuery.toQueryImpl
      (spec := spec₁) (m := OracleComp ((spec₁ + spec₂).withLabels X K R))) oa)).run s))
    {st : RelabelState (spec₁ + spec₂) X K R} (hle : z.2.1 ≤ st) (hc : ¬G.Conflict st) :
    simulateQ (G.merge st).fst.toPartialImpl oa = some z.1 := by
  refine G.simulateQ_toPartialImpl_of_mem_support_deferredImpl _ (fun st ↦ (G.merge st).fst)
    (fun t s z hz st hle hc ↦ ?_) oa hz hle hc
  rw [show HasQuery.toQueryImpl (spec := spec₁)
      (m := OracleComp ((spec₁ + spec₂).withLabels X K R)) t =
      liftM (((spec₁ + spec₂).withLabels X K R).query (.inl (.inl (.inr (.inl t))))) from rfl,
    simulateQ_spec_query, deferredImpl_run_inl, support_map] at hz
  obtain ⟨w, hw, rfl⟩ := hz
  exact (QueryCache.fst_apply _ _).trans
    (G.merge_le_merge hle hc (G.merge_apply_of_mem_support_relabelImpl_pub hw))

end LeftSummand

end CanonicalGraph
