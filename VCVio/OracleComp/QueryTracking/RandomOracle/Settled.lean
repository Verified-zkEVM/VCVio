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
`RelabelState.endFill` only extend the state, and extending the state can change an entry of the
merged cache only by completing the children of a node at a point the public cache holds, which
is a `CanonicalGraph.Conflict`. So, off a conflict of any state extending the final state, the
merged cache settles the whole program: reading it through `QueryCache.toPartialImpl` replays the
program to the output of the run. None of this needs every drawn label to belong to a node with
drawn children (`CanonicalGraph.LabelsComplete`), which fails in the deferred game once a label
is read before its children are drawn.

## Main statements

- `CanonicalGraph.merge_apply_of_le` and `CanonicalGraph.merge_le_merge`: off a conflict of the
  larger state, the merged cache is monotone in the state.
- `CanonicalGraph.merge_le_merge_of_mem_support_endFill` and
  `CanonicalGraph.simulateQ_toPartialImpl_merge_of_mem_support_endFill`: the merged cache before
  the end fill is below the merged cache after it, off a conflict after it, so a replay settled
  before the end fill is settled after it.
- `CanonicalGraph.simulateQ_toPartialImpl_merge_of_mem_support_deferredImpl`: a program over the
  public oracle, run in the deferred game from any state, is replayed to its output by the merged
  cache of every conflict-free state extending the final state.
- `CanonicalGraph.simulateQ_toPartialImpl_merge_fst_of_mem_support_deferredImpl`: the same for a
  program over the left summand `spec₁` of a public oracle `spec₁ + spec₂`, read on the `spec₁`
  part of the merged cache.
- `CanonicalGraph.simulateQ_toPartialImpl_of_mem_support_deferredImpl`: the common form, for any
  handler whose every query leaves its answer in a cache read off conflict-free extensions.
- `SecretEncoding.le_merge_of_forall_enc_eq_none`: a public cache that holds no encoded point is
  below its rebuilt real cache.
-/

public section

open OracleComp OracleSpec

namespace CanonicalGraph

section

variable {ι : Type} {pub : OracleSpec ι} {X K R : Type} (G : CanonicalGraph pub X K R)

/-! ## Monotonicity of the merged cache -/

/-- Off a conflict of `st`, the merged cache of `st` has every entry of the merged cache of a
state `st₀ ≤ st`. -/
theorem merge_apply_of_le {st₀ st : RelabelState pub X K R} (hle : st₀ ≤ st)
    (hc : ¬G.Conflict st) {t : ι} {v : pub.Range t} (h₀ : G.merge st₀ t = some v) :
    G.merge st t = some v := by
  by_cases ht₀ : ∃ k vs, G.childVals st₀ k = some vs ∧ G.pt k vs = t
  · obtain ⟨k, vs, hk, rfl⟩ := ht₀
    rw [G.merge_apply_pt hk] at h₀
    rw [G.merge_apply_pt (G.childVals_mono hle hk)]
    obtain ⟨ℓ, hℓ, rfl⟩ := Option.map_eq_some_iff.1 h₀
    rw [hle.2 hℓ]
    rfl
  · rw [G.merge_apply_of_not_exists ht₀] at h₀
    by_cases ht : ∃ k vs, G.childVals st k = some vs ∧ G.pt k vs = t
    · obtain ⟨k, vs, hk, rfl⟩ := ht
      exact absurd ⟨k, vs, hk, by rw [hle.1 h₀]; rfl⟩ hc
    · rw [G.merge_apply_of_not_exists ht, hle.1 h₀]

/-- Off a conflict of `st`, the merged cache of a state `st₀ ≤ st` is below the merged cache of
`st`. -/
theorem merge_le_merge {st₀ st : RelabelState pub X K R} (hle : st₀ ≤ st)
    (hc : ¬G.Conflict st) : G.merge st₀ ≤ G.merge st :=
  fun _ _ h ↦ G.merge_apply_of_le hle hc h

/-- Off a conflict after the end fill, the merged cache before the end fill is below the merged
cache after it. -/
theorem merge_le_merge_of_mem_support_endFill [DecidableEq X] [DecidableEq K] [SampleableType R]
    {s : RelabelState pub X K R × List (X ⊕ K)} {st : RelabelState pub X K R}
    (hst : st ∈ support (RelabelState.endFill s)) (hc : ¬G.Conflict st) :
    G.merge s.1 ≤ G.merge st :=
  G.merge_le_merge (RelabelState.le_of_mem_support_endFill hst) hc

/-- A replay settled on the merged cache before the end fill is settled, at the same value, on
the merged cache after it, off a conflict after the end fill. -/
theorem simulateQ_toPartialImpl_merge_of_mem_support_endFill [DecidableEq X] [DecidableEq K]
    [SampleableType R] {α : Type}
    {s : RelabelState pub X K R × List (X ⊕ K)} {st : RelabelState pub X K R}
    (hst : st ∈ support (RelabelState.endFill s)) (hc : ¬G.Conflict st)
    (oa : OracleComp pub α) {a : α} (ha : simulateQ (G.merge s.1).toPartialImpl oa = some a) :
    simulateQ (G.merge st).toPartialImpl oa = some a :=
  QueryCache.simulateQ_toPartialImpl_mono (G.merge_le_merge_of_mem_support_endFill hst hc) oa ha

/-! ## Settled public queries -/

variable [DecidableEq ι] [DecidableEq X] [DecidableEq K] [SampleableType R]
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

/-- A run of the deferred game extends the relabelled state. -/
theorem le_of_mem_support_simulateQ_deferredImpl {α : Type}
    (oa : OracleComp (pub.withLabels X K R) α) {s : RelabelState pub X K R × List (X ⊕ K)}
    {z : α × (RelabelState pub X K R × List (X ⊕ K))}
    (hz : z ∈ support ((simulateQ G.deferredImpl oa).run s)) : s.1 ≤ z.2.1 := by
  refine OracleComp.simulateQ_run_preservesInv _ (fun s' ↦ s.1 ≤ s'.1) ?_ oa s le_rfl z hz
  intro t s' hs' z' hz'
  refine hs'.trans ?_
  rcases t with t | c | k
  · rw [deferredImpl_run_inl, support_map] at hz'
    obtain ⟨w, hw, rfl⟩ := hz'
    exact G.le_of_mem_support_relabelImpl hw
  · rw [deferredImpl_run_touch, support_pure, Set.mem_singleton_iff] at hz'
    exact hz' ▸ le_rfl
  · rw [deferredImpl_run_read, support_map] at hz'
    obtain ⟨w, hw, rfl⟩ := hz'
    exact (RelabelState.le_and_cell_eq_of_mem_support_drawCell hw).1

/-! ## Settled programs -/

/-- Let a handler `h` issue each query `t` in the deferred game as a run whose answer `rd st`
holds at `t`, for every conflict-free state `st` extending the post-state. Then the output of a
program run through `h` is its replay on `rd st`, for every conflict-free state `st` extending
the final state. -/
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
  induction oa using OracleComp.inductionOn generalizing s with
  | pure x =>
    rw [simulateQ_pure, simulateQ_pure, StateT.run_pure, support_pure,
      Set.mem_singleton_iff] at hz
    exact hz ▸ rfl
  | query_bind t k ih =>
    rw [simulateQ_bind, simulateQ_spec_query, simulateQ_bind, StateT.run_bind,
      mem_support_bind_iff] at hz
    obtain ⟨z₁, h₁, h₂⟩ := hz
    rw [simulateQ_bind, simulateQ_spec_query, QueryCache.toPartialImpl_apply,
      hstep t s z₁ h₁ st ((G.le_of_mem_support_simulateQ_deferredImpl _ h₂).trans hle) hc]
    exact ih z₁.1 h₂

/-- **Settledness.** A program over the public oracle, run in the deferred game, returns its
replay on the merged cache of every conflict-free state extending the final state. -/
theorem simulateQ_toPartialImpl_merge_of_mem_support_deferredImpl {α : Type}
    (oa : OracleComp pub α) {s : RelabelState pub X K R × List (X ⊕ K)}
    {z : α × (RelabelState pub X K R × List (X ⊕ K))}
    (hz : z ∈ support ((simulateQ G.deferredImpl (simulateQ (HasQuery.toQueryImpl (spec := pub)
      (m := OracleComp (pub.withLabels X K R))) oa)).run s))
    {st : RelabelState pub X K R} (hle : z.2.1 ≤ st) (hc : ¬G.Conflict st) :
    simulateQ (G.merge st).toPartialImpl oa = some z.1 := by
  refine G.simulateQ_toPartialImpl_of_mem_support_deferredImpl _ G.merge
    (fun t s z hz st hle hc ↦ ?_) oa hz hle hc
  rw [show HasQuery.toQueryImpl (spec := pub) (m := OracleComp (pub.withLabels X K R)) t =
      liftM ((pub.withLabels X K R).query (.inl (.inl (.inr t)))) from rfl,
    simulateQ_spec_query, deferredImpl_run_inl, support_map] at hz
  obtain ⟨w, hw, rfl⟩ := hz
  exact G.merge_apply_of_le hle hc (G.merge_apply_of_mem_support_relabelImpl_pub hw)

end

section LeftSummand

variable {X K R : Type} [DecidableEq X] [DecidableEq K] [SampleableType R] {κ₁ κ₂ : Type}
  [DecidableEq κ₁] [DecidableEq κ₂] {spec₁ : OracleSpec κ₁} {spec₂ : OracleSpec κ₂}
  [∀ t, SampleableType ((spec₁ + spec₂).Range t)] (G : CanonicalGraph (spec₁ + spec₂) X K R)

/-- **Settledness, left summand.** For a public oracle `spec₁ + spec₂`, a program over `spec₁`,
run in the deferred game, returns its replay on the `spec₁` part of the merged cache of every
conflict-free state extending the final state. -/
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
    (G.merge_apply_of_le hle hc (G.merge_apply_of_mem_support_relabelImpl_pub hw))

end LeftSummand

end CanonicalGraph

namespace SecretEncoding

variable {ι : Type} {pub : OracleSpec ι} {S X R : Type} (E : SecretEncoding pub S X R)

/-- A public cache that holds no point encoded under `s` is below the real cache rebuilt from it
and any derivation table. -/
theorem le_merge_of_forall_enc_eq_none {s : S} {st : SplitCache pub X R}
    (h : ∀ x, st.1 (E.enc s x) = none) : st.1 ≤ E.merge s st := by
  intro t u ht
  by_cases hx : ∃ x, E.enc s x = t
  · obtain ⟨x, rfl⟩ := hx
    rw [h x] at ht
    cases ht
  · rw [E.merge_apply_of_not_exists s st hx]
    exact ht

end SecretEncoding
