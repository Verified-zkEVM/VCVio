/-
Copyright (c) 2026 VCVio Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: VCVio Contributors
-/

module

public import VCVio.OracleComp.QueryTracking.RandomOracle.ReadSet
import VCVio.OracleComp.QueryTracking.RandomOracle.CachePartial
import VCVio.OracleComp.QueryTracking.RandomOracle.Commute
import VCVio.OracleComp.Constructions.SampleableType.Measure

/-!
# Predicting undisclosed cells

A public query can draw a node only after all its children have been drawn.
A set of missing cells therefore stays missing if every node in the set has a child in the set
and the caller never directly requests a cell in the set.
A guess made before the end fill matches a missing cell with probability at most one over the
number of answers, even if the pending list repeats that cell.
-/

public section

open OracleComp OracleSpec
open scoped ENNReal

namespace CanonicalGraph

variable {ι X K R α : Type} {pub : OracleSpec ι}

/-- Derivations and explicit reads disclose their cell. Sampling, public queries and touches
make no direct disclosure. -/
@[expose] def AvoidsDirectRead (hidden : Set (X ⊕ K)) : (pub.withLabels X K R).Domain → Prop
  | .inl (.inr x) => Sum.inl x ∉ hidden
  | .inr (.inr k) => Sum.inr k ∉ hidden
  | _ => True

variable [DecidableEq ι] [DecidableEq X] [DecidableEq K] [SampleableType R]
  [∀ t, SampleableType (pub.Range t)] (G : CanonicalGraph pub X K R)

/-- Public oracle calls cannot be the first to open a hidden node with a hidden child. -/
theorem stays_undisclosed {hidden : Set (X ⊕ K)}
    (child : ∀ k, .inr k ∈ hidden → ∃ c ∈ G.ch k, c ∈ hidden)
    {oa : OracleComp (pub.withLabels X K R) α}
    (avoid : AllQueriesSatisfy oa (AvoidsDirectRead (pub := pub) (R := R) hidden))
    {s : RelabelState pub X K R × List (X ⊕ K)} (cold : ∀ c ∈ hidden, s.1.2 c = none)
    {z} (run : z ∈ support ((simulateQ G.deferredImpl oa).run s)) :
    ∀ c ∈ hidden, z.2.1.2 c = none := by
  apply avoid.holds_of_mem_support_run_simulateQ (fun s' ↦ ∀ c ∈ hidden, s'.1.2 c = none) _ cold run
  intro t ht before absent after step c protectedCell
  rcases G.cell_eq_or_draws_of_mem_support_deferredImpl step c with
    same | ⟨k, vs, rfl, ready, rfl⟩ | ⟨x, rfl, rfl⟩ | ⟨k, rfl, rfl⟩
  · exact same.trans (absent c protectedCell)
  · obtain ⟨c', member, protectedChild⟩ := child k protectedCell
    have present := G.isSome_childVals_iff.mp (by rw [ready]; rfl) c' member
    simp [absent c' protectedChild] at present
  · exact (ht protectedCell).elim
  · exact (ht protectedCell).elim

/-- A public query made before the node has these children is recorded in the ordinary table.
If its payload later becomes the canonical children, that same row witnesses a conflict. -/
theorem conflict_of_deferred_public_query {k : K} {vs : List R}
    {s : RelabelState pub X K R × List (X ⊕ K)} {z} {final : RelabelState pub X K R}
    (notReady : G.childVals s.1 k ≠ some vs)
    (query : z ∈ support ((G.deferredImpl (.inl (.inl (.inr (G.pt k vs))))).run s))
    (later : z.2.1 ≤ final) (ready : G.childVals final k = some vs) :
    G.Conflict final := by
  have ordinary : ¬ ∃ j ws, G.childVals s.1 j = some ws ∧ G.pt j ws = G.pt k vs := by
    rintro ⟨j, ws, old, same⟩
    obtain ⟨rfl, rfl⟩ := G.eq_of_childVals_of_pt_eq old ready same
    exact notReady old
  rw [deferredImpl_run_inl, G.relabelImpl_run_pub_of_not_exists ordinary, support_map] at query
  obtain ⟨_, h, rfl⟩ := query
  rw [support_map] at h
  obtain ⟨_, draw, rfl⟩ := h
  exact ⟨k, vs, ready, Option.isSome_iff_exists.mpr
    ⟨_, later.1 (QueryImpl.withCaching_run_caches _ _ _ _ draw)⟩⟩

omit [DecidableEq ι] [DecidableEq X] [DecidableEq K] [SampleableType R]
  [∀ t, SampleableType (pub.Range t)] in
/-- A formerly ordinary merged entry becoming a canonical point witnesses a conflict. -/
theorem conflict_of_merged_before_ready {k : K} {vs : List R}
    {before final : RelabelState pub X K R} (later : before ≤ final)
    (notReady : G.childVals before k ≠ some vs)
    (occupied : (G.merge before (G.pt k vs)).isSome)
    (ready : G.childVals final k = some vs) : G.Conflict final := by
  have ordinary : ¬ ∃ j ws, G.childVals before j = some ws ∧ G.pt j ws = G.pt k vs := by
    rintro ⟨j, ws, old, same⟩
    obtain ⟨rfl, rfl⟩ := G.eq_of_childVals_of_pt_eq old ready same
    exact notReady old
  rw [G.merge_apply_of_not_exists ordinary] at occupied
  exact ⟨k, vs, ready, QueryCache.isSome_mono later.1 occupied⟩

end CanonicalGraph

namespace randomOracle

variable {ι α : Type} {spec : OracleSpec ι} [DecidableEq ι]
  [∀ t, SampleableType (spec.Range t)]

/-- An adaptive lazy computation stores a fixed guess at a fixed cold input with probability
at most the mass of the guess. It may query the input repeatedly or skip it altogether. -/
theorem prEvent_cold_cell_eq_le (oa : OracleComp spec α) (t : ι) (v : spec.Range t)
    (cache : spec.QueryCache) (cold : cache t = none) :
    Pr{let z ← (simulateQ spec.randomOracle oa).run cache}[z.2 t = some v] ≤
      (Nat.card (spec.Range t) : ℝ≥0∞)⁻¹ := by
  induction oa using OracleComp.inductionOn generalizing cache with
  | pure a => simp [cold, prEvent_norm]
  | query_bind s k ih =>
    rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
    by_cases same : s = t
    · subst s
      rw [QueryImpl.withCaching_run_none _ cold]
      simp only [uniformSampleImpl_apply, bind_map_left]
      refine (prEvent_bind_le_prEvent_of_support _ _ (· = v) _ ?_).trans
        (SampleableType.prEvent_uniformSample_eq_singleton_natCard v).le
      intro u _ ne
      apply prEvent_eq_zero_of_forall_mem_support
      intro z hz matchGuess
      have ext := QueryImpl.le_snd_of_mem_support_run_simulateQ_withCaching
        uniformSampleImpl (k u) hz
      have kept := ext (QueryCache.cacheQuery_self cache t u)
      exact ne (Option.some.inj (kept.symm.trans matchGuess))
    · apply prEvent_bind_le_of_forall_le_of_support
      intro z hz
      exact ih z.1 z.2 ((run_apply_of_ne same cache hz).trans cold)

end randomOracle

namespace RelabelState

variable {ι X K R J : Type} {pub : OracleSpec ι} [DecidableEq X] [DecidableEq K]
  [SampleableType R] [Fintype J]

/-- The guesses and their cells may be chosen from the state before the fill.
Only guesses at cells still missing in this state contribute to the bound. -/
theorem prEvent_endFill_guesses_le (st : RelabelState pub X K R) (pending : List (X ⊕ K))
    (cell : J → X ⊕ K) (value : J → R) :
    Pr{let final ← endFill (st, pending)}[
      ∃ j, st.2 (cell j) = none ∧ final.2 (cell j) = some (value j)] ≤
      Fintype.card J * (Nat.card R : ℝ≥0∞)⁻¹ := by
  refine prEvent_exists_le_card_mul _ _ fun j ↦ ?_
  by_cases cold : st.2 (cell j) = none
  · simpa only [endFill_eq, prEvent_norm, cold, true_and] using
      randomOracle.prEvent_cold_cell_eq_le (((X ⊕ K) →ₒ R).queryAll pending)
        (cell j) (value j) st.2 cold
  · simp [cold]

end RelabelState
