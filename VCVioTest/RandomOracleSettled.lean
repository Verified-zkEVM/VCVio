/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module
public import VCVio.OracleComp.QueryTracking.RandomOracle.Settled

/-!
# Settled public programs on a one-node graph

The public oracle is a random oracle on `Bool` beside one further point `.inr ()`. It has one
derivation `()` and one node `()`, whose only child is the derivation and whose point is the
derivation's value in the left summand. The program `guess` over the left summand queries the
point `true`.

* Settledness applies from a state whose node label is drawn while its child is not, a state
  that does not satisfy `CanonicalGraph.LabelsComplete`.
* The conflict hypothesis cannot be dropped: a run of `guess` from the empty state caches its
  answer `u` as a public answer, but drawing the derivation at `true` afterwards completes the
  node at the guessed point, a conflict, and the merged cache there then reads the undrawn label.
* Off a public entry at the point `.inr ()` that a secret encoding uses, the replay carries over
  to the real cache that `SecretEncoding.merge` rebuilds from the split state.
-/

public section

open OracleComp OracleSpec

namespace SettledToy

/-- The summand the program queries: a random oracle on `Bool`. -/
abbrev pub₁ := Bool →ₒ Bool

/-- The public oracle. -/
abbrev pub := pub₁ + (Unit →ₒ Bool)

/-- One node, whose only child is the derivation and whose point is the derivation's value. -/
def G : CanonicalGraph pub Unit Unit Bool where
  ch _ := [.inl ()]
  pt _ vs := .inl (vs.headD false)
  range_eq _ _ := rfl
  pt_inj {_ _ vs vs'} h h' hpt := by
    match vs, vs', h, h' with
    | [v], [v'], _, _ => exact ⟨rfl, by simpa using hpt⟩

/-- Query the point `true`. -/
def guess : OracleComp pub₁ Bool := pub₁.query true

/-- The run of `guess` in the deferred game. -/
noncomputable abbrev guessRun (s : RelabelState pub Unit Unit Bool × List (Unit ⊕ Unit)) :=
  (simulateQ G.deferredImpl (simulateQ (HasQuery.toQueryImpl (spec := pub₁)
    (m := OracleComp (pub.withLabels Unit Unit Bool))) guess)).run s

/-- The children of the node are drawn exactly when the derivation is. -/
theorem childVals_eq (st : RelabelState pub Unit Unit Bool) :
    G.childVals st () = (st.2 (.inl ())).map fun v ↦ [v] := by
  cases h : st.2 (.inl ()) with
  | some v => exact G.childVals_eq_some_iff.2 (.cons h .nil)
  | none =>
    cases hc : G.childVals st () with
    | none => rfl
    | some vs =>
      have hf : List.Forall₂ (fun c v ↦ st.2 c = some v) [.inl ()] vs :=
        G.childVals_eq_some_iff.1 hc
      rcases hf with _ | ⟨hv, -⟩
      rw [h] at hv
      exact absurd hv (Option.some_ne_none _).symm

/-! ## Without complete labels -/

/-- A state whose node label is drawn while the derivation is not. -/
def labelOnly (ℓ : Bool) : RelabelState pub Unit Unit Bool :=
  (∅, (∅ : ((Unit ⊕ Unit) →ₒ Bool).QueryCache).cacheQuery (.inr ()) ℓ)

theorem not_labelsComplete_labelOnly (ℓ : Bool) : ¬G.LabelsComplete (labelOnly ℓ) := by
  intro h
  have := h () (by simp [labelOnly])
  simp [childVals_eq, labelOnly, QueryCache.cacheQuery_of_ne, QueryCache.empty_apply] at this

/-- From that state, the guess is still settled on the merged cache of every conflict-free
extension of its final state. -/
example (ℓ : Bool) {z} (hz : z ∈ support (guessRun (labelOnly ℓ, [])))
    {st} (hle : z.2.1 ≤ st) (hc : ¬G.Conflict st) :
    simulateQ (G.merge st).fst.toPartialImpl guess = some z.1 :=
  G.simulateQ_toPartialImpl_merge_fst_of_mem_support_deferredImpl guess hz hle hc

/-! ## The conflict hypothesis is needed -/

/-- The guess `u` cached as a public answer, with the derivation undrawn. -/
def cached (u : Bool) : RelabelState pub Unit Unit Bool :=
  ((∅ : pub.QueryCache).cacheQuery (.inl true) u, ∅)

/-- The same, with the derivation drawn at `true`. -/
def filled (u : Bool) : RelabelState pub Unit Unit Bool :=
  ((∅ : pub.QueryCache).cacheQuery (.inl true) u,
    (∅ : ((Unit ⊕ Unit) →ₒ Bool).QueryCache).cacheQuery (.inl ()) true)

theorem cached_le_filled (u : Bool) : cached u ≤ filled u :=
  ⟨le_rfl, QueryCache.le_cacheQuery _ (QueryCache.empty_apply _)⟩

/-- No node has drawn children in the empty state. -/
theorem not_exists_childVals_empty (t : Bool ⊕ Unit) :
    ¬∃ k vs, G.childVals ((∅, ∅) : RelabelState pub Unit Unit Bool) k = some vs ∧
      G.pt k vs = t := by
  rintro ⟨k, vs, hk, -⟩
  rw [childVals_eq] at hk
  simp [QueryCache.empty_apply] at hk

/-- From the empty state, a run of `guess` can end in `cached u` with output `u`. -/
theorem mem_support_guessRun (u : Bool) :
    (u, (cached u, [])) ∈ support (guessRun ((∅, ∅), [])) := by
  rw [guessRun, show (simulateQ (HasQuery.toQueryImpl (spec := pub₁)
      (m := OracleComp (pub.withLabels Unit Unit Bool))) guess) =
      liftM ((pub.withLabels Unit Unit Bool).query (.inl (.inl (.inr (.inl true))))) from by
        simp [guess]; rfl,
    simulateQ_spec_query, CanonicalGraph.deferredImpl_run_inl,
    G.relabelImpl_run_pub_of_not_exists (not_exists_childVals_empty _), support_map, support_map,
    Set.image_image]
  refine ⟨(u, (∅ : pub.QueryCache).cacheQuery (.inl true) u), ?_, rfl⟩
  rw [randomOracle, QueryImpl.withCaching_run_none _ (QueryCache.empty_apply _), support_map]
  exact ⟨u, by simp, rfl⟩

theorem merge_cached (u : Bool) : G.merge (cached u) (.inl true) = some u := by
  have h : ¬∃ k vs, G.childVals (cached u) k = some vs ∧ G.pt k vs = .inl true := by
    rintro ⟨k, vs, hk, -⟩
    rw [childVals_eq] at hk
    simp [cached, QueryCache.empty_apply] at hk
  rw [G.merge_apply_of_not_exists h]
  simp [cached]

theorem conflict_filled (u : Bool) : G.Conflict (filled u) :=
  ⟨(), [true], by simp [childVals_eq, filled], by simp [filled, G]⟩

theorem merge_filled (u : Bool) : G.merge (filled u) (.inl true) = none := by
  have h : G.childVals (filled u) () = some [true] := by simp [childVals_eq, filled]
  rw [show (.inl true : Bool ⊕ Unit) = G.pt () [true] from rfl, G.merge_apply_pt h]
  simp [filled, QueryCache.cacheQuery_of_ne, QueryCache.empty_apply]

/-- The guess is settled on the merged cache of `cached u`, but not on that of its conflicting
extension `filled u`. -/
theorem settled_cached_not_filled (u : Bool) :
    simulateQ (G.merge (cached u)).fst.toPartialImpl guess = some u ∧
      simulateQ (G.merge (filled u)).fst.toPartialImpl guess = none := by
  simp [guess, merge_cached, merge_filled]

/-- So the merged cache is not monotone across a conflict. -/
theorem not_merge_le_merge_filled (u : Bool) : ¬G.merge (cached u) ≤ G.merge (filled u) :=
  fun h ↦ by simpa [merge_filled] using h (merge_cached u)

/-- Without the conflict hypothesis, settledness fails on a reachable run: the run of `guess`
from the empty state that ends in `cached u` is not replayed on the merged cache of its
extension `filled u`. -/
theorem settled_false_without_conflict (u : Bool) :
    ∃ z ∈ support (guessRun ((∅, ∅), [])),
      z.2.1 ≤ filled u ∧ simulateQ (G.merge (filled u)).fst.toPartialImpl guess ≠ some z.1 :=
  ⟨_, mem_support_guessRun u, cached_le_filled u, by simp [(settled_cached_not_filled u).2]⟩

/-! ## The seed merge -/

/-- A secret encoding with one derivation, encoded at the point `.inr ()`, which is no node
point. -/
def E : SecretEncoding pub Unit Unit Bool where
  enc _ _ := .inr ()
  range_eq _ _ := rfl
  injective _ _ _ _ := rfl

/-- Off a public entry at the encoded point, the guess is settled on the left summand of the real
cache rebuilt from the split state of every conflict-free extension of its final state. -/
example {s z} (hz : z ∈ support (guessRun s)) {st} (hle : z.2.1 ≤ st) (hc : ¬G.Conflict st)
    (hseed : ¬∃ x, (st.1 (E.enc () x)).isSome) :
    simulateQ (E.merge () (G.toSplitCache st)).fst.toPartialImpl guess = some z.1 := by
  refine QueryCache.simulateQ_toPartialImpl_mono (QueryCache.fst_mono
    (E.le_merge_of_not_exists_isSome _ fun ⟨x, hx⟩ ↦ hseed ⟨x, ?_⟩)) _
    (G.simulateQ_toPartialImpl_merge_fst_of_mem_support_deferredImpl guess hz hle hc)
  rwa [G.merge_apply_of_not_exists fun ⟨_, _, _, h⟩ ↦ nomatch h] at hx

end SettledToy
