/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module
public import VCVio.OracleComp.QueryTracking.RandomOracle.Settled

/-!
# Settled public programs on a one-node graph

A random oracle on `Bool` has one derivation `()` and one node `()`, whose only child is the
derivation and whose point is the derivation's value. The public program `guess` queries the
point `true`.

* Settledness applies from a state whose node label is drawn while its child is not, a state
  that does not satisfy `CanonicalGraph.LabelsComplete`.
* The conflict hypothesis cannot be dropped: a guess `u` cached as a public answer is in the
  merged cache, but drawing the derivation at `true` afterwards completes the node at the guessed
  point, a conflict, and the merged cache there then reads the undrawn label.
* Settledness on the left summand of a public oracle `spec₁ + spec₂` resolves its lifts at a
  concrete sum.
-/

public section

open OracleComp OracleSpec

namespace SettledToy

/-- The public oracle: a random oracle on `Bool`. -/
abbrev pub := Bool →ₒ Bool

/-- One node, whose only child is the derivation and whose point is the derivation's value. -/
def G : CanonicalGraph pub Unit Unit Bool where
  ch _ := [.inl ()]
  pt _ vs := vs.headD false
  range_eq _ _ := rfl
  pt_inj {_ _ vs vs'} h h' hpt := by
    match vs, vs', h, h' with
    | [v], [v'], _, _ => exact ⟨rfl, by simpa using hpt⟩

/-- Query the public point `true`. -/
def guess : OracleComp pub Bool := pub.query true

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
example (ℓ : Bool) {z} (hz : z ∈ support ((simulateQ G.deferredImpl
      (simulateQ (HasQuery.toQueryImpl (spec := pub)
        (m := OracleComp (pub.withLabels Unit Unit Bool))) guess)).run (labelOnly ℓ, [])))
    {st} (hle : z.2.1 ≤ st) (hc : ¬G.Conflict st) :
    simulateQ (G.merge st).toPartialImpl guess = some z.1 :=
  G.simulateQ_toPartialImpl_merge_of_mem_support_deferredImpl guess hz hle hc

/-! ## The conflict hypothesis is needed -/

/-- The guess `u` cached as a public answer, with the derivation undrawn. -/
def cached (u : Bool) : RelabelState pub Unit Unit Bool :=
  ((∅ : pub.QueryCache).cacheQuery true u, ∅)

/-- The same, with the derivation drawn at `true`. -/
def filled (u : Bool) : RelabelState pub Unit Unit Bool :=
  ((∅ : pub.QueryCache).cacheQuery true u,
    (∅ : ((Unit ⊕ Unit) →ₒ Bool).QueryCache).cacheQuery (.inl ()) true)

theorem cached_le_filled (u : Bool) : cached u ≤ filled u :=
  ⟨le_rfl, QueryCache.le_cacheQuery _ (QueryCache.empty_apply _)⟩

theorem merge_cached (u : Bool) : G.merge (cached u) true = some u := by
  have h : ¬∃ k vs, G.childVals (cached u) k = some vs ∧ G.pt k vs = true := by
    rintro ⟨k, vs, hk, -⟩
    rw [childVals_eq] at hk
    simp [cached, QueryCache.empty_apply] at hk
  rw [G.merge_apply_of_not_exists h]
  simp [cached]

theorem conflict_filled (u : Bool) : G.Conflict (filled u) :=
  ⟨(), [true], by simp [childVals_eq, filled], by simp [filled, G]⟩

theorem merge_filled (u : Bool) : G.merge (filled u) true = none := by
  have h : G.childVals (filled u) () = some [true] := by simp [childVals_eq, filled]
  rw [show true = G.pt () [true] from rfl, G.merge_apply_pt h]
  simp [filled, QueryCache.cacheQuery_of_ne, QueryCache.empty_apply]

/-- The guess is settled on the merged cache of `cached u`, but not on that of its conflicting
extension `filled u`. -/
theorem settled_cached_not_filled (u : Bool) :
    simulateQ (G.merge (cached u)).toPartialImpl guess = some u ∧
      simulateQ (G.merge (filled u)).toPartialImpl guess = none := by
  simp [guess, merge_cached, merge_filled]

/-- So the merged cache is not monotone across a conflict. -/
theorem not_merge_le_merge_filled (u : Bool) : ¬G.merge (cached u) ≤ G.merge (filled u) :=
  fun h ↦ by simpa [merge_filled] using h (merge_cached u)

/-! ## The left summand -/

/-- A public oracle with two summands. -/
abbrev pub₂ := (Bool →ₒ Bool) + (Unit →ₒ Bool)

/-- One node whose point is in the left summand. -/
def G₂ : CanonicalGraph pub₂ Unit Unit Bool where
  ch _ := [.inl ()]
  pt _ vs := .inl (vs.headD false)
  range_eq _ _ := rfl
  pt_inj {_ _ vs vs'} h h' hpt := by
    match vs, vs', h, h' with
    | [v], [v'], _, _ => exact ⟨rfl, by simpa using hpt⟩

example {z} (s : RelabelState pub₂ Unit Unit Bool × List (Unit ⊕ Unit))
    (hz : z ∈ support ((simulateQ G₂.deferredImpl
      (simulateQ (HasQuery.toQueryImpl (spec := Bool →ₒ Bool)
        (m := OracleComp (pub₂.withLabels Unit Unit Bool))) guess)).run s))
    {st} (hle : z.2.1 ≤ st) (hc : ¬G₂.Conflict st) :
    simulateQ (G₂.merge st).fst.toPartialImpl guess = some z.1 :=
  G₂.simulateQ_toPartialImpl_merge_fst_of_mem_support_deferredImpl guess hz hle hc

end SettledToy
