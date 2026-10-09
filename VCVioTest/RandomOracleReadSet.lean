/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module
public import VCVio.OracleComp.QueryTracking.RandomOracle.ReadSet

/-!
# Read sets on a one-node graph

The public oracle is a random oracle on `Bool`. The graph has one derivation `()` and one node
`()`, whose only child is the derivation and whose point is the derivation's value.

* A touch of the node followed by a read of the derivation reads within the derivation cell, so
  its run in the deferred game leaves the node's cell as it found it.
* The public clause of `CanonicalGraph.ReadsWithin` is needed. Once the derivation is drawn, a
  public query at the node's point makes no derivation and no read, yet draws the node's label, a
  cell outside the derivation cell; that query does not read within the derivation cell.
-/

public section

open OracleComp OracleSpec

namespace ReadSetToy

/-- The public oracle. -/
abbrev pub := Bool →ₒ Bool

/-- One node, whose only child is the derivation and whose point is the derivation's value. -/
def G : CanonicalGraph pub Unit Unit Bool where
  ch _ := [.inl ()]
  pt _ vs := vs.headD false
  range_eq _ _ := rfl
  pt_inj {_ _ vs vs'} h h' hpt := by
    match vs, vs', h, h' with
    | [v], [v'], _, _ => exact ⟨rfl, by simpa using hpt⟩

/-! ## The frame on a touch-then-read -/

/-- Touch the node, then read the derivation. -/
def cells : ℕ → Option (Unit ⊕ Unit)
  | 0 => some (.inr ())
  | _ => some (.inl ())

/-- The touch-then-read reads within the derivation cell. -/
theorem allQueriesSatisfy_touchRead_cells :
    AllQueriesSatisfy (touchRead (pub := pub) (R := Bool) cells 1) (G.ReadsWithin {.inl ()}) :=
  G.allQueriesSatisfy_readsWithin_touchRead fun c hc ↦ by
    cases Option.some_injective _ hc
    rfl

/-- Its run in the deferred game leaves the node's cell as it found it. -/
example {s : RelabelState pub Unit Unit Bool × List (Unit ⊕ Unit)} {z}
    (hz : z ∈ support ((simulateQ G.deferredImpl
      (touchRead (pub := pub) (R := Bool) cells 1)).run s)) :
    z.2.1.2 (.inr ()) = s.1.2 (.inr ()) :=
  G.cell_eq_of_mem_support_simulateQ_deferredImpl allQueriesSatisfy_touchRead_cells hz (by simp)

/-! ## The public clause is needed -/

/-- The state with only the derivation drawn, at `v`. -/
def derived (v : Bool) : RelabelState pub Unit Unit Bool :=
  (∅, (∅ : ((Unit ⊕ Unit) →ₒ Bool).QueryCache).cacheQuery (.inl ()) v)

/-- The public query at the node's point does not read within the derivation cell. -/
theorem not_readsWithin_pt (v : Bool) :
    ¬G.ReadsWithin {.inl ()} (.inl (.inl (.inr (G.pt () [v])))) :=
  fun h ↦ by simpa using h () [v] rfl

/-- With the derivation drawn at `v`, every run of the public query at the node's point draws the
node's label. -/
theorem cell_eq_some_of_mem_support_pt (v : Bool) {z}
    (hz : z ∈ support ((G.deferredImpl (.inl (.inl (.inr (G.pt () [v]))))).run (derived v, []))) :
    z.2.1.2 (.inr ()) = some z.1 := by
  have hk : G.childVals (derived v) () = some [v] :=
    G.childVals_eq_some_iff.2 (.cons (by simp [derived]) .nil)
  rw [CanonicalGraph.deferredImpl_run_inl, G.relabelImpl_run_pt hk, Functor.map_map,
    support_map] at hz
  obtain ⟨w, hw, rfl⟩ := hz
  exact (RelabelState.le_and_cell_eq_of_mem_support_drawCell hw).2

/-- So the public query changes the node's cell, which lies outside the derivation cell. -/
theorem exists_mem_support_pt_cell_ne (v : Bool) :
    ∃ z ∈ support ((G.deferredImpl (.inl (.inl (.inr (G.pt () [v]))))).run (derived v, [])),
      z.2.1.2 (.inr ()) ≠ (derived v).2 (.inr ()) := by
  obtain ⟨z, hz⟩ := support_nonempty
    ((G.deferredImpl (.inl (.inl (.inr (G.pt () [v]))))).run (derived v, []))
  refine ⟨z, hz, ?_⟩
  rw [cell_eq_some_of_mem_support_pt v hz]
  simp [derived, QueryCache.cacheQuery_of_ne, QueryCache.empty_apply]

end ReadSetToy
