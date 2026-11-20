/-
Copyright (c) 2026 VCVio Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: VCVio Contributors
-/

module

public import VCVio.OracleComp.QueryTracking.RandomOracle.TouchRead.Children

/-!
# Unary edges in the eager relabelled game

Reading the child fixes the actual input of a unary node.
The public query then draws that node and preserves the entire relabelled state.
-/

public section

open OracleComp OracleSpec

namespace CanonicalGraph

variable {ι : Type} {pub : OracleSpec ι} {X K R : Type} (G : CanonicalGraph pub X K R)

private theorem childVals_singleton {k : K} {c : X ⊕ K} {v : R}
    {st : RelabelState pub X K R} (hch : G.ch k = [c]) (hv : st.2 c = some v) :
    G.childVals st k = some [v] := by
  apply G.childVals_eq_some_iff.mpr
  rw [hch]
  exact List.Forall₂.cons hv List.Forall₂.nil

variable [DecidableEq ι] [DecidableEq X] [DecidableEq K]
  [SampleableType R] [∀ t, SampleableType (pub.Range t)]

/-- Normalize an actual unary edge with the same reply and complete cache state. -/
theorem simulateQ_eagerImpl_unary_edge
    (k : K) (c : X ⊕ K)
    (hch : G.ch k = [c]) :
    simulateQ G.eagerImpl (do
      let value ← readCell (some c)
      let answer ← query (spec := pub.withLabels X K R)
        (.inl (.inl (.inr (G.pt k [value]))))
      pure (cast (G.range_eq k [value]) answer)) =
      simulateQ G.eagerImpl (do
        touchCell (some c)
        readCell (some (.inr k))) := by
  simpa [bind_assoc] using G.simulateQ_eagerImpl_edge k [c] hch

/-- Reading two unary points at the same child value gives the ordered pair of their labels.
Both reads preserve the same final public and cell caches as the original queries. -/
theorem simulateQ_eagerImpl_unary_siblings (first second : K) (c : X ⊕ K)
    (hfirst : G.ch first = [c]) (hsecond : G.ch second = [c]) :
    simulateQ G.eagerImpl (do
      let v ← readCell (some c)
      let a ← query (spec := pub.withLabels X K R) (.inl (.inl (.inr (G.pt first [v]))))
      let b ← query (spec := pub.withLabels X K R) (.inl (.inl (.inr (G.pt second [v]))))
      pure (cast (G.range_eq first [v]) a, cast (G.range_eq second [v]) b)) =
      simulateQ G.eagerImpl (do
        touchCell (some c)
        let a ← readCell (some (.inr first))
        let b ← readCell (some (.inr second))
        pure (a, b)) := by
  simpa [bind_assoc] using G.simulateQ_eagerImpl_siblings first second [c] hfirst hsecond

/-- When the preceding step supplies a cached child value, both node queries consume that value
directly. The original execution makes no additional child read. -/
theorem eagerImpl_unary_siblings_run_of_cached (low high : K) (c : X ⊕ K)
    (hlow : G.ch low = [c]) (hhigh : G.ch high = [c]) (st : RelabelState pub X K R)
    (x : R) (cached : st.2 c = some x) :
    (simulateQ G.eagerImpl (do
      let a ← query (spec := pub.withLabels X K R) (.inl (.inl (.inr (G.pt low [x]))))
      let b ← query (spec := pub.withLabels X K R) (.inl (.inl (.inr (G.pt high [x]))))
      pure (cast (G.range_eq low [x]) a, cast (G.range_eq high [x]) b))).run st =
      (simulateQ G.eagerImpl (do
        let a ← readCell (some (.inr low))
        let b ← readCell (some (.inr high))
        pure (a, b))).run st :=
  G.eagerImpl_siblings_run_of_childVals low high [x] st
    (G.childVals_singleton hlow cached) (G.childVals_singleton hhigh cached)

/-- Every returned low value remains cached after touching its sibling. -/
theorem cell_eq_of_mem_support_read_touch (low high : K) (st : RelabelState pub X K R)
    {z : R × RelabelState pub X K R}
    (hz : z ∈ support ((simulateQ G.eagerImpl (do
      let a ← readCell (some (.inr low))
      touchCell (some (.inr high))
      pure a)).run st)) : z.2.2 (.inr low) = some z.1 := by
  simp only [simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure,
    G.eagerImpl_readCell_run, G.eagerImpl_touchCell_run, bind_map_left,
    mem_support_bind_iff, mem_support_pure_iff] at hz
  obtain ⟨first, hfirst, second, hsecond, rfl⟩ := hz
  exact (RelabelState.le_and_cell_eq_of_mem_support_drawCell hsecond).1.2
    (RelabelState.le_and_cell_eq_of_mem_support_drawCell hfirst).2

end CanonicalGraph
