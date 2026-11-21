/-
Copyright (c) 2026 VCVio Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: VCVio Contributors
-/

module

public import VCVio.OracleComp.QueryTracking.RandomOracle.Relabel

/-!
# Recovering children from a matching node label

A verifier supplies a list of child values and obtains the label recorded at a node.
If the list differs from the node's stored children, the match comes from the ordinary public cache.
This gives a target collision even when the node's children have yet to be drawn.
-/

public section

namespace CanonicalGraph

open OracleSpec

variable {ι X K R : Type} {pub : OracleSpec ι} (G : CanonicalGraph pub X K R)

/-- A well-shaped point with different or undrawn children reads from the public cache. -/
theorem merge_pt_of_childVals_ne {st : RelabelState pub X K R} {k : K} {vs : List R}
    (width : vs.length = (G.ch k).length) (different : G.childVals st k ≠ some vs) :
    G.merge st (G.pt k vs) = st.1 (G.pt k vs) := by
  apply G.merge_apply_of_not_exists
  rintro ⟨j, ws, ready, same⟩
  obtain ⟨rfl, rfl⟩ := G.pt_inj (G.length_eq_of_childVals_eq_some ready) width same
  exact different ready

/-- Outside the node-key collision event, a match with the node's own label identifies all
of its ordered children. -/
theorem NodeKeys.childVals_of_match {G : CanonicalGraph pub X K R} (nk : G.NodeKeys)
    {st : RelabelState pub X K R} {k : K} {vs : List R} {v : R}
    (safe : ¬ nk.TCHazard st) (width : vs.length = (G.ch k).length)
    (label : st.2 (.inr k) = some v)
    (matched : G.merge st (G.pt k vs) = some (cast (G.range_eq k vs).symm v)) :
    G.childVals st k = some vs := by
  by_contra different
  rw [G.merge_pt_of_childVals_ne width different] at matched
  exact safe ⟨G.pt k vs, k, v, nk.node_pt width, label, matched⟩

end CanonicalGraph
