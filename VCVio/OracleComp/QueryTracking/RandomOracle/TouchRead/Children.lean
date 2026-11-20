/-
Copyright (c) 2026 VCVio Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: VCVio Contributors
-/
module

public import VCVio.OracleComp.QueryTracking.RandomOracle.TouchRead

/-!
# Hash points with ordered children in the eager game

Every value returned by an ordered list of reads remains in the cache at the end of the list.
A pair of public hash points can therefore share all of their inputs, including repeated children.
-/

public section

open OracleComp OracleSpec

namespace CanonicalGraph

variable {ι X K R : Type} {pub : OracleSpec ι} (G : CanonicalGraph pub X K R)
  [DecidableEq ι] [DecidableEq X] [DecidableEq K] [SampleableType R]
  [∀ t, SampleableType (pub.Range t)]

/-- An ordered list of reads extends the initial state and retains every response at its child.
The list may contain the same cell more than once. -/
theorem readCells_recorded (cs : List (X ⊕ K)) (st : RelabelState pub X K R)
    {z : List R × RelabelState pub X K R}
    (hz : z ∈ support ((simulateQ G.eagerImpl (cs.mapM fun c => readCell (some c))).run st)) :
    st ≤ z.2 ∧ List.Forall₂ (fun c v => z.2.2 c = some v) cs z.1 := by
  induction cs generalizing st z with
  | nil =>
    simp only [List.mapM_nil, simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at hz
    subst z
    exact ⟨le_rfl, .nil⟩
  | cons c cs ih =>
    simp only [List.mapM_cons, simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure,
      G.eagerImpl_readCell_run, mem_support_bind_iff, mem_support_pure_iff] at hz
    obtain ⟨head, first, tail, rest, rfl⟩ := hz
    obtain ⟨leHead, atHead⟩ := RelabelState.le_and_cell_eq_of_mem_support_drawCell first
    obtain ⟨leTail, atTail⟩ := ih head.2 rest
    exact ⟨leHead.trans leTail, .cons (leTail.2 atHead) atTail⟩

/-- Touching each child is the eager computation that forgets the values of all the reads. -/
theorem simulateQ_eagerImpl_touchCells (cs : List (X ⊕ K)) :
    simulateQ G.eagerImpl (forM cs fun c => touchCell (some c)) =
      (fun _ => ()) <$> simulateQ G.eagerImpl (cs.mapM fun c => readCell (some c)) := by
  induction cs with
  | nil => simp
  | cons c cs ih =>
    simp only [List.forM_cons, List.mapM_cons, simulateQ_bind, simulateQ_pure,
      G.simulateQ_eagerImpl_touchCell, ih, bind_map_left, map_bind, map_pure]
    simp only [← bind_pure_comp]

/-- A continuation may replace the inputs it read by their cached values at the end of the list. -/
private theorem bind_readCells {α : Type} (cs : List (X ⊕ K))
    (f : List R → OracleComp (pub.withLabels X K R) α) (g : OracleComp (pub.withLabels X K R) α)
    (agrees : ∀ (st : RelabelState pub X K R) vs, List.Forall₂ (fun c v => st.2 c = some v) cs vs →
      (simulateQ G.eagerImpl (f vs)).run st = (simulateQ G.eagerImpl g).run st) :
    simulateQ G.eagerImpl ((cs.mapM fun c => readCell (some c)) >>= f) =
      simulateQ G.eagerImpl ((forM cs fun c => touchCell (some c)) >>= fun _ => g) := by
  ext st : 1
  simp only [simulateQ_bind, G.simulateQ_eagerImpl_touchCells, bind_map_left, StateT.run_bind]
  apply OracleComp.bind_congr_of_forall_mem_support
  intro z hz
  exact agrees z.2 z.1 (G.readCells_recorded cs st hz).2

/-- Once a parent's ordered inputs are recorded, its public query reads that parent's label. -/
theorem eagerImpl_point_run_of_childVals (k : K) (vs : List R) (st : RelabelState pub X K R)
    (ready : G.childVals st k = some vs) :
    (simulateQ G.eagerImpl (do
      let a ← query (spec := pub.withLabels X K R) (.inl (.inl (.inr (G.pt k vs))))
      pure (cast (G.range_eq k vs) a))).run st =
      (simulateQ G.eagerImpl (readCell (some (.inr k)))).run st := by
  simp [G.eagerImpl_apply_inl, G.relabelImpl_run_pt ready,
    G.eagerImpl_readCell_run]

/-- Two ready public points use the same ordered values, including after the first output is drawn.
The ordered pair and both complete caches agree for any initial state. -/
theorem eagerImpl_siblings_run_of_childVals (lo hi : K) (vs : List R) (st : RelabelState pub X K R)
    (low : G.childVals st lo = some vs) (high : G.childVals st hi = some vs) :
    (simulateQ G.eagerImpl (do
      let a ← query (spec := pub.withLabels X K R) (.inl (.inl (.inr (G.pt lo vs))))
      let b ← query (spec := pub.withLabels X K R) (.inl (.inl (.inr (G.pt hi vs))))
      pure (cast (G.range_eq lo vs) a, cast (G.range_eq hi vs) b))).run st =
      (simulateQ G.eagerImpl (do
        let a ← readCell (some (.inr lo))
        let b ← readCell (some (.inr hi))
        pure (a, b))).run st := by
  simp only [simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure,
    G.eagerImpl_readCell_run, simulateQ_HasQuery_query, G.eagerImpl_apply_inl,
    G.relabelImpl_run_pt low, bind_map_left]
  apply OracleComp.bind_congr_of_forall_mem_support
  intro z hz
  have ready := G.childVals_mono (RelabelState.le_and_cell_eq_of_mem_support_drawCell hz).1 high
  simp [G.relabelImpl_run_pt ready]

/-- Read the ordered children of a parent, then query the public point they determine. -/
theorem simulateQ_eagerImpl_edge (k : K) (cs : List (X ⊕ K)) (shape : G.ch k = cs) :
    simulateQ G.eagerImpl (do
      let vs ← cs.mapM fun c => readCell (some c)
      let a ← query (spec := pub.withLabels X K R) (.inl (.inl (.inr (G.pt k vs))))
      pure (cast (G.range_eq k vs) a)) =
    simulateQ G.eagerImpl (do
      forM cs fun c => touchCell (some c)
      readCell (some (.inr k))) := by
  apply G.bind_readCells
  intro st vs recorded
  exact G.eagerImpl_point_run_of_childVals k vs st
    (G.childVals_eq_some_iff.mpr (shape ▸ recorded))

/-- Read both hash outputs at the ordered list of children shared by the two output rows. -/
theorem simulateQ_eagerImpl_siblings (lo hi : K) (cs : List (X ⊕ K))
    (low : G.ch lo = cs) (high : G.ch hi = cs) :
    simulateQ G.eagerImpl (do
      let vs ← cs.mapM fun c => readCell (some c)
      let a ← query (spec := pub.withLabels X K R) (.inl (.inl (.inr (G.pt lo vs))))
      let b ← query (spec := pub.withLabels X K R) (.inl (.inl (.inr (G.pt hi vs))))
      pure (cast (G.range_eq lo vs) a, cast (G.range_eq hi vs) b)) =
    simulateQ G.eagerImpl (do
      forM cs fun c => touchCell (some c)
      let a ← readCell (some (.inr lo))
      let b ← readCell (some (.inr hi))
      pure (a, b)) := by
  apply G.bind_readCells
  intro st vs recorded
  exact G.eagerImpl_siblings_run_of_childVals lo hi vs st
    (G.childVals_eq_some_iff.mpr (low ▸ recorded))
    (G.childVals_eq_some_iff.mpr (high ▸ recorded))

end CanonicalGraph
