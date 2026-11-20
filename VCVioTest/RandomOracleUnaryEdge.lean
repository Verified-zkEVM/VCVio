/-
Copyright (c) 2026 VCVio Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: VCVio Contributors
-/

module

public import VCVio.OracleComp.QueryTracking.RandomOracle.TouchRead.Unary

/-!
# Unary normalization boundaries

Warm rows remain fixed, cold rows are drawn, and a node may also be its own child.
All conclusions retain the complete public and cell caches.
-/

public section

open OracleComp OracleSpec

namespace VCVioTest.UnaryEdge

variable {ι : Type} {pub : OracleSpec ι} {X K R : Type}
  [DecidableEq ι] [DecidableEq X] [DecidableEq K]
  [SampleableType R] [∀ t, SampleableType (pub.Range t)]
  (G : CanonicalGraph pub X K R)

/-- Warm child and node rows preserve the whole state, including unrelated cells. -/
theorem warm_endpoint
    (k : K) (c : X ⊕ K)
    (hch : G.ch k = [c]) (st : RelabelState pub X K R) (v w : R)
    (hc : st.2 c = some v) (hk : st.2 (.inr k) = some w) :
    (simulateQ G.eagerImpl (do
      let value ← readCell (some c)
      let answer ← query (spec := pub.withLabels X K R)
        (.inl (.inl (.inr (G.pt k [value]))))
      pure (cast (G.range_eq k [value]) answer))).run st = pure (w, st) := by
  rw [G.simulateQ_eagerImpl_unary_edge k c hch]
  simp only [simulateQ_bind, StateT.run_bind, G.eagerImpl_touchCell_run,
    RelabelState.drawCell_run_of_cell_eq_some hc, map_pure, pure_bind,
    G.eagerImpl_readCell_run, RelabelState.drawCell_run_of_cell_eq_some hk]

/-- A missing node is drawn after the same warm child, with its new row retained. -/
theorem cold_node_endpoint
    (k : K) (c : X ⊕ K)
    (hch : G.ch k = [c]) (st : RelabelState pub X K R) (v : R)
    (hc : st.2 c = some v) (hk : st.2 (.inr k) = none) :
    (simulateQ G.eagerImpl (do
      let value ← readCell (some c)
      let answer ← query (spec := pub.withLabels X K R)
        (.inl (.inl (.inr (G.pt k [value]))))
      pure (cast (G.range_eq k [value]) answer))).run st =
      (fun u => (u, (st.1, st.2.cacheQuery (.inr k) u))) <$> ($ᵗ R) := by
  rw [G.simulateQ_eagerImpl_unary_edge k c hch]
  simp only [simulateQ_bind, StateT.run_bind, G.eagerImpl_touchCell_run,
    RelabelState.drawCell_run_of_cell_eq_some hc, map_pure, pure_bind,
    G.eagerImpl_readCell_run, RelabelState.drawCell_run_of_cell_eq_none hk]

/-- No acyclicity premise is needed when the child is the node itself. -/
theorem self_child
    (k : K) (hch : G.ch k = [.inr k])
    (st : RelabelState pub X K R) (v : R) (hk : st.2 (.inr k) = some v) :
    (simulateQ G.eagerImpl (do
      let value ← readCell (some (.inr k))
      let answer ← query (spec := pub.withLabels X K R)
        (.inl (.inl (.inr (G.pt k [value]))))
      pure (cast (G.range_eq k [value]) answer))).run st = pure (v, st) := by
  exact warm_endpoint G k (.inr k) hch st v v hk hk

/-- The ordinary public law transports an arbitrary stateful continuation. -/
theorem whole_endpoint
    {α : Type} (k : K) (c : X ⊕ K)
    (hch : G.ch k = [c]) (st : RelabelState pub X K R)
    (next : R → StateT (RelabelState pub X K R) ProbComp α) :
    (simulateQ G.eagerImpl (do
      let value ← readCell (some c)
      let answer ← query (spec := pub.withLabels X K R)
        (.inl (.inl (.inr (G.pt k [value]))))
      pure (cast (G.range_eq k [value]) answer)) >>= next).run st =
      (simulateQ G.eagerImpl (do
        touchCell (some c)
        readCell (some (.inr k))) >>= next).run st := by
  exact congrArg (fun run => (run >>= next).run st)
    (G.simulateQ_eagerImpl_unary_edge k c hch)

/-- Already cached siblings return their specified values in the original query order. -/
theorem warm_siblings (first second : K) (c : X ⊕ K)
    (hf : G.ch first = [c]) (hs : G.ch second = [c])
    (st : RelabelState pub X K R) (v a b : R)
    (hc : st.2 c = some v) (ha : st.2 (.inr first) = some a)
    (hb : st.2 (.inr second) = some b) :
    (simulateQ G.eagerImpl (do
      let x ← readCell (some c)
      let u ← query (spec := pub.withLabels X K R) (.inl (.inl (.inr (G.pt first [x]))))
      let w ← query (spec := pub.withLabels X K R) (.inl (.inl (.inr (G.pt second [x]))))
      pure (cast (G.range_eq first [x]) u, cast (G.range_eq second [x]) w))).run st =
      pure ((a, b), st) := by
  rw [G.simulateQ_eagerImpl_unary_siblings first second c hf hs]
  simp only [simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure,
    G.eagerImpl_touchCell_run, G.eagerImpl_readCell_run,
    RelabelState.drawCell_run_of_cell_eq_some hc, RelabelState.drawCell_run_of_cell_eq_some ha,
    RelabelState.drawCell_run_of_cell_eq_some hb, map_pure, pure_bind]

/-- When both points name one node, the second read returns its first draw. -/
theorem coincident_siblings (k : K) (c : X ⊕ K) (hch : G.ch k = [c])
    (st : RelabelState pub X K R) :
    (simulateQ G.eagerImpl (do
      let x ← readCell (some c)
      let u ← query (spec := pub.withLabels X K R) (.inl (.inl (.inr (G.pt k [x]))))
      let w ← query (spec := pub.withLabels X K R) (.inl (.inl (.inr (G.pt k [x]))))
      pure (cast (G.range_eq k [x]) u, cast (G.range_eq k [x]) w))).run st =
      (simulateQ G.eagerImpl (do
        touchCell (some c)
        let a ← readCell (some (.inr k))
        pure (a, a))).run st := by
  rw [G.simulateQ_eagerImpl_unary_siblings k k c hch hch]
  simp only [simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure,
    G.eagerImpl_readCell_run]
  congr 1
  funext afterChild
  apply OracleComp.bind_congr_of_forall_mem_support
  intro z hz
  have cached := (RelabelState.le_and_cell_eq_of_mem_support_drawCell hz).2
  simp [RelabelState.drawCell_run_of_cell_eq_some cached]

/-- Keep the first answer and touch the second label, retaining both rows in the final state. -/
theorem low_reply_high_touch (low high : K) (c : X ⊕ K)
    (hlow : G.ch low = [c]) (hhigh : G.ch high = [c]) :
    Prod.fst <$> simulateQ G.eagerImpl (do
      let x ← readCell (some c)
      let a ← query (spec := pub.withLabels X K R) (.inl (.inl (.inr (G.pt low [x]))))
      let b ← query (spec := pub.withLabels X K R) (.inl (.inl (.inr (G.pt high [x]))))
      pure (cast (G.range_eq low [x]) a, cast (G.range_eq high [x]) b)) =
      simulateQ G.eagerImpl (do
        touchCell (some c)
        let a ← readCell (some (.inr low))
        touchCell (some (.inr high))
        pure a) := by
  rw [G.simulateQ_eagerImpl_unary_siblings low high c hlow hhigh]
  simp only [simulateQ_bind, simulateQ_pure, map_bind, map_pure,
    G.simulateQ_eagerImpl_touchCell, bind_map_left]

/-- A chain step consumes its input digest directly and keeps the first half of the reply. -/
def publicStep (low high : K) (x : R) : OracleComp (pub.withLabels X K R) R := do
  let a ← query (spec := pub.withLabels X K R) (.inl (.inl (.inr (G.pt low [x]))))
  let _ ← query (spec := pub.withLabels X K R) (.inl (.inl (.inr (G.pt high [x]))))
  pure (cast (G.range_eq low [x]) a)

/-- Draw the low node and retain the high node in the cache. -/
noncomputable def labelStep (low high : K) : OracleComp (pub.withLabels X K R) R := do
  let a ← readCell (some (.inr low))
  touchCell (some (.inr high))
  pure a

private theorem single_step (low high : K) (c : X ⊕ K)
    (hl : G.ch low = [c]) (hh : G.ch high = [c]) :
    simulateQ G.eagerImpl (do let x ← readCell (some c); publicStep G low high x) =
      simulateQ G.eagerImpl (do touchCell (some c); labelStep low high) := by
  simpa only [publicStep, labelStep, simulateQ_bind, simulateQ_pure, map_bind, map_pure]
    using low_reply_high_touch G low high c hl hh

/-- Two consecutive raw queries share the returned digest. A completed earlier step supplies
the next input cell, so no intermediate value needs to be read in the normalized chain. -/
theorem consecutive_steps (c : X ⊕ K) (first firstHigh last lastHigh : K)
    (hf : G.ch first = [c]) (hf' : G.ch firstHigh = [c])
    (hl : G.ch last = [.inr first]) (hl' : G.ch lastHigh = [.inr first]) :
    simulateQ G.eagerImpl (do
      let x ← readCell (some c)
      let y ← publicStep G first firstHigh x
      publicStep G last lastHigh y) =
    simulateQ G.eagerImpl (do
      touchCell (some c)
      touchCell (some (.inr first))
      touchCell (some (.inr firstHigh))
      labelStep last lastHigh) := by
  simp only [simulateQ_bind]
  rw [← bind_assoc, ← simulateQ_bind, single_step G first firstHigh c hf hf',
    simulateQ_bind, bind_assoc]
  congr 1
  funext _
  apply StateT.ext
  intro st
  rw [StateT.run_bind]
  -- Carry the first low digest across the first high touch.
  calc
    _ = ((simulateQ G.eagerImpl (labelStep first firstHigh)).run st >>= fun w =>
          (simulateQ G.eagerImpl (labelStep last lastHigh)).run w.2) := by
      apply OracleComp.bind_congr_of_forall_mem_support
      intro w hw
      have cached := G.cell_eq_of_mem_support_read_touch first firstHigh st hw
      have eqn := congrArg (fun run => run.run w.2) (single_step G last lastHigh
        (.inr first) hl hl')
      simpa only [simulateQ_bind, StateT.run_bind, G.eagerImpl_touchCell_run,
        G.eagerImpl_readCell_run, RelabelState.drawCell_run_of_cell_eq_some cached,
        pure_bind, map_pure] using eqn
    _ = _ := by
      simp only [labelStep, simulateQ_bind, simulateQ_pure, G.simulateQ_eagerImpl_touchCell,
        StateT.run_bind, StateT.run_pure, bind_assoc, bind_map_left, pure_bind]

end VCVioTest.UnaryEdge
