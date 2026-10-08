/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module

public import VCVio.OracleComp.QueryTracking.RandomOracle.Relabel

/-!
# Touch-then-read programs over the label operations

Over `pub.withLabels X K R` a *cell* is a derivation `x : X` or a node `k : K`. `touchCell c`
touches the cell `c` and `readCell c` reads it: a derivation is read by its derivation query, a
node by reading its label. Both take an optional cell; where there is none, a touch does nothing
and a read returns a fixed value, so neither makes a query.

A hash chain from a derived secret whose intermediate values are computed but not used has a
normal form over these operations. For a sequence of cells `cell : ℕ → Option (X ⊕ K)`,
`touchUpTo cell s` touches cells `0, …, s - 1` in order and `touchRead cell s` then reads cell `s`.
In the eager game `CanonicalGraph.eagerImpl` a read draws its cell and a touch draws its cell and
discards the value (`CanonicalGraph.eagerImpl_readCell_run`,
`CanonicalGraph.eagerImpl_touchCell_run`), so there a touch-then-read over cells that all exist
draws cells `0, …, s` and returns the value of cell `s`
(`CanonicalGraph.eagerImpl_touchRead_succ_run`). Whether or not the cells exist, a touch is in
the eager game a read whose value is discarded (`CanonicalGraph.simulateQ_eagerImpl_touchCell`),
so a touch-then-read of cell `s + 1` is the touch-then-read of cell `s` followed by a read of cell
`s + 1` (`CanonicalGraph.simulateQ_eagerImpl_touchRead_succ`).

The `_pred` lemmas carry a predicate on programs, closed under `pure` and `bind`, from the touches
and reads of cells to these programs.
-/

public section

open OracleSpec

namespace OracleComp

variable {ι : Type} {pub : OracleSpec ι} {X K R : Type}

/-- Touch a cell, if there is one. -/
@[expose] def touchCell : Option (X ⊕ K) → OracleComp (pub.withLabels X K R) Unit
  | none => pure ()
  | some c => query (spec := pub.withLabels X K R) (.inr (.inl c))

/-- Read a cell: the derivation query of a derivation, the label of a node, and a fixed value
where there is no cell. -/
@[expose] noncomputable def readCell [Nonempty R] :
    Option (X ⊕ K) → OracleComp (pub.withLabels X K R) R
  | none => pure (Classical.arbitrary R)
  | some (.inl x) => query (spec := pub.withLabels X K R) (.inl (.inr x))
  | some (.inr k) => query (spec := pub.withLabels X K R) (.inr (.inr k))

/-- Touch cells `0, …, s - 1` of `cell`, in order. -/
@[expose] def touchUpTo (cell : ℕ → Option (X ⊕ K)) : ℕ → OracleComp (pub.withLabels X K R) Unit
  | 0 => pure ()
  | s + 1 => do
      touchUpTo cell s
      touchCell (cell s)

/-- Touch cells `0, …, s - 1` of `cell`, then read cell `s`. -/
@[expose] noncomputable def touchRead [Nonempty R] (cell : ℕ → Option (X ⊕ K)) (s : ℕ) :
    OracleComp (pub.withLabels X K R) R := do
  touchUpTo cell s
  readCell (cell s)

section Pred

variable {Q : ∀ {α : Type}, OracleComp (pub.withLabels X K R) α → Prop}
  (hpure : ∀ {α : Type} (x : α), Q (pure x))
  (hbind : ∀ {α β : Type} (oa : OracleComp (pub.withLabels X K R) α)
    (ob : α → OracleComp (pub.withLabels X K R) β), Q oa → (∀ x, Q (ob x)) → Q (oa >>= ob))
  (htouch : ∀ c, Q (touchCell (some c)))

include hpure htouch in
/-- A touch satisfies `Q` when every touch of a cell does. -/
theorem touchCell_pred : ∀ c, Q (touchCell c)
  | none => hpure ()
  | some c => htouch c

include hpure hbind htouch in
/-- Touching a prefix of cells satisfies `Q` when every touch of a cell does. -/
theorem touchUpTo_pred (cell : ℕ → Option (X ⊕ K)) : ∀ s, Q (touchUpTo cell s)
  | 0 => hpure ()
  | s + 1 => hbind _ _ (touchUpTo_pred cell s) fun _ => touchCell_pred hpure htouch _

variable [Nonempty R] (hread : ∀ c, Q (readCell (some c)))

include hpure hread in
/-- A read satisfies `Q` when every read of a cell does. -/
theorem readCell_pred : ∀ c, Q (readCell c)
  | none => hpure _
  | some c => hread c

include hpure hbind htouch hread in
/-- A touch-then-read satisfies `Q` when every touch and every read of a cell does. -/
theorem touchRead_pred (cell : ℕ → Option (X ⊕ K)) (s : ℕ) : Q (touchRead cell s) :=
  hbind _ _ (touchUpTo_pred hpure hbind htouch cell s) fun _ => readCell_pred hpure hread _

end Pred

end OracleComp

namespace CanonicalGraph

open OracleComp

variable {ι : Type} {pub : OracleSpec ι} {X K R : Type} (G : CanonicalGraph pub X K R)
  [DecidableEq ι] [DecidableEq X] [DecidableEq K] [SampleableType R]
  [∀ t, SampleableType (pub.Range t)]

/-- In the eager game a read draws its cell. -/
theorem eagerImpl_readCell_run (c : X ⊕ K) (st : RelabelState pub X K R) :
    (simulateQ G.eagerImpl (readCell (some c))).run st = (RelabelState.drawCell c).run st := by
  rcases c with x | k
  · simp only [readCell, simulateQ_HasQuery_query, eagerImpl_apply_inl, relabelImpl_apply_inr]
  · simp only [readCell, simulateQ_HasQuery_query, eagerImpl_apply_inr]
    rfl

/-- In the eager game a touch draws its cell and discards the value. -/
theorem eagerImpl_touchCell_run (c : X ⊕ K) (st : RelabelState pub X K R) :
    (simulateQ G.eagerImpl (touchCell (some c))).run st =
      (fun z => ((), z.2)) <$> (RelabelState.drawCell c).run st := by
  simp only [touchCell, simulateQ_HasQuery_query, eagerImpl_apply_inr]
  simp [RelabelState.labelImpl]

/-- In the eager game, when cells `s` and `s + 1` exist, reading cell `s + 1` after touching cells
`0, …, s` is the touch-then-read of cell `s` followed by a draw of cell `s + 1`. -/
theorem eagerImpl_touchRead_succ_run (cell : ℕ → Option (X ⊕ K)) (s : ℕ) {c c' : X ⊕ K}
    (hc : cell s = some c) (hc' : cell (s + 1) = some c') (st : RelabelState pub X K R) :
    (simulateQ G.eagerImpl (touchRead cell (s + 1))).run st =
      (simulateQ G.eagerImpl (touchRead cell s)).run st >>= fun z =>
        (RelabelState.drawCell c').run z.2 := by
  simp only [touchRead, touchUpTo, hc, hc', simulateQ_bind, StateT.run_bind, bind_assoc,
    G.eagerImpl_readCell_run, G.eagerImpl_touchCell_run, bind_map_left]

/-- In the eager game a touch is a read whose value is discarded, whether or not the cell
exists. -/
theorem simulateQ_eagerImpl_touchCell (c : Option (X ⊕ K)) :
    simulateQ G.eagerImpl (touchCell c) = (fun _ ↦ ()) <$> simulateQ G.eagerImpl (readCell c) := by
  rcases c with _ | c
  · simp [touchCell, readCell]
  · exact StateT.ext fun st ↦ by
      rw [StateT.run_map, G.eagerImpl_touchCell_run, G.eagerImpl_readCell_run]

/-- In the eager game a touch-then-read of cell `s + 1` is the touch-then-read of cell `s`
followed by a read of cell `s + 1`, whether or not the cells exist. -/
theorem simulateQ_eagerImpl_touchRead_succ (cell : ℕ → Option (X ⊕ K)) (s : ℕ) :
    simulateQ G.eagerImpl (touchRead cell (s + 1)) =
      simulateQ G.eagerImpl (touchRead cell s) >>= fun _ ↦
        simulateQ G.eagerImpl (readCell (cell (s + 1))) := by
  simp only [touchRead, touchUpTo, simulateQ_bind, G.simulateQ_eagerImpl_touchCell, bind_assoc,
    bind_map_left]

end CanonicalGraph
