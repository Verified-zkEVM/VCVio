/-
Copyright (c) 2026 VCVio Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: VCVio Contributors
-/
module

public import VCVio.OracleComp.QueryTracking.RandomOracle.JointPotential.EagerSubgraph.Run

/-! # A public query outside a selected eager subgraph -/

public section
open OracleSpec OracleComp
namespace VCVioTest.RandomOracleEagerSubgraph

def small : CanonicalGraph (Bool →ₒ Bool) Unit Unit Bool where
  ch _ := []
  pt _ _ := false
  range_eq _ _ := rfl
  pt_inj {_ _ xs ys} hx hy _ := by
    have x := List.eq_nil_of_length_eq_zero hx
    have y := List.eq_nil_of_length_eq_zero hy
    exact ⟨Subsingleton.elim _ _, x.trans y.symm⟩

def big : CanonicalGraph (Bool →ₒ Bool) Unit Bool Bool where
  ch _ := []
  pt b _ := b
  range_eq _ _ := rfl
  pt_inj {_ _ xs ys} hx hy eq := by
    have x := List.eq_nil_of_length_eq_zero hx
    have y := List.eq_nil_of_length_eq_zero hy
    exact ⟨eq, x.trans y.symm⟩

def selected : small.Subgraph big where
  cell := ⟨Sum.map id (fun _ => false), by rintro (a|a) (b|b) eq <;> simp_all⟩
  node _ := false
  node_cell _ := rfl
  children _ := rfl
  point _ _ := rfl

/-- Repeating the selected ordinary query preserves both the outside canonical and public rows. -/
theorem repeat_selected : selected.Preserves (do
    let a ← query (spec := (Bool →ₒ Bool).withLabels Unit Unit Bool) (.inl (.inl (.inr false)))
    let b ← query (spec := (Bool →ₒ Bool).withLabels Unit Unit Bool) (.inl (.inl (.inr false)))
    pure (a,b)) :=
  selected.preserves_bind (selected.preserves_public () [] rfl) fun _ =>
    selected.preserves_bind (selected.preserves_public () [] rfl) fun _ => selected.preserves_pure _

/-- An unselected public point can fill an unselected canonical row in the empty cache. -/
theorem outside_changes {z : Bool × RelabelState (Bool →ₒ Bool) Unit Bool Bool}
    (run : z ∈ support ((big.eagerImpl (.inl (.inl (.inr true)))).run (∅, ∅))) :
    ¬selected.Framed (∅, ∅) z.2 := by
  have ready : big.childVals (∅, ∅) true = some [] := big.childVals_eq_some_iff.mpr .nil
  change z ∈ support ((big.relabelImpl (.inl (.inr (big.pt true [])))).run (∅, ∅)) at run
  rw [big.relabelImpl_run_pt ready, support_map] at run
  obtain ⟨w, hw, rfl⟩ := run
  have stored := (RelabelState.le_and_cell_eq_of_mem_support_drawCell hw).2
  intro frame
  have outside := frame.cells (.inr true) (by rintro ⟨c,eq⟩; cases c <;> cases eq)
  change w.2.2 (.inr true) = none at outside
  rw [stored] at outside
  contradiction

/-- The first read selects a touch or an ordinary query without losing the outside cells. -/
theorem exact_adaptive : selected.Exact (do
    let a ← readCell (pub := Bool →ₒ Bool) (some (.inl ())) (K := Unit)
    if a then touchCell (some (.inr ())) else do
      let _ ← query (spec := (Bool →ₒ Bool).withLabels Unit Unit Bool) (.inl (.inl (.inr false)))
      pure ()) := by
  apply selected.exact_bind (selected.exact_readCell (.inl ()))
  intro a
  cases a with
  | false =>
    exact selected.exact_bind (selected.exact_public () [] rfl) fun _ => selected.exact_pure ()
  | true => exact selected.exact_touchCell (.inr ())

/-- An unselected ordinary query cannot satisfy exactness when it fills an outside private label. -/
theorem not_exact_outside : ¬selected.Exact
    (query (spec := (Bool →ₒ Bool).withLabels Unit Unit Bool) (.inl (.inl (.inr true)))) := by
  intro law
  have eqn := law (∅, ∅)
  simp only [simulateQ_HasQuery_query, CanonicalGraph.Subgraph.liftQuery] at eqn
  obtain ⟨z, hz⟩ := OracleComp.support_nonempty
    ((big.eagerImpl (.inl (.inl (.inr true)))).run (∅, ∅))
  have ready : big.childVals (∅, ∅) true = some [] := big.childVals_eq_some_iff.mpr .nil
  have drawn := hz
  change z ∈ support ((big.relabelImpl (.inl (.inr (big.pt true [])))).run (∅, ∅)) at drawn
  rw [big.relabelImpl_run_pt ready, support_map] at drawn
  obtain ⟨w, hw, rfl⟩ := drawn
  have outside : Sum.inr true ∉ Set.range selected.cell := by
    rintro ⟨c, eq⟩
    cases c <;> cases eq
  have filled := (RelabelState.le_and_cell_eq_of_mem_support_drawCell hw).2
  rw [eqn, support_map] at hz
  obtain ⟨u, _, same⟩ := hz
  have noChange := congrArg (fun a : Bool × RelabelState (Bool →ₒ Bool) Unit Bool Bool =>
    a.2.2 (.inr true)) same
  change (selected.extend (∅, ∅) u.2).2 (.inr true) = w.2.2 (.inr true) at noChange
  rw [selected.extend_outside _ _ outside, filled] at noChange
  contradiction

end VCVioTest.RandomOracleEagerSubgraph
