/-
Copyright (c) 2026 VCVio Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: VCVio Contributors
-/
module

public import VCVio.OracleComp.QueryTracking.RandomOracle.JointPotential.Subgraph
public import VCVio.OracleComp.QueryTracking.RandomOracle.TouchRead

/-!
# Running an eager computation in a larger graph

A public query at any well-formed point of the selected graph can become ready only there.
The projection keeps the whole ordinary public cache and all selected graph cells.
-/

public section

open OracleComp OracleSpec
namespace CanonicalGraph.Subgraph

variable {ι X K X' K' R : Type} {pub : OracleSpec ι}
  {S : CanonicalGraph pub X K R} {G : CanonicalGraph pub X' K' R} (f : S.Subgraph G)

/-- All graph cells outside the selection retain their exact initial contents. -/
@[expose] def Framed (s t : RelabelState pub X' K' R) : Prop :=
  ∀ c, c ∉ Set.range f.cell → t.2 c = s.2 c

variable [DecidableEq X] [DecidableEq K] [DecidableEq X'] [DecidableEq K']
  [DecidableEq ι] [SampleableType R] [∀ t, SampleableType (pub.Range t)]

/-- Interpret the selected graph's requests in the larger graph. -/
@[expose] noncomputable def liftQuery :
    QueryImpl (pub.withLabels X K R) (OracleComp (pub.withLabels X' K' R)) :=
  fun q => match q with
  | .inl (.inl (.inl n)) => query (spec := pub.withLabels X' K' R) (.inl (.inl (.inl n)))
  | .inl (.inl (.inr t)) => query (spec := pub.withLabels X' K' R) (.inl (.inl (.inr t)))
  | .inl (.inr x) => readCell (some (f.cell (.inl x)))
  | .inr (.inl c) => touchCell (some (f.cell c))
  | .inr (.inr k) => readCell (some (.inr (f.node k)))

/-- Each full execution projects to a supported selected execution with the same reply. -/
@[expose] def Preserves {α : Type} (p : OracleComp (pub.withLabels X K R) α) : Prop :=
  ∀ (s : RelabelState pub X' K' R) z, z ∈ support ((simulateQ G.eagerImpl
      (simulateQ f.liftQuery p)).run s) →
    (z.1, f.project z.2) ∈ support ((simulateQ S.eagerImpl p).run (f.project s)) ∧ f.Framed s z.2

theorem preserves_pure {α : Type} (a : α) : f.Preserves (pure a) := by
  intro s z run
  simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at run ⊢
  subst z
  exact ⟨rfl, fun _ _ => rfl⟩

theorem preserves_bind {α β : Type} {p : OracleComp (pub.withLabels X K R) α}
    {k : α → OracleComp (pub.withLabels X K R) β}
    (first : f.Preserves p) (rest : ∀ a, f.Preserves (k a)) : f.Preserves (p >>= k) := by
  intro s z run
  simp only [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at run ⊢
  obtain ⟨w, hw, hz⟩ := run
  obtain ⟨head, outside⟩ := first s w hw
  obtain ⟨tail, outside'⟩ := rest w.1 w.2 z hz
  exact ⟨⟨(w.1, f.project w.2), head, tail⟩, fun c hc => (outside' c hc).trans (outside c hc)⟩

theorem preserves_map {α β : Type} (g : α → β) {p : OracleComp (pub.withLabels X K R) α}
    (ready : f.Preserves p) : f.Preserves (g <$> p) := by
  rw [← bind_pure_comp]
  exact f.preserves_bind ready (fun a => f.preserves_pure (g a))

omit [DecidableEq ι] [∀ t, SampleableType (pub.Range t)] in
private theorem draw_selected (c : X ⊕ K) (s : RelabelState pub X' K' R) {z}
    (run : z ∈ support ((RelabelState.drawCell (f.cell c)).run s)) :
    (z.1, f.project z.2) ∈ support ((RelabelState.drawCell c).run (f.project s)) ∧ f.Framed s z.2 := by
  cases old : s.2 (f.cell c) with
  | some a =>
    have here : (f.project s).2 c = some a := old
    rw [RelabelState.drawCell_run_of_cell_eq_some old, mem_support_pure_iff] at run
    subst z
    rw [RelabelState.drawCell_run_of_cell_eq_some here, mem_support_pure_iff]
    exact ⟨rfl, fun _ _ => rfl⟩
  | none =>
    have here : (f.project s).2 c = none := old
    rw [RelabelState.drawCell_run_of_cell_eq_none old, support_map] at run
    obtain ⟨u, hu, rfl⟩ := run
    rw [RelabelState.drawCell_run_of_cell_eq_none here, support_map]
    refine ⟨⟨u, hu, ?_⟩, ?_⟩
    · exact congrArg (fun t => (u, t)) (f.project_update s c u).symm
    · intro x outside
      exact QueryCache.cacheQuery_of_ne _ _ (fun eq => outside ⟨c, eq.symm⟩)

theorem preserves_readCell (c : X ⊕ K) : f.Preserves (readCell (some c)) := by
  intro s z run
  rw [S.eagerImpl_readCell_run]
  cases c with
  | inl x =>
    change z ∈ support ((simulateQ G.eagerImpl
      (simulateQ f.liftQuery (query (spec := pub.withLabels X K R) (.inl (.inr x))))).run s) at run
    rw [simulateQ_HasQuery_query] at run
    exact f.draw_selected _ s (G.eagerImpl_readCell_run _ s ▸ run)
  | inr k =>
    change z ∈ support ((simulateQ G.eagerImpl
      (simulateQ f.liftQuery (query (spec := pub.withLabels X K R) (.inr (.inr k))))).run s) at run
    rw [simulateQ_HasQuery_query] at run
    exact f.draw_selected (.inr k) s (by
      rw [f.node_cell]
      exact G.eagerImpl_readCell_run _ s ▸ run)

/-- A physical query with a well-formed input for a selected node cannot select any other node. -/
theorem preserves_public {I : Type} {A : CanonicalGraph (I →ₒ R) X K R}
    {B : CanonicalGraph (I →ₒ R) X' K' R} (v : A.Subgraph B) [DecidableEq I]
    (k : K) (vs : List R) (width : vs.length = (A.ch k).length) :
    v.Preserves (query (spec := (I →ₒ R).withLabels X K R) (.inl (.inl (.inr (A.pt k vs))))) := by
  intro s z run
  simp only [simulateQ_HasQuery_query, liftQuery, eagerImpl_apply_inl] at run ⊢
  have width' : vs.length = (B.ch (v.node k)).length := by simpa only [v.children, List.length_map] using width
  by_cases ready : A.childVals (v.project s) k = some vs
  · have global := (v.childVals s k).trans ready
    rw [v.point, B.relabelImpl_run_pt global, support_map] at run
    obtain ⟨w, hw, rfl⟩ := run
    have smaller := v.draw_selected (.inr k) s (by simpa only [v.node_cell] using hw)
    rw [A.relabelImpl_run_pt ready, support_map]
    exact ⟨⟨_, smaller.1, rfl⟩, smaller.2⟩
  · have small : ¬∃ r xs, A.childVals (v.project s) r = some xs ∧ A.pt r xs = A.pt k vs := by
      rintro ⟨r,xs,h,eq⟩
      obtain ⟨rfl,rfl⟩ := A.pt_inj (A.length_eq_of_childVals_eq_some h) width eq
      exact ready h
    have large : ¬∃ r xs, B.childVals s r = some xs ∧ B.pt r xs = A.pt k vs := by
      rintro ⟨r,xs,h,eq⟩
      obtain ⟨same,rfl⟩ := B.pt_inj (B.length_eq_of_childVals_eq_some h) width' (eq.trans (v.point k vs))
      subst r
      exact ready ((v.childVals s k).symm.trans h)
    rw [B.relabelImpl_run_pub_of_not_exists large, support_map] at run
    obtain ⟨w, hw, rfl⟩ := run
    rw [A.relabelImpl_run_pub_of_not_exists small, support_map]
    exact ⟨⟨w, hw, rfl⟩, fun _ _ => rfl⟩

end CanonicalGraph.Subgraph
