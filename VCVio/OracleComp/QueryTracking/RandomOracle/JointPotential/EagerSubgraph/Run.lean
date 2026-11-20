/-
Copyright (c) 2026 VCVio Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: VCVio Contributors
-/

module

public import VCVio.OracleComp.QueryTracking.RandomOracle.JointPotential.EagerSubgraph
import Mathlib.Logic.Function.Basic

/-!
# Exact executions of a selected eager subgraph

An execution in the selected graph supplies the return value, the entire public cache and
the selected private cells. The initial state supplies all private cells outside the embedding.
-/

public section

open OracleComp OracleSpec

namespace CanonicalGraph.Subgraph

variable {ι X K X' K' R : Type} {pub : OracleSpec ι}
  {S : CanonicalGraph pub X K R} {G : CanonicalGraph pub X' K' R} (f : S.Subgraph G)

/-- Combine a selected graph's terminal state with the initial values outside the embedding. -/
@[expose] noncomputable def extend (s : RelabelState pub X' K' R) (t : RelabelState pub X K R) :
    RelabelState pub X' K' R :=
  (t.1, QueryCache.ofFn fun c =>
    Function.extend (γ := Option R) f.cell (fun a => t.2 a) (fun b => s.2 b) c)

/-- A selected cell takes its full terminal value from the small graph. -/
theorem extend_at (s : RelabelState pub X' K' R) (t : RelabelState pub X K R) (c : X ⊕ K) :
    (f.extend s t).2 (f.cell c) = t.2 c :=
  f.cell.injective.extend_apply _ _ _

/-- An unselected cell retains exactly its initial value or absence. -/
theorem extend_outside (s : RelabelState pub X' K' R) (t : RelabelState pub X K R)
    {c : X' ⊕ K'} (away : c ∉ Set.range f.cell) : (f.extend s t).2 c = s.2 c :=
  Function.extend_apply' _ _ _ away

/-- Replacing the selected cells by their initial projection restores the initial state. -/
theorem extend_project (s : RelabelState pub X' K' R) : f.extend s (f.project s) = s := by
  refine Prod.ext rfl (QueryCache.ext fun c => ?_)
  by_cases selected : c ∈ Set.range f.cell
  · obtain ⟨x, rfl⟩ := selected
    exact f.extend_at _ _ x
  · exact f.extend_outside _ _ selected

/-- Projecting a reconstructed state returns the supplied selected state. -/
theorem project_extend (s : RelabelState pub X' K' R) (t : RelabelState pub X K R) :
    f.project (f.extend s t) = t :=
  Prod.ext rfl (QueryCache.ext (fun c => f.extend_at _ _ c))

private theorem extend_extend (s : RelabelState pub X' K' R) (u t : RelabelState pub X K R) :
    f.extend (f.extend s u) t = f.extend s t := by
  refine Prod.ext rfl (QueryCache.ext fun c => ?_)
  by_cases selected : c ∈ Set.range f.cell
  · obtain ⟨x, rfl⟩ := selected
    rw [f.extend_at, f.extend_at]
  · rw [f.extend_outside _ _ selected, f.extend_outside _ _ selected, f.extend_outside _ _ selected]

variable [DecidableEq X] [DecidableEq K] [DecidableEq X'] [DecidableEq K']
  [DecidableEq ι] [SampleableType R] [∀ t, SampleableType (pub.Range t)]

/-- The small graph determines the whole eager computation, including both final caches. -/
@[expose] def Exact {α : Type} (p : OracleComp (pub.withLabels X K R) α) : Prop :=
  ∀ s, (simulateQ G.eagerImpl (simulateQ f.liftQuery p)).run s =
    (fun z => (z.1, f.extend s z.2)) <$> (simulateQ S.eagerImpl p).run (f.project s)

/-- A pure computation keeps its entire initial state. -/
theorem exact_pure {α : Type} (a : α) : f.Exact (pure a) := by
  intro s
  simp [f.extend_project]

/-- Exact executions compose through a continuation chosen by the returned value. -/
theorem exact_bind {α β : Type} {p : OracleComp (pub.withLabels X K R) α}
    {k : α → OracleComp (pub.withLabels X K R) β}
    (first : f.Exact p) (rest : ∀ a, f.Exact (k a)) : f.Exact (p >>= k) := by
  intro s
  simp only [simulateQ_bind, StateT.run_bind, first s, bind_map_left, map_bind]
  apply bind_congr
  rintro ⟨a, u⟩
  simp only [rest a (f.extend s u), f.project_extend, f.extend_extend]

/-- Changing the returned value preserves exactness. -/
theorem exact_map {α β : Type} (g : α → β) {p : OracleComp (pub.withLabels X K R) α}
    (small : f.Exact p) : f.Exact (g <$> p) := by
  rw [← bind_pure_comp]
  exact f.exact_bind small fun a => f.exact_pure (g a)

omit [DecidableEq ι] [∀ t, SampleableType (pub.Range t)] in
private theorem exact_draw (c : X ⊕ K) (s : RelabelState pub X' K' R) :
    (RelabelState.drawCell (f.cell c)).run s =
      (fun z => (z.1, f.extend s z.2)) <$> (RelabelState.drawCell c).run (f.project s) := by
  cases old : s.2 (f.cell c) with
  | some a =>
    have here : (f.project s).2 c = some a := old
    rw [RelabelState.drawCell_run_of_cell_eq_some old,
      RelabelState.drawCell_run_of_cell_eq_some here]
    simp [f.extend_project]
  | none =>
    have here : (f.project s).2 c = none := old
    rw [RelabelState.drawCell_run_of_cell_eq_none old,
      RelabelState.drawCell_run_of_cell_eq_none here]
    simp only [Functor.map_map]
    congr 1
    funext w
    congr 1
    refine Prod.ext rfl (QueryCache.ext fun x => ?_)
    by_cases inside : x ∈ Set.range f.cell
    · obtain ⟨b, rfl⟩ := inside
      rw [f.extend_at]
      exact congrArg (fun z : RelabelState pub X K R => z.2 b) (f.project_update s c w)
    · rw [f.extend_outside _ _ inside]
      exact QueryCache.cacheQuery_of_ne _ _ fun eq => inside ⟨c, eq.symm⟩

/-- A selected private read obtains exactly the same sample or warm value in either graph. -/
theorem exact_readCell (c : X ⊕ K) : f.Exact (readCell (some c)) := by
  intro s
  rw [S.eagerImpl_readCell_run]
  cases c with
  | inl x =>
    change (simulateQ G.eagerImpl (simulateQ f.liftQuery
      (query (spec := pub.withLabels X K R) (.inl (.inr x))))).run s = _
    rw [simulateQ_HasQuery_query]
    exact (G.eagerImpl_readCell_run _ s).trans (f.exact_draw _ s)
  | inr k =>
    change (simulateQ G.eagerImpl (simulateQ f.liftQuery
      (query (spec := pub.withLabels X K R) (.inr (.inr k))))).run s = _
    rw [simulateQ_HasQuery_query]
    change (simulateQ G.eagerImpl (readCell (some (.inr (f.node k))))).run s = _
    rw [G.eagerImpl_readCell_run]
    simpa only [f.node_cell] using f.exact_draw (.inr k) s

/-- A selected touch makes the same update while discarding the sampled value. -/
theorem exact_touchCell (c : X ⊕ K) : f.Exact (touchCell (some c)) := by
  intro s
  rw [S.eagerImpl_touchCell_run]
  change (simulateQ G.eagerImpl (simulateQ f.liftQuery
    (query (spec := pub.withLabels X K R) (.inr (.inl c))))).run s = _
  rw [simulateQ_HasQuery_query]
  change (simulateQ G.eagerImpl (touchCell (some (f.cell c)))).run s = _
  rw [G.eagerImpl_touchCell_run, f.exact_draw]
  simp [Functor.map_map]

/-- A well-formed public query for the selected graph can be answered only by its own node
or by its ordinary public cache. -/
theorem exact_public {I : Type} {A : CanonicalGraph (I →ₒ R) X K R}
    {B : CanonicalGraph (I →ₒ R) X' K' R} (v : A.Subgraph B) [DecidableEq I]
    (k : K) (vs : List R) (width : vs.length = (A.ch k).length) :
    v.Exact (query (spec := (I →ₒ R).withLabels X K R) (.inl (.inl (.inr (A.pt k vs))))) := by
  intro s
  simp only [simulateQ_HasQuery_query, liftQuery, eagerImpl_apply_inl]
  have width' : vs.length = (B.ch (v.node k)).length := by
    simpa only [v.children, List.length_map] using width
  by_cases ready : A.childVals (v.project s) k = some vs
  · have global := (v.childVals s k).trans ready
    rw [A.relabelImpl_run_pt ready, v.point, B.relabelImpl_run_pt global]
    have law := v.exact_draw (.inr k) s
    rw [v.node_cell] at law
    rw [law]
    simp [Functor.map_map]
  · have small : ¬∃ r xs, A.childVals (v.project s) r = some xs ∧ A.pt r xs = A.pt k vs := by
      rintro ⟨r,xs,h,eq⟩
      obtain ⟨rfl,rfl⟩ := A.pt_inj (A.length_eq_of_childVals_eq_some h) width eq
      exact ready h
    have large : ¬∃ r xs, B.childVals s r = some xs ∧ B.pt r xs = A.pt k vs := by
      rintro ⟨r,xs,h,eq⟩
      obtain ⟨same, rfl⟩ := B.pt_inj (B.length_eq_of_childVals_eq_some h) width'
        (eq.trans (v.point k vs))
      subst r
      exact ready ((v.childVals s k).symm.trans h)
    rw [B.relabelImpl_run_pub_of_not_exists large, A.relabelImpl_run_pub_of_not_exists small]
    simp only [Functor.map_map]
    congr 1
    funext z
    exact congrArg (fun t : RelabelState (I →ₒ R) X' K' R => (z.1, (z.2,t.2)))
      (v.extend_project s).symm

/-- Equal selected executions on every warm cache give equal executions in the containing graph. -/
theorem run_eq_of_exact {α : Type} {p q : OracleComp (pub.withLabels X K R) α}
    (hp : f.Exact p) (hq : f.Exact q)
    (same : ∀ t, (simulateQ S.eagerImpl p).run t = (simulateQ S.eagerImpl q).run t)
    (s : RelabelState pub X' K' R) :
    (simulateQ G.eagerImpl (simulateQ f.liftQuery p)).run s =
      (simulateQ G.eagerImpl (simulateQ f.liftQuery q)).run s := by
  rw [hp s, hq s, same]

end CanonicalGraph.Subgraph
