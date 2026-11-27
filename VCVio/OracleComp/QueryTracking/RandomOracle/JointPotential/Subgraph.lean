/-
Copyright (c) 2026 VCVio Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: VCVio Contributors
-/

module

public import VCVio.OracleComp.QueryTracking.RandomOracle.JointPotential

/-!
# Charged hazards in a subgraph

Drawing a cell outside the chosen subgraph leaves the projected state unchanged.
If a public point misses every ready node, it also misses every ready node in the subgraph.
These two properties preserve the charge for any hazard in the subgraph.
-/

public section

open OracleComp OracleSpec
open scoped ENNReal

namespace CanonicalGraph

variable {ι X K X' K' R : Type} {pub : OracleSpec ι}
variable {S : CanonicalGraph pub X K R} {G : CanonicalGraph pub X' K' R}

/-- A subgraph preserves the ordered children and public points of its selected nodes. -/
structure Subgraph (S : CanonicalGraph pub X K R) (G : CanonicalGraph pub X' K' R) where
  /-- Embed a selected private input or node label into the containing graph. -/
  cell : (X ⊕ K) ↪ (X' ⊕ K')
  /-- The node of the containing graph that supplies each selected public point. -/
  node : K → K'
  node_cell : ∀ k, cell (.inr k) = .inr (node k)
  children : ∀ k, G.ch (node k) = (S.ch k).map cell
  point : ∀ k vs, S.pt k vs = G.pt (node k) vs

namespace Subgraph
variable (f : Subgraph S G)

/-- Keep the entire public cache and the selected graph cells. -/
@[expose] def project (st : RelabelState pub X' K' R) : RelabelState pub X K R :=
  (st.1, QueryCache.ofFn fun c => st.2 (f.cell c))

/-- Extending both full caches also extends the projected caches. -/
theorem project_mono : Monotone f.project := by
  intro st later h
  refine ⟨h.1, ?_⟩
  intro c u e
  exact h.2 e

/-- Projection preserves the values of the ordered children, including a missing child. -/
theorem childVals (st : RelabelState pub X' K' R) (k : K) :
    G.childVals st (f.node k) = S.childVals (f.project st) k := by
  apply Option.ext
  intro vs
  rw [G.childVals_eq_some_iff, S.childVals_eq_some_iff, f.children, List.forall₂_map_left_iff]
  rfl

variable [DecidableEq X] [DecidableEq K] [DecidableEq X'] [DecidableEq K']

/-- A write to a selected cell updates exactly that cell in the projection. -/
theorem project_update (st : RelabelState pub X' K' R) (c : X ⊕ K) (v : R) :
    f.project (st.1, st.2.cacheQuery (f.cell c) v) =
      ((f.project st).1, (f.project st).2.cacheQuery c v) := by
  refine Prod.ext (by rfl) ?_
  apply QueryCache.ext
  intro x
  by_cases same : x = c
  · subst x
    simp [project]
  · simp [project, QueryCache.cacheQuery_of_ne _ _ same,
      QueryCache.cacheQuery_of_ne _ _ (fun eq => same (f.cell.injective eq))]

omit [DecidableEq X] [DecidableEq K] in
private theorem project_outside (st : RelabelState pub X' K' R) (c : X' ⊕ K') (v : R)
    (outside : ¬∃ x, f.cell x = c) : f.project (st.1, st.2.cacheQuery c v) = f.project st := by
  refine Prod.ext (by rfl) ?_
  apply QueryCache.ext
  intro x
  exact QueryCache.cacheQuery_of_ne _ _ (fun eq => outside ⟨x, eq⟩)

variable [DecidableEq ι] [SampleableType R] [∀ t, SampleableType (pub.Range t)]

/-- A hazard charged in the selected graph keeps its potential in the full graph.
Drawing a cell outside the selection leaves the projected potential unchanged and cannot
introduce the projected hazard. -/
theorem isCharged {P : RelabelState pub X K R → Prop} {φ : RelabelState pub X K R → ℝ≥0∞}
    (charge : S.IsCharged P φ) : G.IsCharged (P ∘ f.project) (φ ∘ f.project) where
  mono := charge.mono.comp f.project_mono
  cell st c safe fresh := by
    by_cases h : ∃ x, f.cell x = c
    · obtain ⟨x, rfl⟩ := h
      simpa only [Function.comp_apply, f.project_update] using
        charge.cell (f.project st) x safe fresh
    · refine ⟨0, ?_, ?_⟩
      · simp only [Function.comp_apply, f.project_outside st c _ h]
        exact (prEvent_eq_zero_of_forall_not _ _ (fun _ => safe)).le
      · intro v
        simp only [Function.comp_apply, f.project_outside st c v h, zero_add, le_refl]
  pub st t safe fresh miss := by
    apply charge.pub (f.project st) t safe fresh
    rintro ⟨k, vs, ready, pt⟩
    exact miss ⟨f.node k, vs, (f.childVals st k).trans ready, (f.point k vs).symm.trans pt⟩

end Subgraph
end CanonicalGraph
