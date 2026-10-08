/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module

public import VCVio.OracleComp.QueryTracking.RandomOracle.Defer
public import VCVio.OracleComp.QueryTracking.RandomOracle.TouchRead
public import VCVio.OracleComp.QueryTracking.QueryBound.Simulation

/-!
# Read sets of the deferred game

In the deferred game `CanonicalGraph.deferredImpl` of a canonical graph `G` a step draws at most
one cell: a derivation draws its derivation cell, a read draws the label it reads, and a public
query at the point of a node whose children are all drawn, at their values, draws that node's
label. A sampling query, a touch, and a public query answered by the public cache draw nothing
(`CanonicalGraph.cell_eq_or_draws_of_mem_support_deferredImpl`).

`CanonicalGraph.ReadsWithin G D` is the predicate on queries under which a step draws no cell
outside a set of cells `D`: derivations and reads of cells of `D`, and public queries at points
of no node outside `D`. A program all of whose queries satisfy it leaves every cell outside `D`
as it found it (`CanonicalGraph.cell_eq_of_mem_support_simulateQ_deferredImpl`), by
`OracleComp.AllQueriesSatisfy.holds_of_mem_support_run_simulateQ`. The touches and reads of
`OracleComp.touchRead` satisfy it as soon as the cell it reads lies in `D`, whatever it touches.

## Main statements

- `CanonicalGraph.cell_eq_or_draws_of_mem_support_deferredImpl`: a step changes a cell only by
  drawing it.
- `CanonicalGraph.cell_eq_of_mem_support_deferredImpl` and
  `CanonicalGraph.cell_eq_of_mem_support_simulateQ_deferredImpl`: a step, and a run, whose
  queries satisfy `ReadsWithin G D` leave every cell outside `D` unchanged.
- `CanonicalGraph.cell_eq_of_mem_support_simulateQ_deferredImpl_readCell`: a read of a cell
  returns the value drawn at that cell.
- `CanonicalGraph.allQueriesSatisfy_readsWithin_readCell` and
  `CanonicalGraph.allQueriesSatisfy_readsWithin_touchRead`: the read sets of the touch-then-read
  programs.
-/

public section

open OracleSpec

namespace CanonicalGraph

open OracleComp

variable {ι : Type} {pub : OracleSpec ι} {X K R : Type} (G : CanonicalGraph pub X K R)

/-- The queries that draw, in the deferred game, no cell outside `D`: a sampling query, a touch,
a derivation or a read of a cell of `D`, and a public query at a point that is the point of no
node outside `D`. -/
@[expose] def ReadsWithin (D : Set (X ⊕ K)) : (pub.withLabels X K R).Domain → Prop
  | .inl (.inl (.inl _)) => True
  | .inl (.inl (.inr t)) => ∀ k vs, G.pt k vs = t → .inr k ∈ D
  | .inl (.inr x) => .inl x ∈ D
  | .inr (.inl _) => True
  | .inr (.inr k) => .inr k ∈ D

/-! ## The read sets of the touch-then-read programs -/

section Read

variable [Nonempty R]

/-- A read draws at most the cell it reads. -/
theorem allQueriesSatisfy_readsWithin_readCell {D : Set (X ⊕ K)} {c : Option (X ⊕ K)}
    (h : ∀ c', c = some c' → c' ∈ D) :
    AllQueriesSatisfy (readCell (pub := pub) (R := R) c) (G.ReadsWithin D) :=
  match c, h with
  | none, _ => allQueriesSatisfy_pure _ _
  | some (.inl _), h => (allQueriesSatisfy_query_iff _ _).2 (h _ rfl)
  | some (.inr _), h => (allQueriesSatisfy_query_iff _ _).2 (h _ rfl)

/-- A touch-then-read draws at most the cell it reads. -/
theorem allQueriesSatisfy_readsWithin_touchRead {D : Set (X ⊕ K)} {cell : ℕ → Option (X ⊕ K)}
    {s : ℕ} (h : ∀ c, cell s = some c → c ∈ D) :
    AllQueriesSatisfy (touchRead (pub := pub) (R := R) cell s) (G.ReadsWithin D) :=
  allQueriesSatisfy_bind (touchUpTo_pred (Q := (AllQueriesSatisfy · (G.ReadsWithin D)))
    (fun _ ↦ allQueriesSatisfy_pure _ _) (fun _ _ ↦ allQueriesSatisfy_bind)
    (fun _ ↦ (allQueriesSatisfy_query_iff _ _).2 trivial) cell s) fun _ ↦
      G.allQueriesSatisfy_readsWithin_readCell h

end Read

/-! ## Frames of the deferred game -/

variable [DecidableEq ι] [DecidableEq X] [DecidableEq K] [SampleableType R]
  [∀ t, SampleableType (pub.Range t)]

/-- A step of the deferred game changes a cell only by drawing it: as the label of a node whose
children are drawn before the step, at a public query at the node's point, or as the cell a
derivation or a read names. -/
theorem cell_eq_or_draws_of_mem_support_deferredImpl {t : (pub.withLabels X K R).Domain}
    {s : RelabelState pub X K R × List (X ⊕ K)} {z} (hz : z ∈ support ((G.deferredImpl t).run s))
    (c : X ⊕ K) :
    z.2.1.2 c = s.1.2 c ∨
      (∃ k vs, c = .inr k ∧ G.childVals s.1 k = some vs ∧ t = .inl (.inl (.inr (G.pt k vs)))) ∨
      (∃ x, t = .inl (.inr x) ∧ c = .inl x) ∨ ∃ k, t = .inr (.inr k) ∧ c = .inr k := by
  rcases t with (((n | t) | x) | (c' | k))
  · rw [deferredImpl_run_inl, relabelImpl_run_unif, Functor.map_map, support_map] at hz
    obtain ⟨_, -, rfl⟩ := hz
    exact .inl rfl
  · rw [deferredImpl_run_inl, support_map] at hz
    obtain ⟨w, hw, rfl⟩ := hz
    by_cases hex : ∃ k vs, G.childVals s.1 k = some vs ∧ G.pt k vs = t
    · obtain ⟨k, vs, hk, rfl⟩ := hex
      rw [G.relabelImpl_run_pt hk, support_map] at hw
      obtain ⟨w, hw, rfl⟩ := hw
      by_cases hc : c = .inr k
      · exact .inr (.inl ⟨k, vs, hc, hk, rfl⟩)
      · exact .inl (RelabelState.cell_eq_of_mem_support_drawCell hw hc)
    · rw [G.relabelImpl_run_pub_of_not_exists hex, support_map] at hw
      obtain ⟨w, -, rfl⟩ := hw
      exact .inl rfl
  · rw [deferredImpl_run_inl, relabelImpl_apply_inr, support_map] at hz
    obtain ⟨w, hw, rfl⟩ := hz
    by_cases hc : c = .inl x
    · exact .inr (.inr (.inl ⟨x, rfl, hc⟩))
    · exact .inl (RelabelState.cell_eq_of_mem_support_drawCell hw hc)
  · rw [deferredImpl_run_touch, support_pure, Set.mem_singleton_iff] at hz
    exact .inl (by rw [hz])
  · rw [deferredImpl_run_read, support_map] at hz
    obtain ⟨w, hw, rfl⟩ := hz
    by_cases hc : c = .inr k
    · exact .inr (.inr (.inr ⟨k, rfl, hc⟩))
    · exact .inl (RelabelState.cell_eq_of_mem_support_drawCell hw hc)

/-- A step of the deferred game at a query that reads within `D` changes no cell outside `D`. -/
theorem cell_eq_of_mem_support_deferredImpl {D : Set (X ⊕ K)}
    {t : (pub.withLabels X K R).Domain} (ht : G.ReadsWithin D t)
    {s : RelabelState pub X K R × List (X ⊕ K)} {z} (hz : z ∈ support ((G.deferredImpl t).run s))
    {c : X ⊕ K} (hc : c ∉ D) : z.2.1.2 c = s.1.2 c := by
  rcases G.cell_eq_or_draws_of_mem_support_deferredImpl hz c with
    h | ⟨k, vs, rfl, -, rfl⟩ | ⟨x, rfl, rfl⟩ | ⟨k, rfl, rfl⟩
  · exact h
  · exact absurd (ht k vs rfl) hc
  all_goals exact absurd ht hc

/-- **The read-set frame.** A run of the deferred game of a program whose queries all read within
`D` changes no cell outside `D`. -/
theorem cell_eq_of_mem_support_simulateQ_deferredImpl {D : Set (X ⊕ K)} {α : Type}
    {oa : OracleComp (pub.withLabels X K R) α} (h : AllQueriesSatisfy oa (G.ReadsWithin D))
    {s : RelabelState pub X K R × List (X ⊕ K)} {z : α × (RelabelState pub X K R × List (X ⊕ K))}
    (hz : z ∈ support ((simulateQ G.deferredImpl oa).run s)) {c : X ⊕ K} (hc : c ∉ D) :
    z.2.1.2 c = s.1.2 c :=
  h.holds_of_mem_support_run_simulateQ (fun s' ↦ s'.1.2 c = s.1.2 c)
    (fun _ ht _ hs' _ hw ↦ (G.cell_eq_of_mem_support_deferredImpl ht hw hc).trans hs') rfl hz

/-- In the deferred game a read of a cell returns the value drawn at that cell. -/
theorem cell_eq_of_mem_support_simulateQ_deferredImpl_readCell {c : X ⊕ K}
    {s : RelabelState pub X K R × List (X ⊕ K)} {z : R × (RelabelState pub X K R × List (X ⊕ K))}
    (hz : z ∈ support ((simulateQ G.deferredImpl (readCell (some c))).run s)) :
    z.2.1.2 c = some z.1 := by
  rcases c with x | k
  · simp only [readCell, simulateQ_HasQuery_query] at hz
    change z ∈ support ((G.deferredImpl (.inl (.inr x))).run s) at hz
    rw [deferredImpl_run_inl, relabelImpl_apply_inr, support_map] at hz
    obtain ⟨w, hw, rfl⟩ := hz
    exact (RelabelState.le_and_cell_eq_of_mem_support_drawCell hw).2
  · simp only [readCell, simulateQ_HasQuery_query] at hz
    change z ∈ support ((G.deferredImpl (.inr (.inr k))).run s) at hz
    rw [deferredImpl_run_read, support_map] at hz
    obtain ⟨w, hw, rfl⟩ := hz
    exact (RelabelState.le_and_cell_eq_of_mem_support_drawCell hw).2

end CanonicalGraph
