/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module

public import VCVio.OracleComp.QueryTracking.RandomOracle.Defer
public import VCVio.OracleComp.QueryTracking.RandomOracle.TouchRead

/-!
# Read sets of the deferred game

In the deferred game `CanonicalGraph.deferredImpl` of a canonical graph `G` a step draws at most
one cell: a derivation draws its derivation cell, a read draws the label it reads, and a public
query at the point of a node whose children are all drawn, at their values, draws that node's
label. A sampling query, a touch, and a public query answered by the public cache draw nothing.

`CanonicalGraph.ReadsWithin G D` is the predicate on queries under which a step draws no cell
outside a set of cells `D`: derivations and reads of cells of `D`, and public queries at points
of no node outside `D`. A program all of whose queries satisfy it leaves every cell outside `D`
as it found it (`CanonicalGraph.cell_eq_of_mem_support_simulateQ_deferredImpl`). The touches and
reads of `OracleComp.touchCell`, `OracleComp.readCell` and `OracleComp.touchRead` satisfy it as
soon as the cells they read lie in `D`, whatever they touch.

Two generic facts about programs all of whose queries satisfy a predicate `P` underlie this. An
invariant of the state that every step at a query satisfying `P` preserves holds at the end of
every run of such a program (`OracleComp.AllQueriesSatisfy.holds_of_mem_support_run_simulateQ`).
Simulated through a handler whose programs at the queries satisfying `P` make only queries
satisfying `Q`, such a program makes only queries satisfying `Q`
(`OracleComp.AllQueriesSatisfy.simulateQ`).

## Main statements

- `OracleComp.AllQueriesSatisfy.holds_of_mem_support_run_simulateQ`: invariants of a run whose
  queries all satisfy a predicate.
- `OracleComp.AllQueriesSatisfy.simulateQ`: the queries of a simulation through a handler.
- `CanonicalGraph.cell_eq_of_mem_support_deferredImpl` and
  `CanonicalGraph.cell_eq_of_mem_support_simulateQ_deferredImpl`: a step, and a run, whose
  queries satisfy `ReadsWithin G D` leave every cell outside `D` unchanged.
- `CanonicalGraph.cell_eq_or_exists_childVals_of_mem_support_deferredImpl`: a sampling or public
  step changes a cell only by drawing the label of a node whose children are drawn.
- `CanonicalGraph.cell_eq_of_mem_support_simulateQ_deferredImpl_readCell`: a read of a cell
  returns the value drawn at that cell.
- `CanonicalGraph.allQueriesSatisfy_readsWithin_touchCell`,
  `CanonicalGraph.allQueriesSatisfy_readsWithin_readCell` and
  `CanonicalGraph.allQueriesSatisfy_readsWithin_touchRead`: the read sets of the touch-then-read
  programs.
-/

public section

open OracleSpec

namespace OracleComp

variable {ι : Type} {spec : OracleSpec ι} {σ α : Type}

/-- **Invariants of a run with restricted queries.** If every query of `oa` satisfies `P`, and
every step of `impl` at a query satisfying `P` preserves `Inv`, then a run of `oa` from a state
satisfying `Inv` ends in a state satisfying `Inv`. -/
theorem AllQueriesSatisfy.holds_of_mem_support_run_simulateQ
    {impl : QueryImpl spec (StateT σ ProbComp)} {P : ι → Prop} {oa : OracleComp spec α}
    (h : AllQueriesSatisfy oa P) (Inv : σ → Prop)
    (hstep : ∀ t, P t → ∀ s, Inv s → ∀ z ∈ support ((impl t).run s), Inv z.2) {s : σ}
    (hs : Inv s) {z : α × σ} (hz : z ∈ support ((simulateQ impl oa).run s)) : Inv z.2 := by
  induction oa using OracleComp.inductionOn generalizing s z with
  | pure a =>
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    exact hz ▸ hs
  | query_bind t oa ih =>
    rw [allQueriesSatisfy_query_bind_iff] at h
    have hz' : z ∈ support (((simulateQ impl
        (OracleSpec.query t : OracleComp spec (spec.Range t))).run s) >>=
          fun w ↦ (simulateQ impl (oa w.1)).run w.2) := by
      simpa [simulateQ_bind, OracleComp.liftM_def] using hz
    obtain ⟨w, hw, hz⟩ := (mem_support_bind_iff _ _ _).1 hz'
    exact ih w.1 (h.2 w.1) (hstep t h.1 s hs w (by simpa [simulateQ_spec_query] using hw)) hz

/-- A simulation of a program whose queries all satisfy `P`, through a handler whose programs at
the queries satisfying `P` make only queries satisfying `Q`, makes only queries satisfying `Q`. -/
theorem AllQueriesSatisfy.simulateQ {τ : Type} {spec' : OracleSpec τ}
    {impl : QueryImpl spec (OracleComp spec')} {P : ι → Prop} {Q : τ → Prop}
    {oa : OracleComp spec α} (h : AllQueriesSatisfy oa P)
    (himpl : ∀ t, P t → AllQueriesSatisfy (impl t) Q) :
    AllQueriesSatisfy (_root_.simulateQ impl oa) Q := by
  induction oa using OracleComp.inductionOn with
  | pure x => exact allQueriesSatisfy_pure x Q
  | query_bind t k ih =>
    rw [allQueriesSatisfy_query_bind_iff] at h
    rw [simulateQ_bind, simulateQ_spec_query]
    exact allQueriesSatisfy_bind (himpl t h.1) fun u ↦ ih u (h.2 u)

end OracleComp

namespace RelabelState

variable {ι : Type} {pub : OracleSpec ι} {X K R : Type} [DecidableEq X] [DecidableEq K]
  [SampleableType R]

/-- Drawing a cell keeps the public cache. -/
theorem fst_eq_of_mem_support_drawCell {c : X ⊕ K} {st : RelabelState pub X K R}
    {z : R × RelabelState pub X K R} (hz : z ∈ support ((drawCell c).run st)) : z.2.1 = st.1 := by
  rw [drawCell_run, support_map] at hz
  obtain ⟨w, -, rfl⟩ := hz
  rfl

/-- Drawing a cell changes no other cell. -/
theorem cell_eq_of_mem_support_drawCell {c c' : X ⊕ K} {st : RelabelState pub X K R}
    {z : R × RelabelState pub X K R} (hz : z ∈ support ((drawCell c).run st)) (hc : c' ≠ c) :
    z.2.2 c' = st.2 c' := by
  cases h : st.2 c with
  | some v =>
    rw [drawCell_run_of_cell_eq_some h, support_pure, Set.mem_singleton_iff] at hz
    rw [hz]
  | none =>
    rw [drawCell_run_of_cell_eq_none h, support_map] at hz
    obtain ⟨u, -, rfl⟩ := hz
    exact QueryCache.cacheQuery_of_ne _ _ hc

end RelabelState

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

/-- A touch draws no cell. -/
theorem allQueriesSatisfy_readsWithin_touchCell (D : Set (X ⊕ K)) (c : Option (X ⊕ K)) :
    AllQueriesSatisfy (touchCell (pub := pub) (R := R) c) (G.ReadsWithin D) := by
  rcases c with _ | c
  · exact allQueriesSatisfy_pure _ _
  · exact (allQueriesSatisfy_query_iff _ _).2 trivial

/-- Touching a prefix of cells draws no cell. -/
theorem allQueriesSatisfy_readsWithin_touchUpTo (D : Set (X ⊕ K)) (cell : ℕ → Option (X ⊕ K)) :
    ∀ s, AllQueriesSatisfy (touchUpTo (pub := pub) (R := R) cell s) (G.ReadsWithin D)
  | 0 => allQueriesSatisfy_pure _ _
  | s + 1 => allQueriesSatisfy_bind (allQueriesSatisfy_readsWithin_touchUpTo D cell s) fun _ =>
      G.allQueriesSatisfy_readsWithin_touchCell D _

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
  allQueriesSatisfy_bind (G.allQueriesSatisfy_readsWithin_touchUpTo D cell s) fun _ =>
    G.allQueriesSatisfy_readsWithin_readCell h

end Read

/-! ## Frames of the deferred game -/

variable [DecidableEq ι] [DecidableEq X] [DecidableEq K] [SampleableType R]
  [∀ t, SampleableType (pub.Range t)]

/-- A step of the deferred game at a query that reads within `D` changes no cell outside `D`. -/
theorem cell_eq_of_mem_support_deferredImpl {D : Set (X ⊕ K)}
    {t : (pub.withLabels X K R).Domain} (ht : G.ReadsWithin D t)
    {s : RelabelState pub X K R × List (X ⊕ K)} {z} (hz : z ∈ support ((G.deferredImpl t).run s))
    {c : X ⊕ K} (hc : c ∉ D) : z.2.1.2 c = s.1.2 c := by
  rcases t with (((n | t) | x) | (c' | k))
  · rw [deferredImpl_run_inl, relabelImpl_run_unif, Functor.map_map, support_map] at hz
    obtain ⟨_, -, rfl⟩ := hz
    rfl
  · rw [deferredImpl_run_inl, support_map] at hz
    obtain ⟨w, hw, rfl⟩ := hz
    by_cases hex : ∃ k vs, G.childVals s.1 k = some vs ∧ G.pt k vs = t
    · obtain ⟨k, vs, hk, rfl⟩ := hex
      rw [G.relabelImpl_run_pt hk, support_map] at hw
      obtain ⟨w, hw, rfl⟩ := hw
      exact RelabelState.cell_eq_of_mem_support_drawCell hw fun h ↦ hc (h ▸ ht k vs rfl)
    · rw [G.relabelImpl_run_pub_of_not_exists hex, support_map] at hw
      obtain ⟨w, -, rfl⟩ := hw
      rfl
  · rw [deferredImpl_run_inl, relabelImpl_apply_inr, support_map] at hz
    obtain ⟨w, hw, rfl⟩ := hz
    exact RelabelState.cell_eq_of_mem_support_drawCell hw fun h ↦ hc (h ▸ ht)
  · rw [deferredImpl_run_touch, support_pure, Set.mem_singleton_iff] at hz
    rw [hz]
  · rw [deferredImpl_run_read, support_map] at hz
    obtain ⟨w, hw, rfl⟩ := hz
    exact RelabelState.cell_eq_of_mem_support_drawCell hw fun h ↦ hc (h ▸ ht)

/-- **The read-set frame.** A run of the deferred game of a program whose queries all read within
`D` changes no cell outside `D`. -/
theorem cell_eq_of_mem_support_simulateQ_deferredImpl {D : Set (X ⊕ K)} {α : Type}
    {oa : OracleComp (pub.withLabels X K R) α} (h : AllQueriesSatisfy oa (G.ReadsWithin D))
    {s : RelabelState pub X K R × List (X ⊕ K)} {z : α × (RelabelState pub X K R × List (X ⊕ K))}
    (hz : z ∈ support ((simulateQ G.deferredImpl oa).run s)) {c : X ⊕ K} (hc : c ∉ D) :
    z.2.1.2 c = s.1.2 c :=
  h.holds_of_mem_support_run_simulateQ (fun s' ↦ s'.1.2 c = s.1.2 c)
    (fun _ ht _ hs' _ hw ↦ (G.cell_eq_of_mem_support_deferredImpl ht hw hc).trans hs') rfl hz

/-- A sampling or public step of the deferred game changes a cell only by drawing the label of a
node whose children are all drawn before the step. -/
theorem cell_eq_or_exists_childVals_of_mem_support_deferredImpl {t : ℕ ⊕ ι}
    {s : RelabelState pub X K R × List (X ⊕ K)} {z}
    (hz : z ∈ support ((G.deferredImpl (.inl (.inl t))).run s)) (c : X ⊕ K) :
    z.2.1.2 c = s.1.2 c ∨ ∃ k vs, c = .inr k ∧ G.childVals s.1 k = some vs := by
  rcases t with n | t
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
      · exact .inr ⟨k, vs, hc, hk⟩
      · exact .inl (RelabelState.cell_eq_of_mem_support_drawCell hw hc)
    · rw [G.relabelImpl_run_pub_of_not_exists hex, support_map] at hw
      obtain ⟨w, -, rfl⟩ := hw
      exact .inl rfl

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
