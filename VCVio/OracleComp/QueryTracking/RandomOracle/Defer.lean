/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module

public import VCVio.OracleComp.QueryTracking.RandomOracle.Relabel
public import VCVio.OracleComp.QueryTracking.RandomOracle.Commute
public import VCVio.OracleComp.SimSemantics.StateT.Measure

/-!
# Deferred touches of a relabelled lazy random oracle

In the eager game `CanonicalGraph.eagerImpl` of a canonical graph `G`, a `touch c` draws the cell
`c` and discards it. The deferred game `CanonicalGraph.deferredImpl` instead records `c` in a
pending list and leaves it undrawn; every other query is answered as in the eager game, so a public
query at a node point whose children include an undrawn touched cell is answered by the public
cache. The end fill `RelabelState.endFill` then runs the random oracle on the cell cache at every
pending cell, which draws the cells still undrawn and leaves the public cache unchanged. Its steps
are random-oracle queries whose answers are the drawn values.

Deferring a touch changes the run only through the public queries that would have read a label
completed by touched cells: in the deferred game such a query is cached as a public answer, and
the end fill later completes the node's children at a point the public cache holds, which is the
final-state predicate `CanonicalGraph.Conflict`. An event of the eager game is therefore at most
the same event of the deferred game after the end fill, or a conflict
(`CanonicalGraph.prEvent_eagerImpl_le_deferredImpl`).

The bound turns a hit on a touched value into a conflict. A query at the point of a node whose
child is a cell touched earlier, at the drawn value, is not a conflict in the eager game: there it
reads the node's label. In the deferred game the same query is cached as a public answer while the
cell is undrawn, and drawing the cell at that value in the end fill is a conflict, whose
probability is that of guessing a fresh uniform value.

The proof goes through the masked game `CanonicalGraph.maskedImpl`, the eager game with the cells
drawn only by touches hidden from the public queries until they are drawn by a real read.
* The masked game, with the hidden cells forgotten, is dominated by the eager game until a
  conflict (`CanonicalGraph.dominatedUntilBad_maskedImpl`): a public query that the two games
  answer differently completes, in the masked game, a node whose point it caches.
* The end fill with its cells hidden, `RelabelState.maskedFill`, intertwines the deferred game
  with the masked game (`CanonicalGraph.intertwines_maskedFill`): drawing a touched cell when it is
  touched or after the run has the same distribution, because queries to the lazy random oracle
  commute (`randomOracle.evalDist_run_bind_simulateQ_run_swap`).
  `QueryImpl.Intertwines.evalDist_simulateQ_run` carries a step-wise intertwining to whole runs,
  which gives an equality of final-state distributions
  (`CanonicalGraph.prEvent_deferredImpl_endFill_eq_maskedFill_bind_maskedImpl`).

## Main statements

- `CanonicalGraph.prEvent_eagerImpl_le_deferredImpl`: from a state with no pending cell, the eager
  game is at most the deferred game after the end fill, or a conflict.
- `CanonicalGraph.prEvent_deferredImpl_endFill_eq_maskedFill_bind_maskedImpl` and
  `CanonicalGraph.prEvent_deferredImpl_endFill_eq_maskedImpl`: the deferred game after the end fill
  has the final-state distribution of the masked game.
- `CanonicalGraph.prEvent_eagerImpl_le_maskedImpl`: the eager game is at most the masked game, or a
  conflict.
-/

public section

open OracleComp OracleSpec MeasureTheory

namespace RelabelState

variable {ι : Type} {pub : OracleSpec ι} {X K R : Type} [DecidableEq X] [DecidableEq K]

/-- A state read with a set of hidden cells undrawn. -/
def mask (s : RelabelState pub X K R × Finset (X ⊕ K)) : RelabelState pub X K R :=
  (s.1.1, .ofFn fun c ↦ if c ∈ s.2 then none else s.1.2 c)

theorem mask_apply (s : RelabelState pub X K R × Finset (X ⊕ K)) (c : X ⊕ K) :
    (mask s).2 c = if c ∈ s.2 then none else s.1.2 c := by
  simp only [mask, QueryCache.ofFn_apply]

/-- Hiding cells gives a state below the full one. -/
theorem mask_le (s : RelabelState pub X K R × Finset (X ⊕ K)) : mask s ≤ s.1 := by
  refine ⟨le_rfl, fun c v hc ↦ ?_⟩
  rw [mask_apply] at hc
  split_ifs at hc
  exact hc

variable [SampleableType R]

/-- Draw a cell and stop hiding it. -/
noncomputable def revealCell (c : X ⊕ K) :
    StateT (RelabelState pub X K R × Finset (X ⊕ K)) ProbComp R :=
  StateT.mk fun s ↦ (fun z ↦ (z.1, (z.2, s.2.erase c))) <$> (drawCell c).run s.1

theorem revealCell_run (c : X ⊕ K) (s : RelabelState pub X K R × Finset (X ⊕ K)) :
    (revealCell c).run s = (fun z ↦ (z.1, (z.2, s.2.erase c))) <$> (drawCell c).run s.1 := by
  simp only [revealCell, StateT.run_mk]

/-! ## The end fill -/

/-- **The end fill.** Run the random oracle on the cell cache at each pending cell in turn,
drawing the undrawn ones; the public cache is unchanged. -/
noncomputable def endFill (s : RelabelState pub X K R × List (X ⊕ K)) :
    ProbComp (RelabelState pub X K R) :=
  (fun w ↦ (s.1.1, w.2)) <$>
    (simulateQ ((X ⊕ K) →ₒ R).randomOracle (((X ⊕ K) →ₒ R).queryAll s.2)).run s.1.2

/-- The end fill with the cells it draws hidden. -/
noncomputable def maskedFill (s : RelabelState pub X K R × List (X ⊕ K)) :
    ProbComp (RelabelState pub X K R × Finset (X ⊕ K)) :=
  (fun st ↦ (st, s.1.2.uncached s.2)) <$> endFill s

/-- The end fill runs the random oracle on the cell cache at the pending cells, keeping the public
cache. -/
theorem endFill_eq (st : RelabelState pub X K R) (cs : List (X ⊕ K)) :
    endFill (st, cs) = (fun w ↦ (st.1, w.2)) <$>
      (simulateQ ((X ⊕ K) →ₒ R).randomOracle (((X ⊕ K) →ₒ R).queryAll cs)).run st.2 := by
  simp only [endFill]

/-- The cell oracle on the whole relabelled state: a query of a cell draws it if it is undrawn
and keeps the public cache. -/
noncomputable def cellImpl :
    QueryImpl ((X ⊕ K) →ₒ R) (StateT (RelabelState pub X K R) ProbComp) :=
  fun c ↦ drawCell c

/-- The end fill is the cell oracle on the whole relabelled state, run at the pending cells. -/
theorem endFill_eq_simulateQ_cellImpl (s : RelabelState pub X K R × List (X ⊕ K)) :
    endFill s =
      Prod.snd <$> (simulateQ (cellImpl (pub := pub)) (((X ⊕ K) →ₒ R).queryAll s.2)).run s.1 := by
  obtain ⟨st, cs⟩ := s
  rw [endFill_eq]
  induction cs generalizing st with
  | nil => simp only [OracleSpec.queryAll_nil, simulateQ_pure, StateT.run_pure, map_pure]
  | cons c cs ih =>
    simp only [OracleSpec.queryAll_cons, simulateQ_bind, simulateQ_spec_query, StateT.run_bind,
      map_bind, cellImpl, drawCell_run, bind_map_left, ← ih]

/-- The masked end fill runs the random oracle on the cell cache at the pending cells, and hides
the pending cells undrawn before it. -/
theorem maskedFill_eq (st : RelabelState pub X K R) (cs : List (X ⊕ K)) :
    maskedFill (st, cs) = (fun w ↦ ((st.1, w.2), st.2.uncached cs)) <$>
      (simulateQ ((X ⊕ K) →ₒ R).randomOracle (((X ⊕ K) →ₒ R).queryAll cs)).run st.2 := by
  rw [maskedFill, endFill_eq, Functor.map_map]

/-- The end fill of an empty pending list leaves the state unchanged. -/
@[simp] theorem endFill_nil (st : RelabelState pub X K R) : endFill (st, []) = pure st := by
  simp only [endFill_eq, queryAll_nil, simulateQ_pure, StateT.run_pure, map_pure, Prod.mk.eta]

/-- The masked end fill of an empty pending list leaves the state unchanged and hides nothing. -/
@[simp] theorem maskedFill_nil (st : RelabelState pub X K R) :
    maskedFill (st, []) = pure (st, ∅) := by
  simp only [maskedFill_eq, QueryCache.uncached, List.toFinset_nil, Finset.filter_empty,
    queryAll_nil, simulateQ_pure, StateT.run_pure, map_pure, Prod.mk.eta]

/-- Read with its hidden cells undrawn, a state produced by the masked end fill is the state
before the fill. -/
theorem mask_eq_of_mem_support_maskedFill {st : RelabelState pub X K R} {cs : List (X ⊕ K)}
    {s'} (hs : s' ∈ support (maskedFill (st, cs))) : mask s' = st := by
  rw [maskedFill_eq, support_map] at hs
  obtain ⟨w, hw, rfl⟩ := hs
  obtain ⟨hle, hiff⟩ := QueryImpl.withCaching_queryAll_le_and_isSome_iff _ hw
  refine Prod.ext rfl (QueryCache.ext fun c ↦ ?_)
  rw [mask_apply]
  by_cases hc : c ∈ st.2.uncached cs
  · simp only [hc, ↓reduceIte, (QueryCache.mem_uncached.1 hc).2]
  · simp only [hc, ↓reduceIte]
    cases h : st.2 c with
    | some v => exact hle h
    | none =>
      have hcs : c ∉ cs := fun hcs ↦ hc (QueryCache.mem_uncached.2 ⟨hcs, h⟩)
      refine Option.not_isSome_iff_eq_none.1 fun hw' ↦ ?_
      rcases (hiff c).1 hw' with h' | h'
      · rw [h] at h'; exact Bool.false_ne_true h'
      · exact hcs h'

/-- Drawing a cell and then filling commutes with filling and then revealing the cell. -/
theorem evalDist_drawCell_bind_maskedFill (c : X ⊕ K) (st : RelabelState pub X K R)
    (cs : List (X ⊕ K)) {γ : Type} [MeasurableSpace γ]
    (f : R → RelabelState pub X K R × Finset (X ⊕ K) → ProbComp γ) :
    𝒟[(drawCell c).run st >>= fun z ↦ maskedFill (z.2, cs) >>= f z.1] =
      𝒟[maskedFill (st, cs) >>= fun s' ↦ (revealCell c).run s' >>= fun z ↦ f z.1 z.2] := by
  simp only [drawCell_run, maskedFill_eq, revealCell_run, bind_map_left]
  calc _ = 𝒟[(((X ⊕ K) →ₒ R).randomOracle c).run st.2 >>= fun z ↦
        (simulateQ ((X ⊕ K) →ₒ R).randomOracle (((X ⊕ K) →ₒ R).queryAll cs)).run z.2 >>= fun w ↦
          f z.1 ((st.1, w.2), (st.2.uncached cs).erase c)] :=
        evalDist_bind_congr_of_support _ _ _ fun z hz ↦ by
          rw [QueryImpl.withCaching_run_uncached _ hz]
    _ = _ := randomOracle.evalDist_run_bind_simulateQ_run_swap c _ st.2
        fun u _ D ↦ f u ((st.1, D), (st.2.uncached cs).erase c)

end RelabelState

namespace CanonicalGraph

variable {ι : Type} {pub : OracleSpec ι} {X K R : Type} (G : CanonicalGraph pub X K R)
  [DecidableEq ι] [DecidableEq X] [DecidableEq K] [SampleableType R]
  [∀ t, SampleableType (pub.Range t)]

/-- **The deferred game.** The relabelled game, with the label of a node read by drawing it; a
touch only records its cell in a pending list. -/
noncomputable def deferredImpl : QueryImpl (pub.withLabels X K R)
    (StateT (RelabelState pub X K R × List (X ⊕ K)) ProbComp) := fun
  | .inl t => StateT.mk fun s ↦ (fun z ↦ (z.1, (z.2, s.2))) <$> (G.relabelImpl t).run s.1
  | .inr (.inl c) => StateT.mk fun s ↦ pure ((), (s.1, s.2 ++ [c]))
  | .inr (.inr k) => StateT.mk fun s ↦
      (fun z ↦ (z.1, (z.2, s.2))) <$> (RelabelState.drawCell (.inr k)).run s.1

open Classical in
/-- The eager game with the cells drawn only by touches hidden: a set of hidden cells is kept
alongside the state. A touch of an undrawn cell draws and hides it; every other draw of a cell
reveals it; a public query at the point of a node whose children are all drawn and not hidden,
at their values, draws (or reads) the node's label, and every other public query is answered by
the public cache. -/
noncomputable def maskedImpl : QueryImpl (pub.withLabels X K R)
    (StateT (RelabelState pub X K R × Finset (X ⊕ K)) ProbComp) := fun
  | .inl (.inl (.inl n)) => StateT.mk fun s ↦ (fun u ↦ (u, s)) <$> (unifSpec.query n : ProbComp _)
  | .inl (.inl (.inr t)) => StateT.mk fun s ↦
      if h : ∃ k vs, G.childVals (RelabelState.mask s) k = some vs ∧ G.pt k vs = t then
        Prod.map (cast (G.range_eq_of_pt_eq h.choose_spec.choose_spec.2).symm) id <$>
          (RelabelState.revealCell (.inr h.choose)).run s
      else (fun z ↦ (z.1, ((z.2, s.1.2), s.2))) <$> (pub.randomOracle t).run s.1.1
  | .inl (.inr x) => RelabelState.revealCell (.inl x)
  | .inr (.inl c) => StateT.mk fun s ↦
      (fun z ↦ ((), (z.2, if (s.1.2 c).isNone then insert c s.2 else s.2))) <$>
        (RelabelState.drawCell c).run s.1
  | .inr (.inr k) => RelabelState.revealCell (.inr k)

/-! ## Run equations -/

theorem deferredImpl_run_inl (t : (pub.withDerivations X R).Domain)
    (s : RelabelState pub X K R × List (X ⊕ K)) :
    (G.deferredImpl (.inl t)).run s = (fun z ↦ (z.1, (z.2, s.2))) <$> (G.relabelImpl t).run s.1 :=
  by simp only [deferredImpl, StateT.run_mk]

theorem deferredImpl_run_touch (c : X ⊕ K) (s : RelabelState pub X K R × List (X ⊕ K)) :
    (G.deferredImpl (.inr (.inl c))).run s = pure ((), (s.1, s.2 ++ [c])) := by
  simp only [deferredImpl, StateT.run_mk]

theorem deferredImpl_run_read (k : K) (s : RelabelState pub X K R × List (X ⊕ K)) :
    (G.deferredImpl (.inr (.inr k))).run s =
      (fun z ↦ (z.1, (z.2, s.2))) <$> (RelabelState.drawCell (.inr k)).run s.1 := by
  simp only [deferredImpl, StateT.run_mk]

theorem maskedImpl_run_unif (n : ℕ) (s : RelabelState pub X K R × Finset (X ⊕ K)) :
    (G.maskedImpl (.inl (.inl (.inl n)))).run s =
      (fun u ↦ (u, s)) <$> (unifSpec.query n : ProbComp _) := by
  simp only [maskedImpl, StateT.run_mk]
  rfl

theorem maskedImpl_apply_derive (x : X) :
    G.maskedImpl (.inl (.inr x)) = RelabelState.revealCell (.inl x) := by
  simp only [maskedImpl]

theorem maskedImpl_apply_read (k : K) :
    G.maskedImpl (.inr (.inr k)) = RelabelState.revealCell (.inr k) := by
  simp only [maskedImpl]

theorem maskedImpl_run_touch (c : X ⊕ K) (s : RelabelState pub X K R × Finset (X ⊕ K)) :
    (G.maskedImpl (.inr (.inl c))).run s =
      (fun z ↦ ((), (z.2, if (s.1.2 c).isNone then insert c s.2 else s.2))) <$>
        (RelabelState.drawCell c).run s.1 := by
  simp only [maskedImpl, StateT.run_mk]

/-- A public query at the point of a node whose children are drawn and not hidden, at their
values, draws (or reads) its label and reveals it. -/
theorem maskedImpl_run_pt {s : RelabelState pub X K R × Finset (X ⊕ K)} {k : K} {vs : List R}
    (h : G.childVals (RelabelState.mask s) k = some vs) :
    (G.maskedImpl (.inl (.inl (.inr (G.pt k vs))))).run s =
      Prod.map (cast (G.range_eq k vs).symm) id <$> (RelabelState.revealCell (.inr k)).run s := by
  simp only [maskedImpl, StateT.run_mk]
  exact G.dite_exists_pt_eq h
    (fun k' e ↦ Prod.map (cast e.symm) id <$> (RelabelState.revealCell (.inr k')).run s) _

/-- A public query at a point of no node whose children are drawn and not hidden is answered by
the public cache. -/
theorem maskedImpl_run_pub_of_not_exists {s : RelabelState pub X K R × Finset (X ⊕ K)} {t : ι}
    (ht : ¬∃ k vs, G.childVals (RelabelState.mask s) k = some vs ∧ G.pt k vs = t) :
    (G.maskedImpl (.inl (.inl (.inr t)))).run s =
      (fun z ↦ (z.1, ((z.2, s.1.2), s.2))) <$> (pub.randomOracle t).run s.1.1 := by
  simp only [maskedImpl, StateT.run_mk, ht, ↓reduceDIte]

/-! ## The masked end fill intertwines the deferred and masked games -/

/-- The masked end fill intertwines the deferred game with the masked game. -/
theorem intertwines_maskedFill :
    QueryImpl.Intertwines RelabelState.maskedFill G.deferredImpl G.maskedImpl := by
  rintro (((n | t) | x) | (c | k)) ⟨st, cs⟩ γ _ f
  · rw [deferredImpl_run_inl, relabelImpl_run_unif]
    simp only [maskedImpl_run_unif, bind_map_left]
    exact OracleComp.evalDist_bind_bind_swap _ _ fun u s' ↦ f u s'
  · by_cases h : ∃ k vs, G.childVals st k = some vs ∧ G.pt k vs = t
    · obtain ⟨k, vs, hk, rfl⟩ := h
      rw [deferredImpl_run_inl, G.relabelImpl_run_pt hk]
      simp only [bind_map_left, Prod.map_fst, Prod.map_snd, id_eq]
      refine (RelabelState.evalDist_drawCell_bind_maskedFill (.inr k) st cs
        fun u s' ↦ f (cast (G.range_eq k vs).symm u) s').trans ?_
      refine evalDist_bind_congr_of_support _ _ _ fun s' hs' ↦ ?_
      rw [G.maskedImpl_run_pt
        (by rw [RelabelState.mask_eq_of_mem_support_maskedFill hs']; exact hk), bind_map_left]
      rfl
    · rw [deferredImpl_run_inl, G.relabelImpl_run_pub_of_not_exists h]
      set F := (simulateQ ((X ⊕ K) →ₒ R).randomOracle (((X ⊕ K) →ₒ R).queryAll cs)).run st.2
      calc _ = 𝒟[(pub.randomOracle t).run st.1 >>= fun y ↦ F >>= fun w ↦
            f y.1 ((y.2, w.2), st.2.uncached cs)] := by
            simp only [Functor.map_map, bind_map_left, RelabelState.maskedFill_eq, F]
        _ = 𝒟[F >>= fun w ↦ (pub.randomOracle t).run st.1 >>= fun y ↦
            f y.1 ((y.2, w.2), st.2.uncached cs)] := OracleComp.evalDist_bind_bind_swap _ _ _
        _ = _ := by
          rw [RelabelState.maskedFill_eq, bind_map_left]
          refine evalDist_bind_congr_of_support _ _ _ fun w hw ↦ ?_
          have hm := RelabelState.mask_eq_of_mem_support_maskedFill (st := st) (cs := cs)
            (s' := ((st.1, w.2), st.2.uncached cs))
            (by rw [RelabelState.maskedFill_eq, support_map]; exact ⟨w, hw, rfl⟩)
          rw [G.maskedImpl_run_pub_of_not_exists (by rw [hm]; exact h), bind_map_left]
  · rw [deferredImpl_run_inl, relabelImpl_apply_inr, bind_map_left, maskedImpl_apply_derive]
    exact RelabelState.evalDist_drawCell_bind_maskedFill (.inl x) st cs f
  · rw [deferredImpl_run_touch, pure_bind, RelabelState.maskedFill_eq, RelabelState.maskedFill_eq,
      OracleSpec.queryAll_append, simulateQ_bind, StateT.run_bind]
    simp only [bind_map_left, map_bind, maskedImpl_run_touch, RelabelState.drawCell_run,
      OracleSpec.queryAll_cons, OracleSpec.queryAll_nil, simulateQ_bind, simulateQ_spec_query,
      simulateQ_pure, StateT.run_bind, StateT.run_pure, pure_bind, bind_assoc]
    refine evalDist_bind_congr_of_support _ _ _ fun w hw ↦ ?_
    rw [QueryImpl.withCaching_queryAll_uncached_append_singleton _ hw c]
  · rw [deferredImpl_run_read, bind_map_left, maskedImpl_apply_read]
    exact RelabelState.evalDist_drawCell_bind_maskedFill (.inr k) st cs f

/-! ## The masked game is dominated by the eager game until a conflict -/

/-- Every step of the masked game extends the state. -/
theorem le_of_mem_support_maskedImpl {t : (pub.withLabels X K R).Domain}
    {s : RelabelState pub X K R × Finset (X ⊕ K)} {z} (hz : z ∈ support ((G.maskedImpl t).run s)) :
    s.1 ≤ z.2.1 := by
  rcases t with ((n | t) | x) | (c | k)
  · rw [maskedImpl_run_unif, support_map] at hz
    obtain ⟨_, -, rfl⟩ := hz
    exact le_rfl
  · by_cases ht : ∃ k vs, G.childVals (RelabelState.mask s) k = some vs ∧ G.pt k vs = t
    · obtain ⟨k, vs, hk, rfl⟩ := ht
      rw [G.maskedImpl_run_pt hk, RelabelState.revealCell_run, Functor.map_map, support_map] at hz
      obtain ⟨w, hw, rfl⟩ := hz
      exact (RelabelState.le_and_cell_eq_of_mem_support_drawCell hw).1
    · rw [G.maskedImpl_run_pub_of_not_exists ht, support_map] at hz
      obtain ⟨w, hw, rfl⟩ := hz
      exact ⟨QueryImpl.withCaching_cache_le _ _ _ _ hw, le_rfl⟩
  · rw [maskedImpl_apply_derive, RelabelState.revealCell_run, support_map] at hz
    obtain ⟨w, hw, rfl⟩ := hz
    exact (RelabelState.le_and_cell_eq_of_mem_support_drawCell hw).1
  · rw [maskedImpl_run_touch, support_map] at hz
    obtain ⟨w, hw, rfl⟩ := hz
    exact (RelabelState.le_and_cell_eq_of_mem_support_drawCell hw).1
  · rw [maskedImpl_apply_read, RelabelState.revealCell_run, support_map] at hz
    obtain ⟨w, hw, rfl⟩ := hz
    exact (RelabelState.le_and_cell_eq_of_mem_support_drawCell hw).1

/-- A conflict persists along the masked game. -/
theorem preservesInv_conflict_maskedImpl :
    QueryImpl.PreservesInv G.maskedImpl fun s ↦ G.Conflict s.1 :=
  fun _ _ h _ hz ↦ h.mono G (G.le_of_mem_support_maskedImpl hz)

/-- The masked game, with the hidden cells forgotten, is dominated by the eager game until a
conflict: the two steps agree except at a public query at the point of a node whose children are
all drawn, some of them hidden, where the masked game answers from the public cache and so
creates a conflict. -/
theorem dominatedUntilBad_maskedImpl :
    QueryImpl.DominatedUntilBad G.maskedImpl G.eagerImpl Prod.fst (fun _ ↦ True)
      fun s ↦ G.Conflict s.1 := by
  intro t s _ _ Q
  have key (h : Prod.map id Prod.fst <$> (G.maskedImpl t).run s = (G.eagerImpl t).run s.1) :
      Pr{let z ← (G.maskedImpl t).run s}[Q (z.1, z.2.1) ∧ ¬G.Conflict z.2.1] ≤
        Pr{let z ← (G.eagerImpl t).run s.1}[Q z] := by
    rw [← h, prEvent_map]
    exact prEvent_mono _ _ _ fun _ h ↦ h.1
  rcases t with ((n | t) | x) | (c | k)
  · refine key ?_
    rw [maskedImpl_run_unif, eagerImpl_apply_inl, relabelImpl_run_unif, Functor.map_map]
    rfl
  · by_cases hr : ∃ k vs, G.childVals (RelabelState.mask s) k = some vs ∧ G.pt k vs = t
    · obtain ⟨k, vs, hk, rfl⟩ := hr
      refine key ?_
      rw [G.maskedImpl_run_pt hk, eagerImpl_apply_inl,
        G.relabelImpl_run_pt (G.childVals_mono (RelabelState.mask_le s) hk),
        RelabelState.revealCell_run, Functor.map_map, Functor.map_map]
      rfl
    · by_cases hf : ∃ k vs, G.childVals s.1 k = some vs ∧ G.pt k vs = t
      · obtain ⟨k, vs, hk, rfl⟩ := hf
        refine le_of_eq_of_le (prEvent_eq_zero_of_forall_mem_support _ _ fun z hz hz' ↦ hz'.2 ?_)
          zero_le
        rw [G.maskedImpl_run_pub_of_not_exists hr, support_map] at hz
        obtain ⟨w, hw, rfl⟩ := hz
        exact ⟨k, vs, G.childVals_mono (st := s.1) (st' := (w.2, s.1.2))
          ⟨QueryImpl.withCaching_cache_le _ _ _ _ hw, le_rfl⟩ hk,
          by rw [QueryImpl.withCaching_run_caches _ _ _ _ hw]; rfl⟩
      · refine key ?_
        rw [G.maskedImpl_run_pub_of_not_exists hr, eagerImpl_apply_inl,
          G.relabelImpl_run_pub_of_not_exists hf, Functor.map_map]
        rfl
  · refine key ?_
    rw [maskedImpl_apply_derive, RelabelState.revealCell_run, eagerImpl_apply_inl,
      relabelImpl_apply_inr, Functor.map_map]
    simp only [Prod.map_apply, id_eq, Prod.mk.eta, id_map']
  · refine key ?_
    rw [maskedImpl_run_touch, eagerImpl_apply_inr, Functor.map_map]
    simp only [Prod.map_apply, id_eq, RelabelState.labelImpl, StateT.run_map]
  · refine key ?_
    rw [maskedImpl_apply_read, RelabelState.revealCell_run, eagerImpl_apply_inr,
      Functor.map_map]
    simp only [Prod.map_apply, id_eq, Prod.mk.eta, id_map', RelabelState.labelImpl]

/-! ## Deferring touches -/

/-- **Deferred decision for touched cells.** From any state of the deferred game, its run
followed by the end fill has the distribution of the masked game run from the masked end fill of
that state, with the hidden cells forgotten. -/
theorem prEvent_deferredImpl_endFill_eq_maskedFill_bind_maskedImpl {α : Type}
    (oa : OracleComp (pub.withLabels X K R) α) (s : RelabelState pub X K R × List (X ⊕ K))
    (P : α × RelabelState pub X K R → Prop) :
    Pr{let z ← (simulateQ G.deferredImpl oa).run s
       let st ← RelabelState.endFill z.2}[P (z.1, st)] =
      Pr{let s' ← RelabelState.maskedFill s
         let z ← (simulateQ G.maskedImpl oa).run s'}[P (z.1, z.2.1)] := by
  have h := G.intertwines_maskedFill.evalDist_simulateQ_run oa s
    fun a s' ↦ (pure (P (a, s'.1)) : ProbComp Prop)
  simp only [RelabelState.maskedFill, bind_map_left] at h ⊢
  rw [h]

/-- **Deferred decision for touched cells, with nothing pending.** From a state with no pending
cell, the deferred game followed by the end fill has the distribution of the masked game from the
same state with nothing hidden, with the hidden cells forgotten. -/
theorem prEvent_deferredImpl_endFill_eq_maskedImpl {α : Type}
    (oa : OracleComp (pub.withLabels X K R) α) (st : RelabelState pub X K R)
    (P : α × RelabelState pub X K R → Prop) :
    Pr{let z ← (simulateQ G.deferredImpl oa).run (st, [])
       let st' ← RelabelState.endFill z.2}[P (z.1, st')] =
      Pr{let z ← (simulateQ G.maskedImpl oa).run (st, ∅)}[P (z.1, z.2.1)] := by
  rw [prEvent_deferredImpl_endFill_eq_maskedFill_bind_maskedImpl, RelabelState.maskedFill_nil,
    pure_bind]

/-- An event of the eager game is at most the same event of the masked game, with the hidden
cells forgotten, or a conflict. -/
theorem prEvent_eagerImpl_le_maskedImpl {α : Type} (oa : OracleComp (pub.withLabels X K R) α)
    (s : RelabelState pub X K R × Finset (X ⊕ K)) (P : α × RelabelState pub X K R → Prop) :
    Pr{let z ← (simulateQ G.eagerImpl oa).run s.1}[P z] ≤
      Pr{let z ← (simulateQ G.maskedImpl oa).run s}[P (z.1, z.2.1) ∨ G.Conflict z.2.1] :=
  G.dominatedUntilBad_maskedImpl.prEvent_simulateQ_run_le_map_or_bad
    (QueryImpl.PreservesInv.trivial _) G.preservesInv_conflict_maskedImpl oa s trivial P

/-- **Touch deferral.** From a state with no pending cell, an event of the eager game is at most
the same event of the deferred game after the end fill, or a conflict. -/
theorem prEvent_eagerImpl_le_deferredImpl {α : Type} (oa : OracleComp (pub.withLabels X K R) α)
    (st : RelabelState pub X K R) (P : α × RelabelState pub X K R → Prop) :
    Pr{let z ← (simulateQ G.eagerImpl oa).run st}[P z] ≤
      Pr{let z ← (simulateQ G.deferredImpl oa).run (st, [])
         let st' ← RelabelState.endFill z.2}[P (z.1, st') ∨ G.Conflict st'] :=
  (G.prEvent_eagerImpl_le_maskedImpl oa (st, ∅) P).trans_eq
    (G.prEvent_deferredImpl_endFill_eq_maskedImpl oa st fun z ↦ P z ∨ G.Conflict z.2).symm

/-- **Touch deferral from the empty state.** An event of the eager game is at most the same event
of the deferred game after the end fill, or a conflict. -/
theorem prEvent_eagerImpl_le_deferredImpl_empty {α : Type}
    (oa : OracleComp (pub.withLabels X K R) α) (P : α × RelabelState pub X K R → Prop) :
    Pr{let z ← (simulateQ G.eagerImpl oa).run (∅, ∅)}[P z] ≤
      Pr{let z ← (simulateQ G.deferredImpl oa).run ((∅, ∅), [])
         let st ← RelabelState.endFill z.2}[P (z.1, st) ∨ G.Conflict st] :=
  G.prEvent_eagerImpl_le_deferredImpl oa (∅, ∅) P

end CanonicalGraph
