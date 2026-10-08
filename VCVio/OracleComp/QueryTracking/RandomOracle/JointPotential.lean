/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module

public import VCVio.OracleComp.QueryTracking.RandomOracle.Defer
public import VCVio.OracleComp.QueryTracking.RandomOracle.FreshAnswer
import ToMathlib.Data.List.MapM
import VCVio.OracleComp.Constructions.SampleableType.NativeMeasure

/-!
# The joint potential of conflicts and target collisions in the deferred game

Fix a canonical graph `G` and a key map `nk : G.NodeKeys`. Two hazards of a relabelled state
involve the public entries at node keys: a conflict `CanonicalGraph.Conflict` (a node whose
children are all drawn has its point, at their values, in the public cache) and a target
collision `CanonicalGraph.NodeKeys.TCHazard` (a public entry at a node's key equals the node's
drawn label). Each public entry at a node key can fire each hazard at most once, so both are
charged by the potential `CanonicalGraph.NodeKeys.potential`, the number of entries at node keys
whose node has all children drawn plus the number whose node has its label drawn, over `|R|`. It
is at most `2 · #keyEntries / |R|`.

* A draw of an undrawn cell fires a conflict only at entries of the nodes it completes, and a
  target collision only at entries of the node whose label it is; each such entry pins at most
  one drawn value, and each enters the potential when the cell is drawn.
* A fresh public answer fires no conflict, and fires a target collision with probability `1/|R|`
  exactly when its point is at the key of a node whose label is already drawn; that entry enters
  the potential at once.
* A touch in the deferred game draws nothing and changes no hazard.

So the deferred game `CanonicalGraph.deferredImpl` and the cell oracle `RelabelState.cellImpl`,
which runs the end fill, both charge the two hazards to the potential
(`CanonicalGraph.NodeKeys.isPotentialStep_deferredImpl`,
`CanonicalGraph.NodeKeys.isPotentialStep_cellImpl`). A third phase draws a value `s ← ms` the
program never reads, such as a secret, after the end fill; a hazard `H s` of the final public
cache with probability at most `c` at each cache is charged `c` on top of the potential
(`OracleComp.prEvent_bind_draw_and_le_of_potential`). One budget `B` covers the three phases.

## Main statements

- `CanonicalGraph.NodeKeys.prEvent_deferredFillDraw_and_le`: the deferred game, the end fill and
  the draw fire a conflict, a target collision or the hazard, with
  `2 · #keyEntries / |R| + c ≤ B` at the final state, with probability at most `B`.
- `CanonicalGraph.NodeKeys.prEvent_deferredFillDraw_le_of_budget`: the same bound without the
  truncation, when `2 · #keyEntries / |R| + c ≤ B` holds at the end of every deferred run.
- `CanonicalGraph.mem_support_deferredFillDraw_iff`: a point of the three phases is a deferred run,
  an end fill of its final state and a draw.
-/

public section

open OracleComp OracleSpec MeasureTheory
open scoped ENNReal

namespace CanonicalGraph

variable {ι : Type} {pub : OracleSpec ι} {X K R : Type}

section DeferredFillDraw

variable (G : CanonicalGraph pub X K R) [DecidableEq ι] [DecidableEq X] [DecidableEq K]
  [SampleableType R] [∀ t, SampleableType (pub.Range t)]

/-- The deferred game from the empty state, followed by the end fill and an independent draw
`s ← ms`: the deferred run's output and final state, the filled state, and the draw. -/
@[expose] noncomputable def deferredFillDraw {S α : Type} (ms : ProbComp S)
    (oa : OracleComp (pub.withLabels X K R) α) :
    ProbComp ((α × RelabelState pub X K R × List (X ⊕ K)) × RelabelState pub X K R × S) := do
  let z ← (simulateQ G.deferredImpl oa).run ((∅, ∅), [])
  let st ← RelabelState.endFill z.2
  let s ← ms
  return (z, st, s)

/-- A point of `deferredFillDraw` is a run of the deferred game from the empty state, an end fill
of its final state, and a draw. -/
theorem mem_support_deferredFillDraw_iff {S α : Type} {ms : ProbComp S}
    {oa : OracleComp (pub.withLabels X K R) α}
    {w : (α × RelabelState pub X K R × List (X ⊕ K)) × RelabelState pub X K R × S} :
    w ∈ support (G.deferredFillDraw ms oa) ↔
      w.1 ∈ support ((simulateQ G.deferredImpl oa).run ((∅, ∅), [])) ∧
        w.2.1 ∈ support (RelabelState.endFill w.1.2) ∧ w.2.2 ∈ support ms := by
  simp only [deferredFillDraw, mem_support_bind_iff, support_pure, Set.mem_singleton_iff]
  constructor
  · rintro ⟨z, hz, st, hst, s, hs, rfl⟩
    exact ⟨hz, hst, hs⟩
  · exact fun ⟨hz, hst, hs⟩ ↦ ⟨w.1, hz, w.2.1, hst, w.2.2, hs, rfl⟩

end DeferredFillDraw

namespace NodeKeys

variable {G : CanonicalGraph pub X K R}

/-! ## The potential -/

section Potential

variable (nk : G.NodeKeys)

/-- The public entries at the key of a node whose children are all drawn. -/
def completeEntries (st : RelabelState pub X K R) : Set ι :=
  {t | (st.1 t).isSome ∧ ∃ k, nk.node t = some k ∧ ∀ c ∈ G.ch k, (st.2 c).isSome}

/-- The public entries at the key of a node whose label is drawn. -/
def labelledEntries (st : RelabelState pub X K R) : Set ι :=
  {t | (st.1 t).isSome ∧ ∃ k, nk.node t = some k ∧ (st.2 (.inr k)).isSome}

/-- The joint potential of conflicts and target collisions: the public entries at the key of a
node whose children are all drawn, plus those at the key of a node whose label is drawn, over
`|R|`. -/
noncomputable def potential (st : RelabelState pub X K R) : ℝ≥0∞ :=
  (((nk.completeEntries st).encard + (nk.labelledEntries st).encard : ℕ∞) : ℝ≥0∞) / Nat.card R

variable {nk}

theorem completeEntries_mono : Monotone nk.completeEntries := fun _ _ hle _ ⟨hC, k, hk, hall⟩ ↦
  ⟨QueryCache.isSome_mono hle.1 hC, k, hk, fun c hc ↦ QueryCache.isSome_mono hle.2 (hall c hc)⟩

theorem labelledEntries_mono : Monotone nk.labelledEntries := fun _ _ hle _ ⟨hC, k, hk, hl⟩ ↦
  ⟨QueryCache.isSome_mono hle.1 hC, k, hk, QueryCache.isSome_mono hle.2 hl⟩

theorem potential_mono : Monotone nk.potential := fun _ _ hle ↦ by
  unfold potential
  gcongr
  · exact completeEntries_mono hle
  · exact labelledEntries_mono hle

/-- Each public entry at a node key enters the potential at most twice. -/
theorem potential_le_two_mul (st : RelabelState pub X K R) :
    nk.potential st ≤ 2 * ((nk.keyEntries st.1).encard : ℝ≥0∞) / Nat.card R := by
  unfold potential
  gcongr
  rw [ENat.toENNReal_add, two_mul]
  have h1 : nk.completeEntries st ⊆ nk.keyEntries st.1 := by
    rintro t ⟨hC, k, hk, -⟩
    exact ⟨hC, by rw [hk]; rfl⟩
  have h2 : nk.labelledEntries st ⊆ nk.keyEntries st.1 := by
    rintro t ⟨hC, k, hk, -⟩
    exact ⟨hC, by rw [hk]; rfl⟩
  exact add_le_add (ENat.toENNReal_le.2 (Set.encard_le_encard h1))
    (ENat.toENNReal_le.2 (Set.encard_le_encard h2))

@[simp] theorem potential_empty : nk.potential ((∅, ∅) : RelabelState pub X K R) = 0 := by
  simp [potential, completeEntries, labelledEntries]

end Potential

/-! ## A cell draw is charged by the potential -/

section CellDraw

variable {nk : G.NodeKeys}

/-- A relation from `A` into `T` that relates every element of `A` to some element of `T`, and
no two elements of `A` to one element, bounds `A.encard` by `T.encard`. -/
private theorem encard_le_of_rel {α β : Type} {A : Set α} {T : Set β} (r : α → β → Prop)
    (h1 : ∀ a ∈ A, ∃ b ∈ T, r a b) (h2 : ∀ a ∈ A, ∀ a' ∈ A, ∀ b, r a b → r a' b → a = a') :
    A.encard ≤ T.encard := by
  rcases A.eq_empty_or_nonempty with rfl | ⟨a₀, ha₀⟩
  · rw [Set.encard_empty]
    exact zero_le
  have : Nonempty β := ⟨(h1 a₀ ha₀).choose⟩
  choose! f hfT hfr using h1
  exact Set.encard_le_encard_of_injOn hfT fun a ha a' ha' he ↦
    h2 a ha a' ha' _ (hfr a ha) (he ▸ hfr a' ha')

variable [DecidableEq X] [DecidableEq K]

/-- The public entries at the key of a node whose children are all drawn once `c` is. -/
private def completeEntriesAfter (st : RelabelState pub X K R) (c : X ⊕ K) : Set ι :=
  {t | (st.1 t).isSome ∧ ∃ k, nk.node t = some k ∧ ∀ c' ∈ G.ch k, c' = c ∨ (st.2 c').isSome}

/-- The public entries at the key of a node whose label is drawn once `c` is. -/
private def labelledEntriesAfter (st : RelabelState pub X K R) (c : X ⊕ K) : Set ι :=
  {t | (st.1 t).isSome ∧ ∃ k, nk.node t = some k ∧
    ((Sum.inr k : X ⊕ K) = c ∨ (st.2 (.inr k)).isSome)}

private theorem completeEntries_cacheQuery (st : RelabelState pub X K R) (c : X ⊕ K) (u : R) :
    nk.completeEntries (st.1, st.2.cacheQuery c u) = completeEntriesAfter (nk := nk) st c := by
  ext t
  simp only [completeEntries, completeEntriesAfter, Set.mem_ofPred_eq,
    QueryCache.isSome_cacheQuery_apply_iff]

private theorem labelledEntries_cacheQuery (st : RelabelState pub X K R) (c : X ⊕ K) (u : R) :
    nk.labelledEntries (st.1, st.2.cacheQuery c u) = labelledEntriesAfter (nk := nk) st c := by
  ext t
  simp only [labelledEntries, labelledEntriesAfter, Set.mem_ofPred_eq,
    QueryCache.isSome_cacheQuery_apply_iff]

/-- Drawing an undrawn cell adds to the potential exactly the entries it newly charges. -/
private theorem potential_cacheQuery_cell {st : RelabelState pub X K R} {c : X ⊕ K}
    (hc : st.2 c = none) (u : R) :
    (((completeEntriesAfter (nk := nk) st c \ nk.completeEntries st).encard +
        (labelledEntriesAfter (nk := nk) st c \ nk.labelledEntries st).encard : ℕ∞) :
        ℝ≥0∞) / Nat.card R + nk.potential st = nk.potential (st.1, st.2.cacheQuery c u) := by
  have hle : st ≤ (st.1, st.2.cacheQuery c u) := ⟨le_rfl, QueryCache.le_cacheQuery _ hc⟩
  have e1 := Set.encard_sdiff_add_encard_of_subset
    ((completeEntries_mono (nk := nk) hle).trans (completeEntries_cacheQuery st c u).le)
  have e2 := Set.encard_sdiff_add_encard_of_subset
    ((labelledEntries_mono (nk := nk) hle).trans (labelledEntries_cacheQuery st c u).le)
  rw [potential, potential, completeEntries_cacheQuery, labelledEntries_cacheQuery,
    ← ENNReal.add_div, ← ENat.toENNReal_add, ← e1, ← e2]
  congr 2
  ring

/-- A drawn value that completes a node at a point the public cache holds is charged to that
point's newly charged entry, and each entry pins the drawn value. -/
private theorem encard_conflict_le {st : RelabelState pub X K R}
    (hst : ¬(G.Conflict st ∨ nk.TCHazard st)) {c : X ⊕ K} (hc : st.2 c = none) :
    {u : R | G.Conflict (st.1, st.2.cacheQuery c u)}.encard ≤
      (completeEntriesAfter (nk := nk) st c \ nk.completeEntries st).encard := by
  refine encard_le_of_rel (fun u t ↦ ∃ k vs, G.childVals (st.1, st.2.cacheQuery c u) k = some vs ∧
    G.pt k vs = t ∧ (st.1 t).isSome) ?_ ?_
  · rintro u ⟨k, vs, hk, hC⟩
    have hlen := G.length_eq_of_childVals_eq_some hk
    refine ⟨G.pt k vs, ⟨⟨hC, k, nk.node_pt hlen, fun c' hc' ↦ ?_⟩, ?_⟩, k, vs, hk, rfl, hC⟩
    · exact (QueryCache.isSome_cacheQuery_apply_iff _ _).1
        (G.isSome_childVals_iff.1 (by rw [hk]; rfl) c' hc')
    · rintro ⟨-, k', hk', hall⟩
      obtain rfl : k = k' := Option.some_inj.1 ((nk.node_pt hlen).symm.trans hk')
      obtain ⟨vs', hvs'⟩ := Option.isSome_iff_exists.1 (G.isSome_childVals_iff.2 hall)
      have h := G.childVals_mono
        (⟨le_rfl, QueryCache.le_cacheQuery _ hc⟩ : st ≤ (st.1, st.2.cacheQuery c u)) hvs'
      rw [hk] at h
      cases h
      exact hst (Or.inl ⟨k, _, hvs', hC⟩)
  · rintro u - u' - t ⟨k, vs, hk, rfl, hC⟩ ⟨k', vs', hk', hpt, -⟩
    obtain ⟨rfl, rfl⟩ := G.eq_of_childVals_of_pt_eq hk hk' hpt.symm
    have hcmem : c ∈ G.ch k := by
      by_contra hcn
      refine hst (Or.inl ⟨k, vs, (G.childVals_congr fun c' hc' ↦ ?_).trans hk, hC⟩)
      exact (QueryCache.cacheQuery_of_ne _ _ fun h : c' = c ↦ hcn (h ▸ hc')).symm
    rw [G.childVals_eq_some_iff, List.forall₂_apply_eq_some_iff] at hk hk'
    simpa only [QueryCache.cacheQuery_self, Option.some_inj] using
      List.map_inj_left.1 (hk.trans hk'.symm) c hcmem

/-- A drawn label equal to a public entry at its node's key is charged to that entry, newly
charged, and each entry pins the drawn value. -/
private theorem encard_tcHazard_le {st : RelabelState pub X K R}
    (hst : ¬(G.Conflict st ∨ nk.TCHazard st)) {c : X ⊕ K} (hc : st.2 c = none) :
    {u : R | nk.TCHazard (st.1, st.2.cacheQuery c u)}.encard ≤
      (labelledEntriesAfter (nk := nk) st c \ nk.labelledEntries st).encard := by
  refine encard_le_of_rel (fun u t ↦ ∃ k, ∃ h : nk.node t = some k, (Sum.inr k : X ⊕ K) = c ∧
    st.1 t = some (cast (nk.range_eq h).symm u)) ?_ ?_
  · rintro u ⟨t, k, ℓ, h, hℓ, hC⟩
    have hkc : (Sum.inr k : X ⊕ K) = c := by
      by_contra hne
      exact hst (Or.inr ⟨t, k, ℓ, h, by rwa [QueryCache.cacheQuery_of_ne _ _ hne] at hℓ, hC⟩)
    subst hkc
    simp only [QueryCache.cacheQuery_self, Option.some_inj] at hℓ
    subst hℓ
    refine ⟨t, ⟨⟨by rw [hC]; rfl, k, h, Or.inl rfl⟩, ?_⟩, k, h, rfl, hC⟩
    rintro ⟨-, k', hk', hl'⟩
    rw [h] at hk'
    cases hk'
    rw [hc] at hl'
    exact absurd hl' Bool.false_ne_true
  · rintro u - u' - t ⟨k, h, -, hC⟩ ⟨k', h', -, hC'⟩
    obtain rfl : k = k' := Option.some_inj.1 (h.symm.trans h')
    rw [hC] at hC'
    exact (cast_inj _).1 (Option.some_inj.1 hC')

/-- Drawing an undrawn cell out of a state with neither hazard fires one with probability at
most the weight it adds to the potential. -/
private theorem exists_cell_charge [SampleableType R] {st : RelabelState pub X K R}
    (hst : ¬(G.Conflict st ∨ nk.TCHazard st)) {c : X ⊕ K} (hc : st.2 c = none) :
    ∃ w : ℝ≥0∞, Pr{let u ← $ᵗ R}[G.Conflict (st.1, st.2.cacheQuery c u) ∨
        nk.TCHazard (st.1, st.2.cacheQuery c u)] ≤ w ∧
      ∀ u, w + nk.potential st ≤ nk.potential (st.1, st.2.cacheQuery c u) := by
  refine ⟨_, ?_, fun u ↦ (potential_cacheQuery_cell hc u).le⟩
  let _ : MeasurableSpace R := ⊤
  rw [prEvent_eq_evalDist_of_discrete]
  refine (SampleableType.evalDist_uniformSample_le_encard_div _).trans ?_
  gcongr
  rw [Set.ofPred_or]
  exact (Set.encard_union_le _ _).trans (add_le_add (encard_conflict_le hst hc)
    (encard_tcHazard_le hst hc))

end CellDraw

/-! ## A fresh public answer is charged by the potential -/

section PublicMiss

variable {nk : G.NodeKeys} [DecidableEq ι]

private theorem not_conflict_cacheQuery_pub {st : RelabelState pub X K R}
    (hst : ¬(G.Conflict st ∨ nk.TCHazard st)) {t : ι}
    (hn : ¬∃ k vs, G.childVals st k = some vs ∧ G.pt k vs = t) (u : pub.Range t) :
    ¬G.Conflict (st.1.cacheQuery t u, st.2) := by
  rintro ⟨k, vs, hk, hC⟩
  have hk' : G.childVals st k = some vs := by
    rw [G.childVals_eq_some_iff] at hk ⊢
    exact hk
  by_cases hpt : G.pt k vs = t
  · exact hn ⟨k, vs, hk', hpt⟩
  · exact hst (Or.inl ⟨k, vs, hk', by rwa [QueryCache.cacheQuery_of_ne _ _ hpt] at hC⟩)

private theorem tcHazard_cacheQuery_pub {st : RelabelState pub X K R}
    (hst : ¬(G.Conflict st ∨ nk.TCHazard st)) {t : ι} (u : pub.Range t)
    (h : nk.TCHazard (st.1.cacheQuery t u, st.2)) :
    ∃ k ℓ, ∃ hk : nk.node t = some k, st.2 (.inr k) = some ℓ ∧
      (st.1.cacheQuery t u) t = some (cast (nk.range_eq hk).symm ℓ) := by
  obtain ⟨t', k, ℓ, hk, hℓ, hC⟩ := h
  by_cases ht : t' = t
  · subst ht
    exact ⟨k, ℓ, hk, hℓ, hC⟩
  · exact absurd (Or.inr ⟨t', k, ℓ, hk, hℓ, by rwa [QueryCache.cacheQuery_of_ne _ _ ht] at hC⟩)
      hst

/-- A fresh public answer at a point that is no node's point at its drawn children values, out
of a state with neither hazard, fires one with probability at most the weight it adds to the
potential: `1/|R|` if the point is at the key of a node whose label is drawn, and `0` otherwise. -/
private theorem exists_pub_charge [∀ t, SampleableType (pub.Range t)]
    {st : RelabelState pub X K R} (hst : ¬(G.Conflict st ∨ nk.TCHazard st)) {t : ι}
    (ht : st.1 t = none) (hn : ¬∃ k vs, G.childVals st k = some vs ∧ G.pt k vs = t) :
    ∃ w : ℝ≥0∞, Pr{let u ← $ᵗ pub.Range t}[G.Conflict (st.1.cacheQuery t u, st.2) ∨
        nk.TCHazard (st.1.cacheQuery t u, st.2)] ≤ w ∧
      ∀ u, w + nk.potential st ≤ nk.potential (st.1.cacheQuery t u, st.2) := by
  have hle : ∀ u : pub.Range t, st ≤ (st.1.cacheQuery t u, st.2) :=
    fun u ↦ ⟨QueryCache.le_cacheQuery _ ht, le_rfl⟩
  let _ : MeasurableSpace (pub.Range t) := ⊤
  by_cases hT : ∃ k ℓ, nk.node t = some k ∧ st.2 (.inr k) = some ℓ
  · obtain ⟨k, ℓ, hk, hℓ⟩ := hT
    refine ⟨1 / Nat.card R, ?_, fun u ↦ ?_⟩
    · have hsub : {u | G.Conflict (st.1.cacheQuery t u, st.2) ∨
          nk.TCHazard (st.1.cacheQuery t u, st.2)} ⊆ {cast (nk.range_eq hk).symm ℓ} := by
        rintro u (hc | htc)
        · exact absurd hc (not_conflict_cacheQuery_pub hst hn u)
        · obtain ⟨k', ℓ', hk', hℓ', hC⟩ := tcHazard_cacheQuery_pub hst u htc
          obtain rfl : k = k' := Option.some_inj.1 (hk.symm.trans hk')
          rw [hℓ] at hℓ'
          cases hℓ'
          rw [QueryCache.cacheQuery_self] at hC
          exact Option.some_inj.1 hC
      rw [prEvent_eq_evalDist_of_discrete]
      refine (measure_mono hsub).trans ((SampleableType.evalDist_uniformSample_le_encard_div
        _).trans ?_)
      rw [Set.encard_singleton, Nat.card_congr (Equiv.cast (nk.range_eq hk)),
        ENat.toENNReal_one]
    · have hins : insert t (nk.labelledEntries st) ⊆
          nk.labelledEntries (st.1.cacheQuery t u, st.2) :=
        Set.insert_subset ⟨by rw [QueryCache.cacheQuery_self]; rfl, k, hk, by rw [hℓ]; rfl⟩
          (labelledEntries_mono (hle u))
      have hnot : t ∉ nk.labelledEntries st := fun h ↦ by
        rw [labelledEntries, Set.mem_ofPred_eq, ht] at h
        exact Bool.false_ne_true h.1
      have h1 := Set.encard_le_encard hins
      rw [Set.encard_insert_of_notMem hnot] at h1
      have h2 := Set.encard_le_encard (completeEntries_mono (nk := nk) (hle u))
      rw [potential, potential, ← ENNReal.add_div]
      gcongr
      rw [show (1 : ℝ≥0∞) = ((1 : ℕ∞) : ℝ≥0∞) from ENat.toENNReal_one.symm, ← ENat.toENNReal_add,
        ENat.toENNReal_le]
      calc 1 + ((nk.completeEntries st).encard + (nk.labelledEntries st).encard)
          = (nk.completeEntries st).encard + ((nk.labelledEntries st).encard + 1) := by ring
        _ ≤ _ := add_le_add h2 h1
  · refine ⟨0, le_of_eq (prEvent_eq_zero_of_forall_not _ _ fun u hu ↦ ?_),
      fun u ↦ by rw [zero_add]; exact potential_mono (hle u)⟩
    rcases hu with hc | htc
    · exact not_conflict_cacheQuery_pub hst hn u hc
    · obtain ⟨k, ℓ, hk, hℓ, -⟩ := tcHazard_cacheQuery_pub hst u htc
      exact hT ⟨k, ℓ, hk, hℓ⟩

end PublicMiss

/-! ## The deferred game and the cell oracle charge the potential -/

section Steps

variable (nk : G.NodeKeys) [DecidableEq X] [DecidableEq K] [SampleableType R]

/-- A cell draw, with its result mapped by `f` and its state wrapped by `wrap`, is deterministic
when the cell is drawn and otherwise charged by the potential of the state that `proj` reads back
out of the wrapper. -/
private theorem drawCell_step {β σ : Type} (f : R → β) (g : β → R) (hgf : ∀ u, g (f u) = u)
    (wrap : RelabelState pub X K R → σ) (proj : σ → RelabelState pub X K R)
    (hproj : ∀ st, proj (wrap st) = st) {st : RelabelState pub X K R}
    (hst : ¬(G.Conflict st ∨ nk.TCHazard st)) (c : X ⊕ K) :
    (∃ a s', (fun z : R × RelabelState pub X K R ↦ (f z.1, wrap z.2)) <$>
        (RelabelState.drawCell c).run st = pure (a, s') ∧
        ¬(G.Conflict (proj s') ∨ nk.TCHazard (proj s'))) ∨
    (∃ (samp : ProbComp β) (upd : β → σ) (w : ℝ≥0∞),
      (fun z : R × RelabelState pub X K R ↦ (f z.1, wrap z.2)) <$>
        (RelabelState.drawCell c).run st = (fun b ↦ (b, upd b)) <$> samp ∧
      Pr{let b ← samp}[G.Conflict (proj (upd b)) ∨ nk.TCHazard (proj (upd b))] ≤ w ∧
      ∀ b, w + nk.potential st ≤ nk.potential (proj (upd b))) := by
  cases hc : st.2 c with
  | some v =>
    exact Or.inl ⟨f v, wrap st, by rw [RelabelState.drawCell_run_of_cell_eq_some hc, map_pure],
      by rwa [hproj]⟩
  | none =>
    obtain ⟨w, hw, hpot⟩ := exists_cell_charge hst hc
    refine Or.inr ⟨f <$> ($ᵗ R), fun b ↦ wrap (st.1, st.2.cacheQuery c (g b)), w, ?_, ?_,
      fun b ↦ by rw [hproj]; exact hpot (g b)⟩
    · rw [RelabelState.drawCell_run_of_cell_eq_none hc, Functor.map_map, Functor.map_map]
      simp only [hgf]
    · rw [prEvent_map]
      simpa only [hgf, hproj] using hw

/-- The cell oracle charges conflicts and target collisions at node keys to the joint
potential. -/
theorem isPotentialStep_cellImpl :
    IsPotentialStep (RelabelState.cellImpl (pub := pub) (X := X) (K := K) (R := R))
      (fun st ↦ G.Conflict st ∨ nk.TCHazard st) nk.potential where
  mono c _ _ hz := by
    rw [RelabelState.cellImpl_apply] at hz
    exact potential_mono (RelabelState.le_and_cell_eq_of_mem_support_drawCell hz).1
  step c st hst := by
    simpa only [RelabelState.cellImpl_apply, id_eq, Prod.mk.eta, id_map'] using
      drawCell_step nk id id (fun _ ↦ rfl) id id (fun _ ↦ rfl) hst c

variable [DecidableEq ι] [∀ t, SampleableType (pub.Range t)]

/-- The deferred game charges conflicts and target collisions at node keys to the joint
potential. -/
theorem isPotentialStep_deferredImpl :
    IsPotentialStep G.deferredImpl (fun s ↦ G.Conflict s.1 ∨ nk.TCHazard s.1)
      (fun s ↦ nk.potential s.1) where
  mono _ _ _ hz := potential_mono (G.le_of_mem_support_deferredImpl hz)
  step := by
    rintro (((n | t) | x) | (c | k)) ⟨st, cs⟩ hst
    · refine Or.inr ⟨(unifSpec.query n : ProbComp _), fun _ ↦ (st, cs), 0, ?_,
        le_of_eq (prEvent_eq_zero_of_forall_not _ _ fun _ ↦ hst), fun _ ↦ by rw [zero_add]⟩
      rw [G.deferredImpl_run_inl, relabelImpl_run_unif, Functor.map_map]
      rfl
    · by_cases h : ∃ k vs, G.childVals st k = some vs ∧ G.pt k vs = t
      · obtain ⟨k, vs, hk, rfl⟩ := h
        rw [G.deferredImpl_run_inl, G.relabelImpl_run_pt hk, Functor.map_map]
        exact drawCell_step nk (cast (G.range_eq k vs).symm) (cast (G.range_eq k vs))
          (fun u ↦ cast_cast _ _ u) (·, cs) Prod.fst (fun _ ↦ rfl) hst (.inr k)
      · cases hC : st.1 t with
        | some v =>
          refine Or.inl ⟨v, (st, cs), ?_, hst⟩
          rw [G.deferredImpl_run_inl, G.relabelImpl_run_pub_of_not_exists h, randomOracle.run_eq]
          simp only [hC, map_pure]
        | none =>
          obtain ⟨w, hw, hpot⟩ := exists_pub_charge hst hC h
          refine Or.inr ⟨$ᵗ pub.Range t, fun u ↦ ((st.1.cacheQuery t u, st.2), cs), w, ?_, hw,
            hpot⟩
          rw [G.deferredImpl_run_inl, G.relabelImpl_run_pub_of_not_exists h,
            randomOracle.run_eq]
          simp only [hC, bind_pure_comp, Functor.map_map]
          rfl
    · rw [G.deferredImpl_run_inl, relabelImpl_apply_inr]
      exact drawCell_step nk id id (fun _ ↦ rfl) (·, cs) Prod.fst (fun _ ↦ rfl) hst (.inl x)
    · exact Or.inl ⟨(), (st, cs ++ [c]), G.deferredImpl_run_touch c _, hst⟩
    · rw [G.deferredImpl_run_read]
      exact drawCell_step nk id id (fun _ ↦ rfl) (·, cs) Prod.fst (fun _ ↦ rfl) hst (.inr k)

end Steps

/-! ## Three phases -/

section ThreePhase

variable (nk : G.NodeKeys) [DecidableEq ι] [DecidableEq X] [DecidableEq K] [SampleableType R]
  [∀ t, SampleableType (pub.Range t)]

/-- **The joint potential over three phases.** The deferred game from the empty state, the end
fill, and an independent draw `s ← ms` whose hazard `H s` fires at each public cache `C` with
probability at most `c C`: a conflict, a target collision at a node key, or the hazard of the
final public cache, with `2 · #keyEntries / |R| + c ≤ B` at the final public cache, has
probability at most `B`. -/
theorem prEvent_deferredFillDraw_and_le {S α : Type} (ms : ProbComp S)
    (H : S → pub.QueryCache → Prop) (c : pub.QueryCache → ℝ≥0∞)
    (hH : ∀ C, Pr{let s ← ms}[H s C] ≤ c C) (oa : OracleComp (pub.withLabels X K R) α)
    (B : ℝ≥0∞) (hB : B ≠ ⊤) :
    Pr{let w ← G.deferredFillDraw ms oa}[
      (G.Conflict w.2.1 ∨ nk.TCHazard w.2.1 ∨ H w.2.2 w.2.1.1) ∧
        2 * ((nk.keyEntries w.2.1.1).encard : ℝ≥0∞) / Nat.card R + c w.2.1.1 ≤ B] ≤ B := by
  let fillDraw (z : α × RelabelState pub X K R × List (X ⊕ K)) :
      ProbComp ((α × RelabelState pub X K R × List (X ⊕ K)) × RelabelState pub X K R × S) := do
    let st ← RelabelState.endFill z.2
    let s ← ms
    return (z, st, s)
  have hgmono : ∀ z, ∀ y ∈ support (fillDraw z),
      nk.potential z.2.1 ≤ nk.potential y.2.1 + c y.2.1.1 := by
    intro z y hy
    simp only [fillDraw, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hy
    obtain ⟨st, hst, s, -, rfl⟩ := hy
    exact (potential_mono (RelabelState.le_of_mem_support_endFill hst)).trans le_self_add
  have hg : ∀ z : α × RelabelState pub X K R × List (X ⊕ K),
      ¬(G.Conflict z.2.1 ∨ nk.TCHazard z.2.1) →
      Pr{let y ← fillDraw z}[((G.Conflict y.2.1 ∨ nk.TCHazard y.2.1) ∨ H y.2.2 y.2.1.1) ∧
        nk.potential y.2.1 + c y.2.1.1 ≤ B] ≤ B - nk.potential z.2.1 := by
    intro z hz
    have key := prEvent_bind_draw_and_le_of_potential (nk.isPotentialStep_cellImpl (pub := pub))
      ms (fun s st ↦ H s st.1) (fun st ↦ c st.1) (fun st ↦ hH st.1) B hB
      (((X ⊕ K) →ₒ R).queryAll z.2.2) z.2.1 hz
    simpa only [fillDraw, RelabelState.endFill_eq_simulateQ_cellImpl, bind_assoc, bind_map_left,
      pure_bind] using key
  have h1 := prEvent_bind_and_le_of_potential nk.isPotentialStep_deferredImpl fillDraw
    (fun y ↦ (G.Conflict y.2.1 ∨ nk.TCHazard y.2.1) ∨ H y.2.2 y.2.1.1)
    (fun y ↦ nk.potential y.2.1 + c y.2.1.1) B hB hgmono hg oa ((∅, ∅), [])
    (not_or.2 ⟨G.not_conflict_empty, not_tcHazard_empty⟩)
  rw [potential_empty, tsub_zero] at h1
  calc _ ≤ Pr{let w ← G.deferredFillDraw ms oa}[((G.Conflict w.2.1 ∨ nk.TCHazard w.2.1) ∨
        H w.2.2 w.2.1.1) ∧ nk.potential w.2.1 + c w.2.1.1 ≤ B] := by
        refine prEvent_mono _ _ _ fun w hw ↦ ?_
        exact ⟨or_assoc.2 hw.1, (add_le_add (nk.potential_le_two_mul w.2.1) le_rfl).trans hw.2⟩
    _ ≤ B := by
      simpa only [deferredFillDraw, fillDraw, bind_assoc] using h1

/-- **The joint potential over three phases, under a pathwise budget.** When
`2 · #keyEntries / |R| + c ≤ B` holds at the end of every deferred run, the deferred game from
the empty state, the end fill, and an independent draw `s ← ms` whose hazard `H s` fires at
each public cache `C` with probability at most `c C` fire a conflict, a target collision at a
node key, or the hazard of the final public cache with probability at most `B`. -/
theorem prEvent_deferredFillDraw_le_of_budget {S α : Type} (ms : ProbComp S)
    (H : S → pub.QueryCache → Prop) (c : pub.QueryCache → ℝ≥0∞)
    (hH : ∀ C, Pr{let s ← ms}[H s C] ≤ c C) (oa : OracleComp (pub.withLabels X K R) α)
    (B : ℝ≥0∞) (hB : B ≠ ⊤)
    (hbud : ∀ z ∈ support ((simulateQ G.deferredImpl oa).run ((∅, ∅), [])),
      2 * ((nk.keyEntries z.2.1.1).encard : ℝ≥0∞) / Nat.card R + c z.2.1.1 ≤ B) :
    Pr{let w ← G.deferredFillDraw ms oa}[
      G.Conflict w.2.1 ∨ nk.TCHazard w.2.1 ∨ H w.2.2 w.2.1.1] ≤ B := by
  refine le_trans (prEvent_mono_of_support _ fun w hw h ↦ ⟨h, ?_⟩)
    (nk.prEvent_deferredFillDraw_and_le ms H c hH oa B hB)
  simp only [deferredFillDraw, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hw
  obtain ⟨z, hz, st, hst, s, -, rfl⟩ := hw
  rw [RelabelState.fst_eq_of_mem_support_endFill hst]
  exact hbud z hz

end ThreePhase

end NodeKeys

end CanonicalGraph
