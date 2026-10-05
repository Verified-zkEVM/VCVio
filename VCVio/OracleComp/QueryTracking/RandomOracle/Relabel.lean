/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module

public import VCVio.OracleComp.QueryTracking.RandomOracle.HiddenSeed
import VCVio.OracleComp.Constructions.SampleableType.NativeMeasure

/-!
# Canonical relabelling of a lazy random oracle

A program over `pub.withDerivations X R` (uniform sampling, a public random oracle `pub` and
derivation queries `x : X`) may evaluate a fixed graph of public queries. A
`CanonicalGraph pub X K R` records it: each node `k : K` has a list of children `G.ch k`, which
are derivations or other nodes, and is evaluated by the public query at its point `G.pt k vs`,
where `vs` are the values of its children. Distinct nodes, or one node at distinct children
values, have distinct points. The graph need not be acyclic, and a node may have no children.

The relabelled game `CanonicalGraph.relabelImpl` gives every node a lazily drawn label. A public
query at the point of a node whose children are all drawn, at their values, draws (or reads) that
node's label; every other public query is answered by the public cache; a derivation draws (or
reads) its entry in the derivation table. The state `RelabelState` holds the public cache, the
derivation table and the labels, and a cell `X ⊕ K` is drawn when its table entry or label is.
The merged cache `CanonicalGraph.merge` is the public cache the state stands for: the point of a
node whose children are drawn, at their values, reads the node's label, and every other point
reads the public cache.

The merged state follows the ideal game `SecretEncoding.idealImpl` except when a draw completes
the children of a node at values whose point the public cache already holds. This is the
final-state predicate `CanonicalGraph.Conflict`: some node whose children are all drawn has its
point, at their values, in the public cache. A step only fills cells and caches, so a conflict
persists. Off a conflict, every step of the relabelled game, read through the merge, is
dominated by the matching step of the ideal game, and
`QueryImpl.prEvent_simulateQ_run_le_map_or_bad` carries this to whole runs. Along the way, every
drawn label belongs to a node whose children are drawn (`CanonicalGraph.LabelsComplete`).

The eager game `CanonicalGraph.eagerImpl` extends the relabelled game by the label operations
`OracleSpec.labelOps`: `touch c` draws the cell `c` and discards it, and `read k` draws the label
of `k`. A program embedded from `pub.withDerivations X R` makes neither.

## Main statements

- `CanonicalGraph.prEvent_idealImpl_le_relabelImpl`: an event of the ideal game is at most the
  same event of the relabelled game, read on the merged state, or a conflict.
- `CanonicalGraph.prEvent_idealImpl_le_eagerImpl_liftComp`: the same bound in the eager game, for
  the program embedded into `pub.withLabels X K R`.
- `CanonicalGraph.prEvent_relabelImpl_and_not_conflict_le`: an event of the relabelled game, read
  on the merged state and off a conflict, is at most the same event of the ideal game.
- `CanonicalGraph.prEvent_relabelImpl_and_not_conflict_le_idealImpl`: the one-step comparison.
- `CanonicalGraph.preservesInv_conflict_relabelImpl`,
  `CanonicalGraph.preservesInv_conflict_eagerImpl` and `CanonicalGraph.Conflict.mono`: a conflict
  persists.
- `CanonicalGraph.merge_apply_pt`, `CanonicalGraph.merge_apply_of_not_exists` and
  `CanonicalGraph.merge_apply_eq_of_le`: the merged cache, point by point.
-/

public section

open OracleComp OracleSpec

namespace OracleSpec

variable (X K R : Type)

/-- Label operations on cells `X ⊕ K` (derivations and nodes): `touch` a cell, answered by
`Unit`, and `read` the label of a node, answered in `R`. -/
abbrev labelOps : OracleSpec ((X ⊕ K) ⊕ K) := ((X ⊕ K) →ₒ Unit) + (K →ₒ R)

variable {ι : Type} (pub : OracleSpec ι)

/-- Programs with uniform sampling, a public random oracle `pub`, derivation queries `X →ₒ R`
and the label operations on `X ⊕ K`. -/
abbrev withLabels : OracleSpec (((ℕ ⊕ ι) ⊕ X) ⊕ ((X ⊕ K) ⊕ K)) :=
  pub.withDerivations X R + labelOps X K R

end OracleSpec

/-- A graph of public points: each node `k : K` has children `ch k`, derivations or nodes, and a
public point `pt k vs` at children values `vs`, answered in `R`. Points of distinct nodes, or of
one node at distinct children values of the right length, are distinct. -/
structure CanonicalGraph {ι : Type} (pub : OracleSpec ι) (X K R : Type) where
  /-- The children of a node. -/
  ch : K → List (X ⊕ K)
  /-- The public point of a node at children values. -/
  pt : K → List R → ι
  /-- The public oracle answers every node point in `R`. -/
  range_eq : ∀ k vs, pub.Range (pt k vs) = R
  /-- Distinct nodes, or distinct children values, have distinct points. -/
  pt_inj : ∀ {k k' vs vs'}, vs.length = (ch k).length → vs'.length = (ch k').length →
    pt k vs = pt k' vs' → k = k' ∧ vs = vs'

/-- The state of the relabelled game: the public cache, the derivation table and the node
labels. -/
structure RelabelState {ι : Type} (pub : OracleSpec ι) (X K R : Type) where
  /-- The public cache. -/
  cache : pub.QueryCache
  /-- The derivation table. -/
  table : (X →ₒ R).QueryCache
  /-- The node labels. -/
  labels : (K →ₒ R).QueryCache

namespace RelabelState

variable {ι : Type} {pub : OracleSpec ι} {X K R : Type}

instance : EmptyCollection (RelabelState pub X K R) := ⟨⟨∅, ∅, ∅⟩⟩

@[simp] theorem cache_empty : (∅ : RelabelState pub X K R).cache = ∅ := rfl

@[simp] theorem table_empty : (∅ : RelabelState pub X K R).table = ∅ := rfl

@[simp] theorem labels_empty : (∅ : RelabelState pub X K R).labels = ∅ := rfl

/-- The three caches of a state determine it. -/
theorem toCaches_injective : Function.Injective fun st : RelabelState pub X K R ↦
    (st.cache, st.table, st.labels) := by
  rintro ⟨_, _, _⟩ ⟨_, _, _⟩ h
  simp only [Prod.mk.injEq] at h
  obtain ⟨rfl, rfl, rfl⟩ := h
  rfl

/-- States are ordered by extension of all three caches. -/
instance : PartialOrder (RelabelState pub X K R) :=
  PartialOrder.lift _ toCaches_injective

theorem le_iff {st st' : RelabelState pub X K R} :
    st ≤ st' ↔ st.cache ≤ st'.cache ∧ st.table ≤ st'.table ∧ st.labels ≤ st'.labels :=
  Iff.rfl

/-- The value of a cell, if drawn: a derivation reads the table, a node its label. -/
@[expose] def cell (st : RelabelState pub X K R) : X ⊕ K → Option R
  | .inl x => st.table x
  | .inr k => st.labels k

@[simp] theorem cell_inl (st : RelabelState pub X K R) (x : X) :
    st.cell (.inl x) = st.table x := rfl

@[simp] theorem cell_inr (st : RelabelState pub X K R) (k : K) :
    st.cell (.inr k) = st.labels k := rfl

/-- A drawn cell keeps its value in every extension. -/
theorem cell_mono {st st' : RelabelState pub X K R} (h : st ≤ st') {c : X ⊕ K} {v : R}
    (hc : st.cell c = some v) : st'.cell c = some v := by
  rcases c with x | k
  · exact h.2.1 hc
  · exact h.2.2 hc

variable [DecidableEq X] [DecidableEq K]

/-- Store a value in a cell. -/
@[expose] def setCell (st : RelabelState pub X K R) : X ⊕ K → R → RelabelState pub X K R
  | .inl x, u => { st with table := st.table.cacheQuery x u }
  | .inr k, u => { st with labels := st.labels.cacheQuery k u }

@[simp] theorem cache_setCell (st : RelabelState pub X K R) (c : X ⊕ K) (u : R) :
    (st.setCell c u).cache = st.cache := by
  rcases c with x | k <;> rfl

@[simp] theorem cell_setCell_self (st : RelabelState pub X K R) (c : X ⊕ K) (u : R) :
    (st.setCell c u).cell c = some u := by
  rcases c with x | k
  · exact QueryCache.cacheQuery_self st.table x u
  · exact QueryCache.cacheQuery_self st.labels k u

theorem cell_setCell_of_ne (st : RelabelState pub X K R) {c c' : X ⊕ K} (u : R)
    (h : c' ≠ c) : (st.setCell c u).cell c' = st.cell c' := by
  rcases c with x | k <;> rcases c' with x' | k'
  · exact QueryCache.cacheQuery_of_ne st.table (t := x) u fun hx ↦ h (congrArg _ hx)
  · rfl
  · rfl
  · exact QueryCache.cacheQuery_of_ne st.labels (t := k) u fun hk ↦ h (congrArg _ hk)

@[simp] theorem table_setCell_inr (st : RelabelState pub X K R) (k : K) (u : R) :
    (st.setCell (.inr k) u).table = st.table := rfl

@[simp] theorem labels_setCell_inl (st : RelabelState pub X K R) (x : X) (u : R) :
    (st.setCell (.inl x) u).labels = st.labels := rfl

@[simp] theorem table_setCell_inl (st : RelabelState pub X K R) (x : X) (u : R) :
    (st.setCell (.inl x) u).table = st.table.cacheQuery x u := rfl

@[simp] theorem labels_setCell_inr (st : RelabelState pub X K R) (k : K) (u : R) :
    (st.setCell (.inr k) u).labels = st.labels.cacheQuery k u := rfl

/-- Filling an undrawn cell extends the state. -/
theorem le_setCell (st : RelabelState pub X K R) {c : X ⊕ K} (u : R) (h : st.cell c = none) :
    st ≤ st.setCell c u := by
  rcases c with x | k
  · exact ⟨le_rfl, QueryCache.le_cacheQuery st.table h, le_rfl⟩
  · exact ⟨le_rfl, le_rfl, QueryCache.le_cacheQuery st.labels h⟩

variable [SampleableType R]

/-- Draw a cell lazily: a drawn cell returns its value, an undrawn one is filled uniformly. -/
noncomputable def drawCell (c : X ⊕ K) : StateT (RelabelState pub X K R) ProbComp R :=
  StateT.mk fun st ↦ match st.cell c with
    | some v => pure (v, st)
    | none => (fun u ↦ (u, st.setCell c u)) <$> ($ᵗ R)

theorem drawCell_run_of_cell_eq_some {c : X ⊕ K} {st : RelabelState pub X K R} {v : R}
    (h : st.cell c = some v) : (drawCell c).run st = pure (v, st) := by
  simp only [drawCell, StateT.run_mk, h]

theorem drawCell_run_of_cell_eq_none {c : X ⊕ K} {st : RelabelState pub X K R}
    (h : st.cell c = none) :
    (drawCell c).run st = (fun u ↦ (u, st.setCell c u)) <$> ($ᵗ R) := by
  simp only [drawCell, StateT.run_mk, h]

/-- Drawing a cell extends the state, and leaves the cell drawn at the returned value. -/
theorem le_and_cell_eq_of_mem_support_drawCell {c : X ⊕ K} {st : RelabelState pub X K R}
    {z : R × RelabelState pub X K R} (hz : z ∈ support ((drawCell c).run st)) :
    st ≤ z.2 ∧ z.2.cell c = some z.1 := by
  cases h : st.cell c with
  | some v =>
    rw [drawCell_run_of_cell_eq_some h, support_pure, Set.mem_singleton_iff] at hz
    subst hz
    exact ⟨le_rfl, h⟩
  | none =>
    rw [drawCell_run_of_cell_eq_none h, support_map] at hz
    obtain ⟨u, -, rfl⟩ := hz
    exact ⟨st.le_setCell u h, st.cell_setCell_self c u⟩

/-- The label operations with every operation drawing its cell: `touch c` draws `c` and discards
it, `read k` draws the label of `k`. -/
@[expose] noncomputable def labelImpl :
    QueryImpl (OracleSpec.labelOps X K R) (StateT (RelabelState pub X K R) ProbComp) := fun
  | .inl c => (fun _ ↦ ()) <$> drawCell c
  | .inr k => drawCell (.inr k)

theorem labelImpl_touch (c : X ⊕ K) :
    (labelImpl (.inl c) : StateT (RelabelState pub X K R) ProbComp _) =
      (fun _ ↦ ()) <$> drawCell c := rfl

theorem labelImpl_read (k : K) :
    (labelImpl (.inr k) : StateT (RelabelState pub X K R) ProbComp _) = drawCell (.inr k) := rfl

/-- Every step of the label operations extends the state. -/
theorem le_of_mem_support_labelImpl {t : (OracleSpec.labelOps X K R).Domain}
    {st : RelabelState pub X K R} {z} (hz : z ∈ support ((labelImpl t).run st)) : st ≤ z.2 := by
  rcases t with c | k
  · rw [labelImpl_touch, StateT.run_map, support_map] at hz
    obtain ⟨w, hw, rfl⟩ := hz
    exact (le_and_cell_eq_of_mem_support_drawCell hw).1
  · exact (le_and_cell_eq_of_mem_support_drawCell hz).1

end RelabelState

namespace SecretEncoding

variable {ι : Type} {pub : OracleSpec ι} {X R : Type} [DecidableEq ι] [DecidableEq X]
  [SampleableType R] [∀ t, SampleableType (pub.Range t)]

/-- The ideal game reads a drawn derivation from its table. -/
theorem idealImpl_run_derive_some {x : X} {st : SecretEncoding.SplitCache pub X R} {v : R}
    (h : st.2 x = some v) :
    (SecretEncoding.idealImpl pub X R (.inr x)).run st = pure (v, st) := by
  simp [SecretEncoding.idealImpl, h]

/-- The ideal game draws an undrawn derivation uniformly and stores it in its table. -/
theorem idealImpl_run_derive_none {x : X} {st : SecretEncoding.SplitCache pub X R}
    (h : st.2 x = none) :
    (SecretEncoding.idealImpl pub X R (.inr x)).run st =
      (fun u ↦ (u, (st.1, st.2.cacheQuery x u))) <$> ($ᵗ R) := by
  simp [SecretEncoding.idealImpl, h]

/-- The ideal game reads a cached public answer from its public cache. -/
theorem idealImpl_run_pub_some {t : ι} {st : SecretEncoding.SplitCache pub X R}
    {v : pub.Range t} (h : st.1 t = some v) :
    (SecretEncoding.idealImpl pub X R (.inl (.inr t))).run st = pure (v, st) := by
  simp [SecretEncoding.idealImpl, h]

/-- The ideal game draws an uncached public answer uniformly and caches it. -/
theorem idealImpl_run_pub_none {t : ι} {st : SecretEncoding.SplitCache pub X R}
    (h : st.1 t = none) :
    (SecretEncoding.idealImpl pub X R (.inl (.inr t))).run st =
      (fun u ↦ (u, (st.1.cacheQuery t u, st.2))) <$> ($ᵗ pub.Range t) := by
  simp [SecretEncoding.idealImpl, h]

end SecretEncoding

namespace CanonicalGraph

variable {ι : Type} {pub : OracleSpec ι} {X K R : Type} (G : CanonicalGraph pub X K R)

/-- Every point witnessed as a node point is answered in `R`. -/
theorem range_eq_of_pt_eq {k : K} {vs : List R} {t : ι} (h : G.pt k vs = t) : pub.Range t = R :=
  h ▸ G.range_eq k vs

/-! ## Children values -/

/-- The values of the children of a node, if all are drawn. -/
def childVals (st : RelabelState pub X K R) (k : K) : Option (List R) :=
  (G.ch k).mapM st.cell

private theorem mapM_eq_some_iff {α β : Type} (f : α → Option β) : ∀ (l : List α) (l' : List β),
    l.mapM f = some l' ↔ List.Forall₂ (fun a b ↦ f a = some b) l l'
  | [], l' => by cases l' <;> simp
  | a :: l, l' => by
    rw [List.mapM_cons]
    cases l' with
    | nil =>
      simp only [List.forall₂_nil_right_iff, reduceCtorEq, iff_false]
      cases f a <;> cases l.mapM f <;> simp
    | cons b l' =>
      rw [List.forall₂_cons, ← mapM_eq_some_iff f l l']
      cases f a <;> cases l.mapM f <;> simp

/-- The children of `k` are drawn at the values `vs` exactly when the two lists agree cell by
cell. -/
theorem childVals_eq_some_iff {st : RelabelState pub X K R} {k : K} {vs : List R} :
    G.childVals st k = some vs ↔ List.Forall₂ (fun c v ↦ st.cell c = some v) (G.ch k) vs :=
  mapM_eq_some_iff _ _ _

/-- Children values have one entry per child. -/
theorem length_eq_of_childVals_eq_some {st : RelabelState pub X K R} {k : K} {vs : List R}
    (h : G.childVals st k = some vs) : vs.length = (G.ch k).length :=
  ((G.childVals_eq_some_iff.1 h).length_eq).symm

/-- Children drawn at some values stay drawn at those values in every extension. -/
theorem childVals_mono {st st' : RelabelState pub X K R} (hle : st ≤ st') {k : K}
    {vs : List R} (h : G.childVals st k = some vs) : G.childVals st' k = some vs :=
  G.childVals_eq_some_iff.2 ((G.childVals_eq_some_iff.1 h).imp fun _ _ ↦
    RelabelState.cell_mono hle)

/-- A point is the point of at most one node at drawn children values. -/
theorem eq_of_childVals_of_pt_eq {st st' : RelabelState pub X K R} {k k' : K}
    {vs vs' : List R} (h : G.childVals st k = some vs) (h' : G.childVals st' k' = some vs')
    (hpt : G.pt k vs = G.pt k' vs') : k = k' ∧ vs = vs' :=
  G.pt_inj (G.length_eq_of_childVals_eq_some h) (G.length_eq_of_childVals_eq_some h') hpt

/-! ## Merging the state into a public cache -/

open Classical in
/-- The public cache the relabelled state stands for: the point of a node whose children are
drawn, at their values, reads the node's label; every other point reads the public cache. -/
noncomputable def merge (st : RelabelState pub X K R) : pub.QueryCache :=
  .ofFn fun t ↦ if h : ∃ k vs, G.childVals st k = some vs ∧ G.pt k vs = t then
    (st.labels h.choose).map (cast (G.range_eq_of_pt_eq h.choose_spec.choose_spec.2).symm)
  else st.cache t

/-- The merged cache at the point of a node at its drawn children values reads its label. -/
theorem merge_apply_pt {st : RelabelState pub X K R} {k : K} {vs : List R}
    (h : G.childVals st k = some vs) :
    G.merge st (G.pt k vs) = (st.labels k).map (cast (G.range_eq k vs).symm) := by
  have key : ∀ k' vs' (h' : G.childVals st k' = some vs' ∧ G.pt k' vs' = G.pt k vs),
      (st.labels k').map (cast (G.range_eq_of_pt_eq h'.2).symm) =
        (st.labels k).map (cast (G.range_eq k vs).symm) := by
    intro k' vs' h'
    obtain ⟨rfl, rfl⟩ := G.eq_of_childVals_of_pt_eq h'.1 h h'.2
    rfl
  simp only [merge, QueryCache.ofFn_apply]
  split
  · rename_i hex
    exact key _ _ hex.choose_spec.choose_spec
  · rename_i hex
    exact absurd ⟨k, vs, h, rfl⟩ hex

/-- The merged cache at a point of no node at drawn children values reads the public cache. -/
theorem merge_apply_of_not_exists {st : RelabelState pub X K R} {t : ι}
    (ht : ¬∃ k vs, G.childVals st k = some vs ∧ G.pt k vs = t) : G.merge st t = st.cache t := by
  simp only [merge, QueryCache.ofFn_apply, ht, ↓reduceDIte]

/-- Merging the empty state gives the empty cache. -/
@[simp] theorem merge_empty : G.merge (∅ : RelabelState pub X K R) = ∅ := by
  refine QueryCache.ext fun t ↦ ?_
  by_cases ht : ∃ k vs, G.childVals ∅ k = some vs ∧ G.pt k vs = t
  · obtain ⟨k, vs, hk, rfl⟩ := ht
    simp only [G.merge_apply_pt hk, RelabelState.labels_empty, QueryCache.empty_apply,
      Option.map_none]
  · simp only [G.merge_apply_of_not_exists ht, RelabelState.cache_empty, QueryCache.empty_apply]

/-- The split state of the ideal game that a relabelled state stands for: the merged cache and
the derivation table. -/
@[expose] noncomputable def toSplitCache (st : RelabelState pub X K R) :
    SecretEncoding.SplitCache pub X R :=
  (G.merge st, st.table)

@[simp] theorem toSplitCache_empty : G.toSplitCache (∅ : RelabelState pub X K R) = (∅, ∅) := by
  simp only [toSplitCache, merge_empty, RelabelState.table_empty]

/-! ## Conflicts -/

/-- Some node whose children are all drawn has its point, at their values, in the public
cache. -/
@[expose] def Conflict (st : RelabelState pub X K R) : Prop :=
  ∃ k vs, G.childVals st k = some vs ∧ (st.cache (G.pt k vs)).isSome

/-- A conflict persists in every extension. -/
theorem Conflict.mono {st st' : RelabelState pub X K R} (hle : st ≤ st') (h : G.Conflict st) :
    G.Conflict st' := by
  obtain ⟨k, vs, hk, hc⟩ := h
  exact ⟨k, vs, G.childVals_mono hle hk, QueryCache.isSome_mono hle.1 hc⟩

/-- Every drawn label belongs to a node whose children are all drawn. -/
@[expose] def LabelsComplete (st : RelabelState pub X K R) : Prop :=
  ∀ k, (st.labels k).isSome → (G.childVals st k).isSome

theorem labelsComplete_empty : G.LabelsComplete (∅ : RelabelState pub X K R) := by
  intro k hk
  simp only [RelabelState.labels_empty, QueryCache.empty_apply, Option.isSome_none,
    Bool.false_eq_true] at hk

/-- Off a conflict, a state extending `st` merges to the same value as `st` at a point `t`
where the public cache is unchanged and no node at `t` with drawn children has a new label, when
every label drawn in `st` belongs to a node with drawn children. -/
theorem merge_apply_eq_of_le {st st' : RelabelState pub X K R} (hle : st ≤ st')
    (hinv : G.LabelsComplete st) (hc : ¬G.Conflict st') {t : ι}
    (hcache : st'.cache t = st.cache t)
    (hlab : ∀ k vs, G.childVals st' k = some vs → G.pt k vs = t → st'.labels k = st.labels k) :
    G.merge st' t = G.merge st t := by
  by_cases ht' : ∃ k vs, G.childVals st' k = some vs ∧ G.pt k vs = t
  · obtain ⟨k, vs, hk', rfl⟩ := ht'
    rw [G.merge_apply_pt hk', hlab k vs hk' rfl]
    cases hk : G.childVals st k with
    | some ws =>
      obtain rfl : ws = vs := Option.some_inj.1 ((G.childVals_mono hle hk).symm.trans hk')
      rw [G.merge_apply_pt hk]
    | none =>
      have hl : st.labels k = none := by
        cases hl : st.labels k with
        | none => rfl
        | some _ => simpa only [hk, hl, Option.isSome_some, Option.isSome_none,
            Bool.false_eq_true, imp_false, not_true_eq_false] using hinv k
      have hnot : ¬∃ k' vs', G.childVals st k' = some vs' ∧ G.pt k' vs' = G.pt k vs := by
        rintro ⟨k', vs', hk'', hpt⟩
        obtain ⟨rfl, rfl⟩ := G.eq_of_childVals_of_pt_eq (G.childVals_mono hle hk'') hk' hpt
        rw [hk] at hk''
        exact absurd hk'' (Option.some_ne_none _).symm
      rw [G.merge_apply_of_not_exists hnot, ← hcache, hl, Option.map_none]
      cases hC : st'.cache (G.pt k vs) with
      | none => rfl
      | some _ => exact absurd ⟨k, vs, hk', by rw [hC]; rfl⟩ hc
  · have ht : ¬∃ k vs, G.childVals st k = some vs ∧ G.pt k vs = t := fun ⟨k, vs, hk, hpt⟩ ↦
      ht' ⟨k, vs, G.childVals_mono hle hk, hpt⟩
    rw [G.merge_apply_of_not_exists ht', G.merge_apply_of_not_exists ht, hcache]

/-! ## The relabelled game -/

variable [DecidableEq ι] [DecidableEq X] [DecidableEq K] [SampleableType R]
  [∀ t, SampleableType (pub.Range t)]

open Classical in
/-- **The relabelled game.** A public query at the point of a node whose children are all drawn,
at their values, draws (or reads) the node's label; every other public query is answered by the
public cache; a derivation draws (or reads) its table entry. -/
noncomputable def relabelImpl :
    QueryImpl (pub.withDerivations X R) (StateT (RelabelState pub X K R) ProbComp) := fun
  | .inl (.inl n) => StateT.mk fun st ↦ (fun u ↦ (u, st)) <$> (unifSpec.query n : ProbComp _)
  | .inl (.inr t) => StateT.mk fun st ↦
      if h : ∃ k vs, G.childVals st k = some vs ∧ G.pt k vs = t then
        Prod.map (cast (G.range_eq_of_pt_eq h.choose_spec.choose_spec.2).symm) id <$>
          (RelabelState.drawCell (.inr h.choose)).run st
      else (fun z ↦ (z.1, { st with cache := z.2 })) <$> (pub.randomOracle t).run st.cache
  | .inr x => RelabelState.drawCell (.inl x)

/-- The relabelled game extended by the label operations, each drawing its cell. -/
@[expose] noncomputable def eagerImpl :
    QueryImpl (pub.withLabels X K R) (StateT (RelabelState pub X K R) ProbComp) :=
  G.relabelImpl +
    (RelabelState.labelImpl :
      QueryImpl (OracleSpec.labelOps X K R) (StateT (RelabelState pub X K R) ProbComp))

theorem relabelImpl_run_unif (n : ℕ) (st : RelabelState pub X K R) :
    (G.relabelImpl (.inl (.inl n))).run st =
      (fun u ↦ (u, st)) <$> (unifSpec.query n : ProbComp _) := by
  rfl

theorem relabelImpl_derive (x : X) :
    G.relabelImpl (.inr x) = RelabelState.drawCell (.inl x) := by
  rfl

/-- A public query at the point of a node at its drawn children values draws its label. -/
theorem relabelImpl_run_pt {st : RelabelState pub X K R} {k : K} {vs : List R}
    (h : G.childVals st k = some vs) :
    (G.relabelImpl (.inl (.inr (G.pt k vs)))).run st =
      Prod.map (cast (G.range_eq k vs).symm) id <$> (RelabelState.drawCell (.inr k)).run st := by
  have key : ∀ k' vs' (h' : G.childVals st k' = some vs' ∧ G.pt k' vs' = G.pt k vs),
      Prod.map (cast (G.range_eq_of_pt_eq h'.2).symm) id <$>
          (RelabelState.drawCell (.inr k')).run st =
        Prod.map (cast (G.range_eq k vs).symm) id <$>
          (RelabelState.drawCell (.inr k)).run st := by
    intro k' vs' h'
    obtain ⟨rfl, rfl⟩ := G.eq_of_childVals_of_pt_eq h'.1 h h'.2
    rfl
  simp only [relabelImpl, StateT.run_mk]
  split
  · rename_i hex
    exact key _ _ hex.choose_spec.choose_spec
  · rename_i hex
    exact absurd ⟨k, vs, h, rfl⟩ hex

/-- A public query at a point of no node at drawn children values is answered by the public
cache. -/
theorem relabelImpl_run_pub_of_not_exists {st : RelabelState pub X K R} {t : ι}
    (ht : ¬∃ k vs, G.childVals st k = some vs ∧ G.pt k vs = t) :
    (G.relabelImpl (.inl (.inr t))).run st =
      (fun z ↦ (z.1, { st with cache := z.2 })) <$> (pub.randomOracle t).run st.cache := by
  simp only [relabelImpl, StateT.run_mk, ht, ↓reduceDIte]

theorem eagerImpl_apply_inl (t : (pub.withDerivations X R).Domain) :
    G.eagerImpl (.inl t) = G.relabelImpl t := rfl

theorem eagerImpl_apply_inr (t : (OracleSpec.labelOps X K R).Domain) :
    G.eagerImpl (.inr t) = RelabelState.labelImpl t := rfl

/-- A program over `pub.withDerivations X R`, embedded into `pub.withLabels X K R` along the left
summand, runs in the eager game as in the relabelled game: it makes no label operation. -/
theorem simulateQ_eagerImpl_liftComp {α : Type} (oa : OracleComp (pub.withDerivations X R) α) :
    simulateQ G.eagerImpl (@liftComp _ _ _ _ oa (pub.withLabels X K R)
      (@instMonadLiftTOfMonadLift _ _ _ OracleQuery.subSpec_add_left.toMonadLift
        inferInstance)) = simulateQ G.relabelImpl oa :=
  QueryImpl.simulateQ_add_liftComp_left _ _ oa

/-! ## Monotonicity of the relabelled game -/

/-- Every step of the relabelled game extends the state. -/
theorem le_of_mem_support_relabelImpl {t : (pub.withDerivations X R).Domain}
    {st : RelabelState pub X K R} {z} (hz : z ∈ support ((G.relabelImpl t).run st)) :
    st ≤ z.2 := by
  rcases t with (n | t) | x
  · rw [relabelImpl_run_unif, support_map] at hz
    obtain ⟨_, -, rfl⟩ := hz
    exact le_rfl
  · by_cases ht : ∃ k vs, G.childVals st k = some vs ∧ G.pt k vs = t
    · obtain ⟨k, vs, hk, rfl⟩ := ht
      rw [G.relabelImpl_run_pt hk, support_map] at hz
      obtain ⟨w, hw, rfl⟩ := hz
      exact (RelabelState.le_and_cell_eq_of_mem_support_drawCell hw).1
    · rw [G.relabelImpl_run_pub_of_not_exists ht, support_map] at hz
      obtain ⟨w, hw, rfl⟩ := hz
      exact ⟨QueryImpl.withCaching_cache_le _ _ _ _ hw, le_rfl, le_rfl⟩
  · exact (RelabelState.le_and_cell_eq_of_mem_support_drawCell hz).1

/-- Every step of the eager game extends the state. -/
theorem le_of_mem_support_eagerImpl {t : (pub.withLabels X K R).Domain}
    {st : RelabelState pub X K R} {z} (hz : z ∈ support ((G.eagerImpl t).run st)) :
    st ≤ z.2 := by
  rcases t with t | t
  · exact G.le_of_mem_support_relabelImpl hz
  · exact RelabelState.le_of_mem_support_labelImpl hz

/-- A conflict persists along the relabelled game. -/
theorem preservesInv_conflict_relabelImpl : QueryImpl.PreservesInv G.relabelImpl G.Conflict :=
  fun _ _ h _ hz ↦ h.mono G (G.le_of_mem_support_relabelImpl hz)

/-- A conflict persists along the eager game. -/
theorem preservesInv_conflict_eagerImpl : QueryImpl.PreservesInv G.eagerImpl G.Conflict :=
  fun _ _ h _ hz ↦ h.mono G (G.le_of_mem_support_eagerImpl hz)

/-- In the relabelled game, a label is drawn only for a node whose children are all drawn. -/
theorem preservesInv_labelsComplete_relabelImpl :
    QueryImpl.PreservesInv G.relabelImpl G.LabelsComplete := by
  intro t st hinv z hz
  have hle := G.le_of_mem_support_relabelImpl hz
  -- A step either keeps the labels or draws the label of a node with drawn children.
  have hlab : z.2.labels = st.labels ∨
      ∃ k, (G.childVals st k).isSome ∧ ∀ k', k' ≠ k → z.2.labels k' = st.labels k' := by
    rcases t with (n | t) | x
    · rw [relabelImpl_run_unif, support_map] at hz
      obtain ⟨_, -, rfl⟩ := hz
      exact .inl rfl
    · by_cases ht : ∃ k vs, G.childVals st k = some vs ∧ G.pt k vs = t
      · obtain ⟨k, vs, hk, rfl⟩ := ht
        rw [G.relabelImpl_run_pt hk, support_map] at hz
        obtain ⟨w, hw, rfl⟩ := hz
        refine .inr ⟨k, by rw [hk]; rfl, fun k' hk' ↦ ?_⟩
        cases hc : st.cell (.inr k) with
        | some v =>
          rw [RelabelState.drawCell_run_of_cell_eq_some hc, support_pure,
            Set.mem_singleton_iff] at hw
          rw [hw]
          rfl
        | none =>
          rw [RelabelState.drawCell_run_of_cell_eq_none hc, support_map] at hw
          obtain ⟨u, -, rfl⟩ := hw
          exact QueryCache.cacheQuery_of_ne _ _ hk'
      · rw [G.relabelImpl_run_pub_of_not_exists ht, support_map] at hz
        obtain ⟨w, -, rfl⟩ := hz
        exact .inl rfl
    · rw [relabelImpl_derive] at hz
      cases hc : st.cell (.inl x) with
      | some v =>
        rw [RelabelState.drawCell_run_of_cell_eq_some hc, support_pure,
          Set.mem_singleton_iff] at hz
        rw [hz]
        exact .inl rfl
      | none =>
        rw [RelabelState.drawCell_run_of_cell_eq_none hc, support_map] at hz
        obtain ⟨u, -, rfl⟩ := hz
        exact .inl rfl
  intro k hk
  have hsome : (G.childVals st k).isSome := by
    rcases hlab with hlab | ⟨k₀, hk₀, hlab⟩
    · exact hinv k (hlab ▸ hk)
    · by_cases hkk : k = k₀
      · exact hkk ▸ hk₀
      · exact hinv k (hlab k hkk ▸ hk)
  obtain ⟨vs, hvs⟩ := Option.isSome_iff_exists.1 hsome
  rw [G.childVals_mono hle hvs]
  rfl

/-! ## The relabelled game projects onto the ideal game off a conflict -/

private theorem prEvent_pure_le {α β : Type} (a : α) (b : β) (p : α → Prop) (q : β → Prop)
    (h : p a → q b) :
    Pr{let z ← (pure a : ProbComp α)}[p z] ≤ Pr{let z ← (pure b : ProbComp β)}[q z] := by
  calc Pr{let z ← (pure a : ProbComp α)}[p z] = Pr{let z ← (pure b : ProbComp β)}[p a] := by
        simp only [pure_bind]
    _ ≤ _ := prEvent_mono_of_support _ fun z hz hp ↦ by
        rw [support_pure, Set.mem_singleton_iff] at hz
        exact hz ▸ h hp

private theorem prEvent_map_le_map {γ α β : Type} (mx : ProbComp γ) (f : γ → α) (g : γ → β)
    (p : α → Prop) (q : β → Prop) (h : ∀ x, p (f x) → q (g x)) :
    Pr{let z ← f <$> mx}[p z] ≤ Pr{let z ← g <$> mx}[q z] := by
  rw [prEvent_map, prEvent_map]
  exact prEvent_mono _ _ _ h

private theorem step_unif (n : ℕ) (st : RelabelState pub X K R)
    (Q : (pub.withDerivations X R).Range (.inl (.inl n)) ×
      SecretEncoding.SplitCache pub X R → Prop) :
    Pr{let z ← (G.relabelImpl (.inl (.inl n))).run st}[
        Q (z.1, G.toSplitCache z.2) ∧ ¬G.Conflict z.2] ≤
      Pr{let z ← ((SecretEncoding.idealImpl pub X R (.inl (.inl n))).run
        (G.toSplitCache st))}[Q z] := by
  rw [relabelImpl_run_unif, prEvent_map]
  change _ ≤ Pr{let z ← (fun u ↦ (u, G.toSplitCache st)) <$> (unifSpec.query n : ProbComp _)}[Q z]
  rw [prEvent_map]
  exact prEvent_mono _ (fun u ↦ Q (u, G.toSplitCache st) ∧ ¬G.Conflict st) _ fun _ h ↦ h.1

private theorem step_derive (x : X) (st : RelabelState pub X K R) (hinv : G.LabelsComplete st)
    (Q : (pub.withDerivations X R).Range (.inr x) × SecretEncoding.SplitCache pub X R → Prop) :
    Pr{let z ← (G.relabelImpl (.inr x)).run st}[Q (z.1, G.toSplitCache z.2) ∧ ¬G.Conflict z.2] ≤
      Pr{let z ← (SecretEncoding.idealImpl pub X R (.inr x)).run (G.toSplitCache st)}[Q z] := by
  rw [relabelImpl_derive]
  cases hT : st.table x with
  | some v =>
    rw [RelabelState.drawCell_run_of_cell_eq_some (c := .inl x) hT,
      SecretEncoding.idealImpl_run_derive_some (st := G.toSplitCache st) hT]
    exact prEvent_pure_le _ _ _ _ And.left
  | none =>
    rw [RelabelState.drawCell_run_of_cell_eq_none (c := .inl x) hT,
      SecretEncoding.idealImpl_run_derive_none (st := G.toSplitCache st) hT]
    refine prEvent_map_le_map _ _ _ _ _ fun u hu ↦ ?_
    have hm : G.merge (st.setCell (.inl x) u) = G.merge st :=
      QueryCache.ext fun t ↦ G.merge_apply_eq_of_le (st.le_setCell (c := .inl x) u hT) hinv hu.2
        (by rw [RelabelState.cache_setCell]) fun _ _ _ _ ↦ rfl
    have h2 : G.toSplitCache (st.setCell (.inl x) u) =
        ((G.toSplitCache st).1, st.table.cacheQuery x u) := by
      rw [toSplitCache, toSplitCache, hm]; rfl
    exact h2 ▸ hu.1
private theorem step_pt (st : RelabelState pub X K R) (hinv : G.LabelsComplete st) {k : K}
    {vs : List R} (hk : G.childVals st k = some vs)
    (Q : (pub.withDerivations X R).Range (.inl (.inr (G.pt k vs))) ×
      SecretEncoding.SplitCache pub X R → Prop) :
    Pr{let z ← (G.relabelImpl (.inl (.inr (G.pt k vs)))).run st}[
        Q (z.1, G.toSplitCache z.2) ∧ ¬G.Conflict z.2] ≤
      Pr{let z ← ((SecretEncoding.idealImpl pub X R (.inl (.inr (G.pt k vs)))).run
        (G.toSplitCache st))}[Q z] := by
  rw [G.relabelImpl_run_pt hk]
  have hmerge := G.merge_apply_pt hk
  cases hl : st.labels k with
  | some v =>
    rw [RelabelState.drawCell_run_of_cell_eq_some (c := .inr k) hl, map_pure,
      SecretEncoding.idealImpl_run_pub_some (st := G.toSplitCache st)
        (v := cast (G.range_eq k vs).symm v) (by rw [toSplitCache, hmerge, hl]; rfl)]
    exact prEvent_pure_le _ _ _ _ And.left
  | none =>
    rw [RelabelState.drawCell_run_of_cell_eq_none (c := .inr k) hl, Functor.map_map,
      SecretEncoding.idealImpl_run_pub_none (st := G.toSplitCache st)
        (by rw [toSplitCache, hmerge, hl]; rfl),
      prEvent_map]
    refine le_trans ?_ (le_of_eq (prEvent_map _ _ _).symm)
    rw [← SampleableType.prEvent_map_cast_uniformSample (G.range_eq k vs).symm, prEvent_map]
    refine prEvent_mono _ _ _ fun u hu ↦ ?_
    set h := (G.range_eq k vs).symm
    have hle : st ≤ st.setCell (.inr k) u := st.le_setCell (c := .inr k) u hl
    have hm : G.merge (st.setCell (.inr k) u) =
        (G.merge st).cacheQuery (G.pt k vs) (cast h u) := by
      refine QueryCache.ext fun t ↦ ?_
      by_cases ht : t = G.pt k vs
      · subst ht
        rw [G.merge_apply_pt (G.childVals_mono hle hk), QueryCache.cacheQuery_self,
          RelabelState.labels_setCell_inr, QueryCache.cacheQuery_self]
        rfl
      · rw [QueryCache.cacheQuery_of_ne _ _ ht]
        refine G.merge_apply_eq_of_le hle hinv hu.2 (by rw [RelabelState.cache_setCell])
          fun k' vs' hk' hpt ↦ ?_
        have hkk : k' ≠ k := by
          rintro rfl
          obtain rfl : vs' = vs := Option.some_inj.1 (hk'.symm.trans (G.childVals_mono hle hk))
          exact ht hpt.symm
        exact QueryCache.cacheQuery_of_ne _ _ hkk
    have h2 : G.toSplitCache (st.setCell (.inr k) u) =
        ((G.merge st).cacheQuery (G.pt k vs) (cast h u), st.table) := by
      rw [toSplitCache, hm]; rfl
    exact h2 ▸ hu.1

private theorem step_pub_of_not_exists (st : RelabelState pub X K R) (hinv : G.LabelsComplete st)
    {t : ι} (ht : ¬∃ k vs, G.childVals st k = some vs ∧ G.pt k vs = t)
    (Q : (pub.withDerivations X R).Range (.inl (.inr t)) ×
      SecretEncoding.SplitCache pub X R → Prop) :
    Pr{let z ← (G.relabelImpl (.inl (.inr t))).run st}[
        Q (z.1, G.toSplitCache z.2) ∧ ¬G.Conflict z.2] ≤
      Pr{let z ← ((SecretEncoding.idealImpl pub X R (.inl (.inr t))).run
        (G.toSplitCache st))}[Q z] := by
  have hmerge : (G.toSplitCache st).1 t = st.cache t := G.merge_apply_of_not_exists ht
  cases hc : st.cache t with
  | some v =>
    have hrun : (G.relabelImpl (.inl (.inr t))).run st = pure (v, st) := by
      rw [G.relabelImpl_run_pub_of_not_exists ht, randomOracle.run_eq]
      simp [hc]
    rw [hrun, SecretEncoding.idealImpl_run_pub_some (hmerge.trans hc)]
    exact prEvent_pure_le _ _ _ _ And.left
  | none =>
    have hrun : (G.relabelImpl (.inl (.inr t))).run st =
        (fun u ↦ (u, { st with cache := st.cache.cacheQuery t u })) <$> ($ᵗ pub.Range t) := by
      rw [G.relabelImpl_run_pub_of_not_exists ht, randomOracle.run_eq]
      simp [hc]
    rw [hrun, SecretEncoding.idealImpl_run_pub_none (hmerge.trans hc)]
    refine prEvent_map_le_map _ _ _ _ _ fun u hu ↦ ?_
    set st' : RelabelState pub X K R := { st with cache := st.cache.cacheQuery t u }
    have hle : st ≤ st' := ⟨QueryCache.le_cacheQuery _ hc, le_rfl, le_rfl⟩
    have hm : G.merge st' = (G.merge st).cacheQuery t u := by
      refine QueryCache.ext fun t' ↦ ?_
      by_cases htt : t' = t
      · subst htt
        rw [QueryCache.cacheQuery_self, G.merge_apply_of_not_exists (st := st') ht]
        exact QueryCache.cacheQuery_self _ _ _
      · rw [QueryCache.cacheQuery_of_ne _ _ htt]
        exact G.merge_apply_eq_of_le hle hinv hu.2 (QueryCache.cacheQuery_of_ne _ _ htt)
          fun _ _ _ _ ↦ rfl
    have h2 : G.toSplitCache st' = ((G.merge st).cacheQuery t u, st.table) := by
      rw [toSplitCache, hm]
    exact h2 ▸ hu.1

/-- Off a conflict, each step of the relabelled game, with its post-state merged, puts on every
event at most the mass of the matching step of the ideal game from the merged state, when every
drawn label belongs to a node whose children are all drawn. -/
theorem prEvent_relabelImpl_and_not_conflict_le_idealImpl
    (t : (pub.withDerivations X R).Domain) (st : RelabelState pub X K R)
    (hinv : G.LabelsComplete st)
    (Q : (pub.withDerivations X R).Range t × SecretEncoding.SplitCache pub X R → Prop) :
    Pr{let z ← (G.relabelImpl t).run st}[Q (z.1, G.toSplitCache z.2) ∧ ¬G.Conflict z.2] ≤
      Pr{let z ← (SecretEncoding.idealImpl pub X R t).run (G.toSplitCache st)}[Q z] := by
  rcases t with (n | t) | x
  · exact G.step_unif n st Q
  · by_cases ht : ∃ k vs, G.childVals st k = some vs ∧ G.pt k vs = t
    · obtain ⟨k, vs, hk, rfl⟩ := ht
      exact G.step_pt st hinv hk Q
    · exact G.step_pub_of_not_exists st hinv ht Q
  · exact G.step_derive x st hinv Q

/-- **Canonical relabelling, off a conflict.** An event of the relabelled game, read on the
merged state and conjoined with the absence of a conflict, is at most the same event of the
ideal game. -/
theorem prEvent_relabelImpl_and_not_conflict_le {α : Type}
    (oa : OracleComp (pub.withDerivations X R) α)
    (P : α × SecretEncoding.SplitCache pub X R → Prop) :
    Pr{let z ← (simulateQ G.relabelImpl oa).run ∅}[
        P (z.1, G.toSplitCache z.2) ∧ ¬G.Conflict z.2] ≤
      Pr{let z ← (simulateQ (SecretEncoding.idealImpl pub X R) oa).run (∅, ∅)}[P z] := by
  have h := QueryImpl.prEvent_simulateQ_run_map_and_not_bad_le G.toSplitCache
    G.preservesInv_labelsComplete_relabelImpl G.preservesInv_conflict_relabelImpl
    (fun t st hinv _ Q ↦ G.prEvent_relabelImpl_and_not_conflict_le_idealImpl t st hinv Q)
    oa ∅ G.labelsComplete_empty P
  rwa [toSplitCache_empty] at h

/-- **Canonical relabelling.** An event of the ideal game is at most the same event of the
relabelled game, read on the merged state, or a conflict. -/
theorem prEvent_idealImpl_le_relabelImpl {α : Type}
    (oa : OracleComp (pub.withDerivations X R) α)
    (P : α × SecretEncoding.SplitCache pub X R → Prop) :
    Pr{let z ← (simulateQ (SecretEncoding.idealImpl pub X R) oa).run (∅, ∅)}[P z] ≤
      Pr{let z ← (simulateQ G.relabelImpl oa).run ∅}[
        P (z.1, G.toSplitCache z.2) ∨ G.Conflict z.2] := by
  have h := QueryImpl.prEvent_simulateQ_run_le_map_or_bad G.toSplitCache
    G.preservesInv_labelsComplete_relabelImpl G.preservesInv_conflict_relabelImpl
    (fun t st hinv _ Q ↦ G.prEvent_relabelImpl_and_not_conflict_le_idealImpl t st hinv Q)
    oa ∅ G.labelsComplete_empty P
  rwa [toSplitCache_empty] at h

/-- **Canonical relabelling, eager form.** An event of the ideal game is at most the same event
of the eager game on the program embedded into `pub.withLabels X K R`, read on the merged state,
or a conflict. -/
theorem prEvent_idealImpl_le_eagerImpl_liftComp {α : Type}
    (oa : OracleComp (pub.withDerivations X R) α)
    (P : α × SecretEncoding.SplitCache pub X R → Prop) :
    Pr{let z ← (simulateQ (SecretEncoding.idealImpl pub X R) oa).run (∅, ∅)}[P z] ≤
      Pr{let z ← (simulateQ G.eagerImpl (@liftComp _ _ _ _ oa (pub.withLabels X K R)
          (@instMonadLiftTOfMonadLift _ _ _ OracleQuery.subSpec_add_left.toMonadLift
            inferInstance))).run ∅}[P (z.1, G.toSplitCache z.2) ∨ G.Conflict z.2] := by
  rw [simulateQ_eagerImpl_liftComp]
  exact G.prEvent_idealImpl_le_relabelImpl oa P

end CanonicalGraph
