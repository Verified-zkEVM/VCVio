/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module

public import VCVio.OracleComp.QueryTracking.RandomOracle.JointPotential
import VCVio.OracleComp.Constructions.SampleableType.Measure

/-!
# Projected hits and equal cells, charged in the deferred game

Two further hazards of the relabelled states of a canonical graph `G`, each charged
(`CanonicalGraph.IsCharged`) so that they join the joint potential of conflicts and target
collisions (`CanonicalGraph.IsCharged.or_add`).

* **Projected hits.** A key map with a projection (`CanonicalGraph.ProjKeys`) assigns to a public
  point the node, if any, at whose key it is read, and reads its answer, of whatever type, in the
  label type `R` through a projection whose image of a uniform answer takes any value with
  probability at most `1 / |R|`. A projected hit (`CanonicalGraph.ProjKeys.ProjHazard`) is a
  public entry at a node's key whose projection is that node's drawn label. Each entry fires it
  at most once, on whichever side of the label's draw the entry falls: a label draw pins one
  value per entry already at its key, and a fresh answer at the key of a drawn label hits it with
  probability at most `1 / |R|`. So projected hits are charged to the potential that counts the
  entries at the key of a node whose label is drawn, over `|R|`
  (`CanonicalGraph.ProjKeys.isCharged`); it is at most `#keyEntries / |R|`.
* **Equal cells.** Two distinct cells drawn equal (`CanonicalGraph.PairHazard`) are charged
  `1 / |R|` once both are drawn (`CanonicalGraph.isCharged_pairHazard`).

A key map with a projection generalises the target collision of `CanonicalGraph.NodeKeys`, whose
answers at a node key are labels, read as such; there the joint potential charges each entry
twice, once for the conflict and once for the target collision.
-/

public section

open OracleComp OracleSpec MeasureTheory
open scoped ENNReal

namespace CanonicalGraph

variable {ι : Type} {pub : OracleSpec ι} {X K R : Type}

/-! ## Projected hits -/

section Proj

variable [∀ t, SampleableType (pub.Range t)]

/-- **A key map with a projection.** It assigns to a public point the node, if any, at whose key
it is read, and reads an answer at a point in `R`; at a point at a node's key the reading of a
uniform answer takes any value with probability at most `1 / |R|`. -/
structure ProjKeys (G : CanonicalGraph pub X K R) where
  /-- The node at whose key a public point is read, if any. -/
  node : ι → Option K
  /-- The reading of an answer in `R`. -/
  proj : (t : ι) → pub.Range t → R
  /-- At a point at a node's key, the reading of a uniform answer is at most uniform. -/
  prEvent_proj_le : ∀ t k, node t = some k → ∀ ℓ : R,
    Pr{let u ← $ᵗ pub.Range t}[proj t u = ℓ] ≤ (Nat.card R : ℝ≥0∞)⁻¹

namespace ProjKeys

variable {G : CanonicalGraph pub X K R} (pk : G.ProjKeys)

/-- A projected hit: the public cache holds, at some point at the key of a node `k`, an answer
whose reading is the drawn label of `k`. -/
@[expose] def ProjHazard (st : RelabelState pub X K R) : Prop :=
  ∃ t k ℓ v, pk.node t = some k ∧ st.2 (.inr k) = some ℓ ∧ st.1 t = some v ∧ pk.proj t v = ℓ

/-- The public entries at the key of a node whose label is drawn. -/
def labelledEntries (st : RelabelState pub X K R) : Set ι :=
  {t | (st.1 t).isSome ∧ ∃ k, pk.node t = some k ∧ (st.2 (.inr k)).isSome}

/-- The public entries at the key of some node. -/
@[expose] def keyEntries (C : pub.QueryCache) : Set ι :=
  {t | (C t).isSome ∧ (pk.node t).isSome}

/-- The projected potential: the public entries at the key of a node whose label is drawn, over
`|R|`. -/
noncomputable def potential (st : RelabelState pub X K R) : ℝ≥0∞ :=
  ((pk.labelledEntries st).encard : ℝ≥0∞) / Nat.card R

variable {pk}

theorem labelledEntries_mono : Monotone pk.labelledEntries := fun _ _ hle _ ⟨hC, k, hk, hl⟩ ↦
  ⟨QueryCache.isSome_mono hle.1 hC, k, hk, QueryCache.isSome_mono hle.2 hl⟩

theorem potential_mono : Monotone pk.potential := fun _ _ hle ↦ by
  unfold potential
  gcongr
  exact labelledEntries_mono hle

/-- Each public entry at a projected key enters the potential at most once. -/
theorem potential_le (st : RelabelState pub X K R) :
    pk.potential st ≤ ((pk.keyEntries st.1).encard : ℝ≥0∞) / Nat.card R := by
  unfold potential
  gcongr
  rintro t ⟨hC, k, hk, -⟩
  exact ⟨hC, by rw [hk]; rfl⟩

theorem not_projHazard_empty : ¬pk.ProjHazard ((∅, ∅) : RelabelState pub X K R) := by
  rintro ⟨t, k, ℓ, v, -, hℓ, -⟩
  simp only [QueryCache.empty_apply, reduceCtorEq] at hℓ

/-- Drawing an undrawn cell out of a state with no projected hit fires one with probability at
most the weight it adds to the potential: one `1 / |R|` per entry at the key of the node whose
label it is. -/
private theorem exists_cell_charge [SampleableType R] [DecidableEq X] [DecidableEq K]
    {st : RelabelState pub X K R} (hst : ¬pk.ProjHazard st) {c : X ⊕ K} (hc : st.2 c = none) :
    ∃ w : ℝ≥0∞, Pr{let u ← $ᵗ R}[pk.ProjHazard (st.1, st.2.cacheQuery c u)] ≤ w ∧
      ∀ u : R, w + pk.potential st ≤ pk.potential (st.1, st.2.cacheQuery c u) := by
  set N := {t | (st.1 t).isSome ∧ ∃ k, pk.node t = some k ∧ (Sum.inr k : X ⊕ K) = c}
  refine ⟨(N.encard : ℝ≥0∞) / Nat.card R, ?_, fun u ↦ ?_⟩
  · let _ : MeasurableSpace R := ⊤
    rw [prEvent_eq_evalDist_of_discrete]
    refine (SampleableType.evalDist_uniformSample_le_encard_div _).trans ?_
    gcongr
    have hsub : some '' {u | pk.ProjHazard (st.1, st.2.cacheQuery c u)} ⊆
        (fun t ↦ (st.1 t).map (pk.proj t)) '' N := by
      rintro _ ⟨u, ⟨t, k, ℓ, v, hk, hℓ, hC, hp⟩, rfl⟩
      have hkc : (Sum.inr k : X ⊕ K) = c := by
        by_contra hne
        exact hst ⟨t, k, ℓ, v, hk, by rwa [QueryCache.cacheQuery_of_ne _ _ hne] at hℓ, hC, hp⟩
      subst hkc
      simp only [QueryCache.cacheQuery_self, Option.some_inj] at hℓ
      subst hℓ
      replace hC : st.1 t = some v := hC
      exact ⟨t, ⟨by rw [hC]; rfl, k, hk, rfl⟩, by beta_reduce; rw [hC, Option.map_some, hp]⟩
    rw [← (Option.some_injective R).encard_image]
    exact (Set.encard_le_encard hsub).trans (Set.encard_image_le _ _)
  · have hdisj : Disjoint N (pk.labelledEntries st) := by
      refine Set.disjoint_left.2 ?_
      rintro t ⟨-, k, hk, rfl⟩ ⟨-, k', hk', hl⟩
      obtain rfl : k = k' := Option.some_inj.1 (hk.symm.trans hk')
      rw [hc] at hl
      exact absurd hl Bool.false_ne_true
    have hsub : N ∪ pk.labelledEntries st ⊆ pk.labelledEntries (st.1, st.2.cacheQuery c u) := by
      refine Set.union_subset (fun t ⟨hC, k, hk, hkc⟩ ↦ ⟨hC, k, hk, ?_⟩)
        (labelledEntries_mono ⟨le_rfl, QueryCache.le_cacheQuery _ hc⟩)
      subst hkc
      simp only [QueryCache.cacheQuery_self, Option.isSome_some]
    unfold potential
    rw [ENNReal.div_add_div_same, ← ENat.toENNReal_add, ← Set.encard_union_eq hdisj]
    gcongr

/-- A fresh public answer out of a state with no projected hit fires one with probability at
most the weight it adds to the potential: `1 / |R|` if its point is at the key of a node whose
label is drawn, and `0` otherwise. -/
private theorem exists_pub_charge [DecidableEq ι] {st : RelabelState pub X K R}
    (hst : ¬pk.ProjHazard st) {t : ι} (ht : st.1 t = none) :
    ∃ w : ℝ≥0∞, Pr{let u ← $ᵗ pub.Range t}[pk.ProjHazard (st.1.cacheQuery t u, st.2)] ≤ w ∧
      ∀ u, w + pk.potential st ≤ pk.potential (st.1.cacheQuery t u, st.2) := by
  have hle : ∀ u : pub.Range t, st ≤ (st.1.cacheQuery t u, st.2) :=
    fun u ↦ ⟨QueryCache.le_cacheQuery _ ht, le_rfl⟩
  have hfire : ∀ u, pk.ProjHazard (st.1.cacheQuery t u, st.2) →
      ∃ k ℓ, pk.node t = some k ∧ st.2 (.inr k) = some ℓ ∧ pk.proj t u = ℓ := by
    rintro u ⟨t', k, ℓ, v, hk, hℓ, hC, hp⟩
    by_cases h : t' = t
    · subst h
      rw [QueryCache.cacheQuery_self, Option.some_inj] at hC
      subst hC
      exact ⟨k, ℓ, hk, hℓ, hp⟩
    · exact absurd ⟨t', k, ℓ, v, hk, hℓ, by rwa [QueryCache.cacheQuery_of_ne _ _ h] at hC, hp⟩ hst
  by_cases hT : ∃ k ℓ, pk.node t = some k ∧ st.2 (.inr k) = some ℓ
  · obtain ⟨k, ℓ, hk, hℓ⟩ := hT
    refine ⟨(Nat.card R : ℝ≥0∞)⁻¹, ?_, fun u ↦ ?_⟩
    · refine (prEvent_mono _ _ (fun u ↦ pk.proj t u = ℓ) fun u h ↦ ?_).trans
        (pk.prEvent_proj_le t k hk ℓ)
      obtain ⟨k', ℓ', hk', hℓ', hp⟩ := hfire u h
      obtain rfl : k = k' := Option.some_inj.1 (hk.symm.trans hk')
      rw [hℓ, Option.some_inj] at hℓ'
      exact hp.trans hℓ'.symm
    · have hins : insert t (pk.labelledEntries st) ⊆
          pk.labelledEntries (st.1.cacheQuery t u, st.2) :=
        Set.insert_subset ⟨by rw [QueryCache.cacheQuery_self]; rfl, k, hk, by rw [hℓ]; rfl⟩
          (labelledEntries_mono (hle u))
      have hnot : t ∉ pk.labelledEntries st := fun h ↦ by
        rw [labelledEntries, Set.mem_ofPred_eq, ht] at h
        exact Bool.false_ne_true h.1
      unfold potential
      rw [inv_eq_one_div, ENNReal.div_add_div_same]
      gcongr
      exact_mod_cast (add_comm _ _).trans_le
        ((Set.encard_insert_of_notMem hnot).symm.trans_le (Set.encard_le_encard hins))
  · refine ⟨0, le_of_eq (prEvent_eq_zero_of_forall_not _ _ fun u hu ↦ ?_),
      fun u ↦ by rw [zero_add]; exact potential_mono (hle u)⟩
    obtain ⟨k, ℓ, hk, hℓ, -⟩ := hfire u hu
    exact hT ⟨k, ℓ, hk, hℓ⟩

variable (pk) in
/-- **Projected hits are charged to the projected potential**, once per entry: at the label's
draw if the entry is older, at the answer if it is newer. -/
theorem isCharged [SampleableType R] [DecidableEq ι] [DecidableEq X] [DecidableEq K] :
    G.IsCharged pk.ProjHazard pk.potential where
  mono := potential_mono
  cell _ _ hst hc := exists_cell_charge hst hc
  pub _ _ hst ht _ := exists_pub_charge hst ht

end ProjKeys

end Proj

/-! ## Equal cells -/

section Pair

variable (X K R) in
/-- Two cells of a relabelled state hold one value. -/
@[expose] def PairHazard (c₁ c₂ : X ⊕ K) (st : RelabelState pub X K R) : Prop :=
  ∃ v, st.2 c₁ = some v ∧ st.2 c₂ = some v

open Classical in
/-- The pair potential: `1 / |R|` once both cells are drawn, `0` before. -/
noncomputable def pairPotential (c₁ c₂ : X ⊕ K) (st : RelabelState pub X K R) : ℝ≥0∞ :=
  if (st.2 c₁).isSome ∧ (st.2 c₂).isSome then (Nat.card R : ℝ≥0∞)⁻¹ else 0

variable {c₁ c₂ : X ⊕ K}

theorem pairPotential_le (st : RelabelState pub X K R) :
    pairPotential c₁ c₂ st ≤ (Nat.card R : ℝ≥0∞)⁻¹ := by
  unfold pairPotential
  split_ifs <;> simp

theorem pairPotential_mono : Monotone (pairPotential (pub := pub) (R := R) c₁ c₂) :=
  fun _ _ hle ↦ by
    unfold pairPotential
    split_ifs with h h'
    · exact le_rfl
    · exact absurd ⟨QueryCache.isSome_mono hle.2 h.1, QueryCache.isSome_mono hle.2 h.2⟩ h'
    · exact zero_le
    · exact le_rfl

theorem not_pairHazard_empty : ¬PairHazard X K R c₁ c₂ ((∅, ∅) : RelabelState pub X K R) := by
  rintro ⟨v, h, -⟩
  simp only [QueryCache.empty_apply, reduceCtorEq] at h

theorem pairHazard_comm {st : RelabelState pub X K R} :
    PairHazard X K R c₁ c₂ st ↔ PairHazard X K R c₂ c₁ st :=
  ⟨fun ⟨v, h₁, h₂⟩ ↦ ⟨v, h₂, h₁⟩, fun ⟨v, h₁, h₂⟩ ↦ ⟨v, h₂, h₁⟩⟩

theorem pairPotential_comm : pairPotential (pub := pub) (R := R) c₁ c₂ = pairPotential c₂ c₁ := by
  funext st
  simp only [pairPotential, and_comm]

variable [DecidableEq X] [DecidableEq K] [SampleableType R]

/-- Drawing the undrawn first cell of two distinct cells draws them equal with probability at most
the weight it adds to the pair potential. -/
private theorem exists_pair_charge (hne : c₁ ≠ c₂) {st : RelabelState pub X K R}
    (hc : st.2 c₁ = none) :
    ∃ w : ℝ≥0∞, Pr{let u ← $ᵗ R}[PairHazard X K R c₁ c₂ (st.1, st.2.cacheQuery c₁ u)] ≤ w ∧
      ∀ u, w + pairPotential c₁ c₂ st ≤ pairPotential c₁ c₂ (st.1, st.2.cacheQuery c₁ u) := by
  cases hv : st.2 c₂ with
  | none =>
    refine ⟨0, le_of_eq (prEvent_eq_zero_of_forall_not _ _ fun u ⟨v, _, h₂⟩ ↦ ?_), fun u ↦ ?_⟩
    · rw [QueryCache.cacheQuery_of_ne _ _ hne.symm, hv] at h₂
      cases h₂
    · simp [pairPotential, hc, hv, QueryCache.cacheQuery_of_ne _ _ hne.symm]
  | some v =>
    refine ⟨(Nat.card R : ℝ≥0∞)⁻¹, (prEvent_mono _ _ (· = v) ?_).trans
      (SampleableType.prEvent_uniformSample_eq_singleton_natCard v).le, fun u ↦ ?_⟩
    · rintro u ⟨v', h₁, h₂⟩
      rw [QueryCache.cacheQuery_self, Option.some_inj] at h₁
      rw [QueryCache.cacheQuery_of_ne _ _ hne.symm, hv, Option.some_inj] at h₂
      exact h₁.trans h₂.symm
    · simp [pairPotential, hc, hv, QueryCache.cacheQuery_of_ne _ _ hne.symm]

variable [∀ t, SampleableType (pub.Range t)] (G : CanonicalGraph pub X K R) in
/-- **Two distinct cells drawn equal are charged `1 / |R|`**, when the second of them is drawn. -/
theorem isCharged_pairHazard [DecidableEq ι] (hne : c₁ ≠ c₂) :
    G.IsCharged (PairHazard X K R c₁ c₂) (pairPotential c₁ c₂) where
  mono := pairPotential_mono
  cell st c hst hc := by
    by_cases h₁ : c = c₁
    · subst h₁
      exact exists_pair_charge hne hc
    by_cases h₂ : c = c₂
    · subst h₂
      simp only [pairHazard_comm (c₁ := c₁) (c₂ := c), pairPotential_comm (c₁ := c₁) (c₂ := c)]
      exact exists_pair_charge (Ne.symm hne) hc
    refine ⟨0, le_of_eq (prEvent_eq_zero_of_forall_not _ _ fun u ⟨v, h1, h2⟩ ↦ hst ⟨v, ?_, ?_⟩),
      fun u ↦ ?_⟩
    · rwa [QueryCache.cacheQuery_of_ne _ _ (Ne.symm h₁)] at h1
    · rwa [QueryCache.cacheQuery_of_ne _ _ (Ne.symm h₂)] at h2
    · rw [zero_add]
      exact pairPotential_mono ⟨le_rfl, QueryCache.le_cacheQuery _ hc⟩
  pub _ _ hst _ _ := ⟨0, le_of_eq (prEvent_eq_zero_of_forall_not _ _ fun _ h ↦ hst h),
    fun _ ↦ by rw [zero_add]; exact le_rfl⟩

end Pair

end CanonicalGraph
