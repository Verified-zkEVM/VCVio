/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import VCVio.OracleComp.QueryTracking.Instability.Collision

/-!
# Instability calculus canaries

Exact values of the flip probability, the instability and the partition instability on a random
oracle from `ℕ` to `Fin 4`. They pin the freshness and size side conditions of
`OracleSpec.QueryCache.flip` and show that the collision bound `(t - 1) / n` is attained.
Occupied-key updates test overwrite semantics, and ordinary-import canaries exercise independent
input/answer universes and higher-universe collision persistence. Biased answers show why the
collision bound needs uniformity, and a positive restricted event retains its original mass.
-/

public section

open OracleComp OracleSpec ENNReal

namespace VCVioTest.QueryCacheInstability

/-- A natural-number oracle with four uniformly sampled answers. -/
abbrev TestSpec : OracleSpec ℕ := ℕ →ₒ Fin 4

noncomputable local instance : UniformAnswerMeasure TestSpec :=
  UniformAnswerMeasure.ofFiniteNonempty TestSpec

/-- The databases that answer `1` at the point `0`. -/
private def answersOne : Set (QueryCache TestSpec) := {D | D 0 = some 1}

/-- The nonempty databases. -/
private def nonempty : Set (QueryCache TestSpec) := {D | D ≠ ∅}

/-- The databases with a collision. -/
private def collision : Set (QueryCache TestSpec) := {D | CacheHasCollision D}

/-- The partition of all databases by their entry at the point `0`. -/
private def byEntryAtZero (o : Option (Fin 4)) : Set (QueryCache TestSpec) := {D | D 0 = o}

private lemma cacheQuery_ne_empty (D : QueryCache TestSpec) (x : ℕ) (u : Fin 4) :
    D.cacheQuery x u ≠ ∅ := fun h => by
  have hx := congrArg (fun D' : QueryCache TestSpec => D' x) h
  simp at hx

/-- One of the four answers at the point `0` lands in `answersOne`. -/
private lemma updateProb_empty_answersOne :
    (∅ : QueryCache TestSpec).updateProb 0 answersOne = 1 / 4 := by
  classical
  rw [QueryCache.updateProb_eq_card_div]
  simp [answersOne, Finset.filter_eq']

-- Updating an occupied key samples a new answer and overwrites the stored value.
example : ((∅ : QueryCache TestSpec).cacheQuery 0 0).updateProb 0 answersOne = 1 / 4 := by
  classical
  rw [QueryCache.updateProb_eq_card_div]
  simp [answersOne, Finset.filter_eq']

-- The flip probability is attained at the fresh point `0` and is `0` at every other point.
example : QueryCache.flip {∅} answersOne 1 = 1 / 4 := by
  refine le_antisymm (QueryCache.flip_le_iff.mpr fun D hD _ x _ => ?_) ?_
  · obtain rfl : D = ∅ := hD
    by_cases hx : x = 0
    · subst hx
      exact updateProb_empty_answersOne.le
    · rw [QueryCache.updateProb_eq_prEvent]
      refine le_of_eq_of_le (prEvent_eq_zero_of_forall_not _ _ fun u hu => ?_) zero_le
      have h0 : ((∅ : QueryCache TestSpec).cacheQuery x u) 0 = some 1 := hu
      rw [QueryCache.cacheQuery_of_ne _ _ (Ne.symm hx)] at h0
      simp at h0
  · rw [← updateProb_empty_answersOne]
    exact QueryCache.updateProb_le_flip rfl (by simp) rfl

-- A query bound of `0` admits no database, whatever the properties are.
example : QueryCache.flip Set.univ (Set.univ : Set (QueryCache TestSpec)) 0 = 0 := by simp

-- A database already defined at `0` is not extended there: only fresh points count.
example : QueryCache.flip {(∅ : QueryCache TestSpec).cacheQuery 0 0} answersOne 2 = 0 := by
  refine nonpos_iff_eq_zero.mp (QueryCache.flip_le_iff.mpr fun D hD _ x hx => ?_)
  obtain rfl : D = (∅ : QueryCache TestSpec).cacheQuery 0 0 := hD
  have hx0 : x ≠ 0 := by
    rintro rfl
    simp at hx
  rw [QueryCache.updateProb_eq_prEvent]
  refine le_of_eq (prEvent_eq_zero_of_forall_not _ _ fun u hu => ?_)
  have h0 : (((∅ : QueryCache TestSpec).cacheQuery 0 0).cacheQuery x u) 0 = some 1 := hu
  rw [QueryCache.cacheQuery_of_ne _ _ (Ne.symm hx0)] at h0
  simp at h0

/-- Every extension of the empty database is nonempty. -/
private lemma updateProb_empty_nonempty :
    (∅ : QueryCache TestSpec).updateProb 0 nonempty = 1 := by
  rw [QueryCache.updateProb_eq_prEvent]
  exact (prEvent_eq_one_iff _ _).mpr fun u _ => cacheQuery_ne_empty ∅ 0 u

-- Instability of a property and of a union containing it are incomparable in general: "nonempty"
-- has instability `1`, and its union with "empty" is the stable property of all databases.
example : QueryCache.instability nonempty 1 = 1 :=
  le_antisymm (QueryCache.instability_le_one _ 1) <| le_max_of_le_left <| by
    rw [← updateProb_empty_nonempty]
    exact QueryCache.updateProb_le_flip (by simp [nonempty]) (by simp) rfl

example : QueryCache.instability (nonempty ∪ nonemptyᶜ) 1 = 0 := by
  rw [Set.union_compl_self, QueryCache.instability_univ]

-- The other direction: the stable empty property gains instability `1` in a union.
example : QueryCache.instability (∅ : Set (QueryCache TestSpec)) 1 <
    QueryCache.instability (∅ ∪ nonempty) 1 := by
  rw [Set.empty_union, QueryCache.instability_empty]
  refine lt_of_lt_of_le zero_lt_one (le_max_of_le_left ?_)
  rw [← updateProb_empty_nonempty]
  exact QueryCache.updateProb_le_flip (by simp [nonempty]) (by simp) rfl

-- Conditioning restricts the target as well as the source: no nonempty database is empty.
example : QueryCache.condFlip nonempty {∅} 1 = 0 := by
  have h : nonempty ∩ ({∅} : Set (QueryCache TestSpec)) = ∅ := by
    ext D
    simp [nonempty]
  rw [QueryCache.condFlip, h, QueryCache.flip_empty_right]

-- Restriction retains the original mass: the only allowed nonempty target has mass `1/4`.
example : QueryCache.condFlip answersOne ({∅} ∪ answersOne) 1 = 1 / 4 := by
  have hsource : answersOneᶜ ∩ ({∅} ∪ answersOne) = ({∅} : Set (QueryCache TestSpec)) := by
    ext D
    simp only [Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_union, Set.mem_singleton_iff]
    constructor
    · rintro ⟨hnot, hempty | hone⟩
      · exact hempty
      · exact (hnot hone).elim
    · rintro rfl
      exact ⟨by simp [answersOne], Or.inl rfl⟩
  have htarget : answersOne ∩ ({∅} ∪ answersOne) = answersOne :=
    Set.inter_eq_self_of_subset_left Set.subset_union_right
  rw [QueryCache.condFlip, hsource, htarget]
  refine le_antisymm (QueryCache.flip_le_iff.mpr fun D hD _ x _ => ?_) ?_
  · obtain rfl : D = ∅ := hD
    by_cases hx : x = 0
    · subst hx
      exact updateProb_empty_answersOne.le
    · rw [QueryCache.updateProb_eq_prEvent]
      refine le_of_eq_of_le (prEvent_eq_zero_of_forall_not _ _ fun u hu => ?_) zero_le
      have h0 : ((∅ : QueryCache TestSpec).cacheQuery x u) 0 = some 1 := hu
      rw [QueryCache.cacheQuery_of_ne _ _ (Ne.symm hx)] at h0
      simp at h0
  · rw [← updateProb_empty_answersOne]
    exact QueryCache.updateProb_le_flip rfl (by simp) rfl

-- Cardinality alone gives no collision bound: a point mass makes the fresh answer collide surely.
example :
    letI : AnswerMeasure TestSpec :=
      { toMeasure := fun _ => MeasureTheory.Measure.dirac 0
        isProbabilityMeasure := fun _ => inferInstance }
    ((∅ : QueryCache TestSpec).cacheQuery 0 0).updateProb 1 collision = 1 ∧
      ¬(1 : ℝ≥0∞) ≤ 1 / 4 := by
  let : AnswerMeasure TestSpec :=
    { toMeasure := fun _ => MeasureTheory.Measure.dirac 0
      isProbabilityMeasure := fun _ => inferInstance }
  constructor
  · change (MeasureTheory.Measure.dirac (0 : Fin 4))
      {u | ((∅ : QueryCache TestSpec).cacheQuery 0 0).cacheQuery 1 u ∈ collision} = 1
    have hcoll : ((∅ : QueryCache TestSpec).cacheQuery 0 0).cacheQuery 1 0 ∈ collision :=
      ⟨0, 1, 0, 0, by decide, by simp, by simp, HEq.rfl⟩
    rw [MeasureTheory.Measure.dirac_apply' _ MeasurableSpace.measurableSet_top]
    have hmem : (0 : Fin 4) ∈
        {u | ((∅ : QueryCache TestSpec).cacheQuery 0 0).cacheQuery 1 u ∈ collision} := hcoll
    exact Set.indicator_of_mem hmem _
  · norm_num

/-- The database `{0 ↦ 0}` has no collision. -/
private lemma not_collision_single :
    ¬CacheHasCollision ((∅ : QueryCache TestSpec).cacheQuery 0 0) := by
  rintro ⟨x₁, x₂, u₁, u₂, hne, h₁, h₂, -⟩
  have h₁' : x₁ = 0 := by
    by_contra h
    simp [QueryCache.cacheQuery_of_ne _ _ h] at h₁
  have h₂' : x₂ = 0 := by
    by_contra h
    simp [QueryCache.cacheQuery_of_ne _ _ h] at h₂
  exact hne (h₁'.trans h₂'.symm)

-- The collision bound `(t - 1) / n` is attained at `t = 2`: the database `{0 ↦ 0}` collides
-- when the fresh point `1` receives the answer `0`.
example : QueryCache.instability collision 2 = 1 / 4 := by
  refine le_antisymm ?_ (le_max_of_le_left ?_)
  · simpa [collision] using
      QueryCache.instability_cacheHasCollision_le (spec := TestSpec) (n := 4)
        (fun _ => (Fintype.card_fin 4).ge) 2
  · classical
    have hsize : ((∅ : QueryCache TestSpec).cacheQuery 0 0).toSet.encard < (2 : ℕ) :=
      lt_of_le_of_lt (QueryCache.toSet_encard_cacheQuery_le _ _ _) (by simp)
    refine le_trans ?_ (QueryCache.updateProb_le_flip (x := 1) not_collision_single hsize
      (by simp))
    rw [QueryCache.updateProb_eq_card_div]
    refine ENNReal.div_le_div (Nat.one_le_cast.mpr (Finset.card_pos.mpr ⟨0, ?_⟩)) (by simp)
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, 0, 1, 0, 0, by decide, by simp, by simp,
      HEq.rfl⟩

-- One fresh answer never removes a collision.
example (t : ℕ) : QueryCache.flip collision collisionᶜ t = 0 :=
  QueryCache.flip_cacheHasCollision_compl t

-- The printed strict bound of [CMS19, Lemma 6.11] fails at `t = 0`, where both sides vanish.
example : ¬QueryCache.instability collision 0 < (0 : ℕ) / (4 : ℝ≥0∞) := by simp

-- The entry at `0` moves the empty database out of its class with probability `1`.
example : QueryCache.partitionInstability byEntryAtZero 1 = 1 := by
  refine le_antisymm (QueryCache.partitionInstability_le_one _ 1)
    (le_iSup_of_le none ?_)
  refine le_trans (le_of_eq ?_) (QueryCache.updateProb_le_flip (D := ∅) (x := 0) rfl (by simp) rfl)
  rw [QueryCache.updateProb_eq_prEvent]
  refine ((prEvent_eq_one_iff _ _).mpr fun u _ => ?_).symm
  exact Set.mem_iUnion₂.mpr ⟨some u, by simp, by simp [byEntryAtZero]⟩

-- The two-class partition recovers the instability of a property.
example (t : ℕ) :
    QueryCache.partitionInstability (fun b : Bool => cond b collision collisionᶜ) t =
      QueryCache.instability collision t :=
  QueryCache.partitionInstability_cond collision t

-- Conditioning on "no collision" and paying for the collision property bounds a union.
example (P : Set (QueryCache TestSpec)) (t : ℕ) :
    QueryCache.instability (P ∪ collision) t ≤
      QueryCache.condInstability P collisionᶜ t + (t : ℝ≥0∞) / 4 :=
  (QueryCache.instability_union_le P collision t).trans <| add_le_add le_rfl <| by
    simpa [collision] using
      QueryCache.instability_cacheHasCollision_le_div (spec := TestSpec) (n := 4)
        (fun _ => (Fintype.card_fin 4).ge) t

-- Independent index and answer universes through an ordinary public import.
example [AnswerMeasure (Unit →ₒ ULift.{1} Bool)]
    (D : QueryCache (Unit →ₒ ULift.{1} Bool)) (P Q : Set (QueryCache (Unit →ₒ ULift.{1} Bool)))
    (t : ℕ) :
    D.updateProb () P ≤ 1 ∧ QueryCache.flip P Q t ≤ 1 ∧
      QueryCache.instability P t ≤ 1 ∧ QueryCache.condFlip P Q t ≤ 1 ∧
      QueryCache.condInstability P Q t ≤ 1 ∧
      QueryCache.partitionInstability (fun b : Bool => cond b P Q) t ≤ 1 := by
  exact ⟨QueryCache.updateProb_le_one _ _ _, QueryCache.flip_le_one _ _ _,
    QueryCache.instability_le_one _ _,
    (QueryCache.condFlip_le_flip _ _ _).trans (QueryCache.flip_le_one _ _ _),
    (QueryCache.condInstability_le_instability _ _ _).trans (QueryCache.instability_le_one _ _),
    QueryCache.partitionInstability_le_one _ _⟩

-- Collision persistence also works when both input and answer types live in `Type 1`.
example [AnswerMeasure (ULift.{1} Bool →ₒ ULift.{1} Bool)] (t : ℕ) :
    QueryCache.flip
      {D : QueryCache (ULift.{1} Bool →ₒ ULift.{1} Bool) | CacheHasCollision D}
      {D | CacheHasCollision D}ᶜ t = 0 :=
  QueryCache.flip_cacheHasCollision_compl t

end VCVioTest.QueryCacheInstability
