/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import VCVio.Quantum.Oracle.Compressed.CollisionPotential

/-!
# Collision events of compressed databases

The collision event in ePrint 2025/2166 §9.3 (Lemma 9.6, p. 61;
event bound, pp. 64–65) changes at a cell only for answers already stored elsewhere.
Thus the changing-answer count is at most the number of occupied entries outside that cell.
This supports the bounds note's (NOTE) refinement in equations (87)–(89), (91).
Recording registers are not part of this population.
-/

public section

namespace Quantum.Database

variable {X Y : Type*}

/-- A partial database is collision-free when distinct filled keys have distinct answers. -/
@[expose]
def CollisionFree (D : Database X Y) : Prop :=
  ∀ x x' y, D x = some y → D x' = some y → x = x'

/-- The empty database is collision-free. -/
theorem collisionFree_empty : (empty : Database X Y).CollisionFree := by
  intro x x' y hx
  simp at hx

/-- The answers stored in the occupied entries of a database. -/
@[expose]
def values [Fintype X] [DecidableEq Y] (D : Database X Y) : Finset Y :=
  Finset.univ.biUnion fun x ↦ (D x).toFinset

/-- Membership in the stored-answer set means that some entry stores that answer. -/
@[simp]
theorem mem_values [Fintype X] [DecidableEq Y] {D : Database X Y} {y : Y} :
    y ∈ D.values ↔ ∃ x, D x = some y := by
  simp [values, Option.mem_toFinset]

/-- There are at most as many stored answers as occupied entries. -/
theorem card_values_le [Fintype X] [DecidableEq Y] (D : Database X Y) :
    D.values.card ≤ D.size := by
  classical
  refine (Finset.card_biUnion_le).trans_eq ?_
  rw [size, Finset.card_filter]
  apply Finset.sum_congr rfl
  intro x _
  cases D x <;> simp

/-- Inserting an answer not stored elsewhere preserves collision-freedom in both directions. -/
theorem collisionFree_update_some_iff [Fintype X] [DecidableEq X] [DecidableEq Y]
    {D : Database X Y} {x : X} (hx : D x = none) {y : Y} (hy : y ∉ D.values) :
    CollisionFree (Function.update D x (some y)) ↔ D.CollisionFree := by
  have fresh : ∀ z, D z ≠ some y := by simpa using hy
  constructor
  · intro h z z' v hz hz'
    have hzx : z ≠ x := by rintro rfl; simp [hx] at hz
    have hz'x : z' ≠ x := by rintro rfl; simp [hx] at hz'
    exact h z z' v (by simpa [hzx] using hz) (by simpa [hz'x] using hz')
  · intro h z z' v hz hz'
    by_cases hzx : z = x
    · subst z
      simp only [Function.update_self, Option.some.injEq] at hz
      subst v
      by_cases hz'x : z' = x
      · exact hz'x.symm
      · exact False.elim (fresh z' (by simpa [hz'x] using hz'))
    · by_cases hz'x : z' = x
      · subst z'
        simp only [Function.update_self, Option.some.injEq] at hz'
        subst v
        exact False.elim (fresh z (by simpa [hzx] using hz))
      · exact h z z' v (by simpa [hzx] using hz) (by simpa [hz'x] using hz')

/-- The binary event that a database contains a collision. -/
@[expose]
noncomputable def collisionLabel (D : Database X Y) : Bool :=
  @decide (¬D.CollisionFree) (Classical.propDecidable _)

/-- The collision event is false exactly on collision-free databases. -/
@[simp]
theorem collisionLabel_eq_false (D : Database X Y) :
    D.collisionLabel = false ↔ D.CollisionFree := by
  classical
  simp [collisionLabel]

/-- The empty database has no collision weight. -/
@[simp]
theorem collisionLabel_empty : (empty : Database X Y).collisionLabel = false :=
  (collisionLabel_eq_false _).mpr collisionFree_empty

/-- The changing answers of the collision event are contained in the stored answers.
A fixed additional bad event may be included, for example a collision in another database. -/
theorem collisionFlipSet_subset_values [Fintype X] [DecidableEq X] [Fintype Y]
    [DecidableEq Y] {D : Database X Y} {x : X} (hx : D x = none) (bad : Bool) :
    binaryFlipSet (fun a ↦ bad || collisionLabel (Function.update D x a)) ⊆ D.values := by
  classical
  intro y hy
  by_contra hfresh
  have hfree := collisionFree_update_some_iff hx hfresh
  have hl : collisionLabel (Function.update D x (some y)) = D.collisionLabel := by
    simp only [collisionLabel]
    exact congrArg (fun p : Prop ↦ decide p) (propext (not_congr hfree))
  have he : Function.update D x none = D := by rw [← hx, Function.update_eq_self]
  simp [binaryFlipSet, hl, he] at hy

/-- The collision changing-answer count is bounded by the population outside the queried cell. -/
theorem card_collisionFlipSet_le [Fintype X] [DecidableEq X] [Fintype Y]
    {D : Database X Y} {x : X} (hx : D x = none) (bad : Bool) :
    (binaryFlipSet (fun a ↦ bad || collisionLabel (Function.update D x a))).card ≤ D.size := by
  classical
  exact (Finset.card_le_card (collisionFlipSet_subset_values hx bad)).trans (card_values_le D)

/-- All databases in a family are collision-free; answers in different databases may coincide. -/
@[expose]
def AllCollisionFree {ι : Type*} (D : ι → Database X Y) : Prop :=
  ∀ i, (D i).CollisionFree

/-- An empty family of databases is collision-free. -/
theorem allCollisionFree_empty {ι : Type*} :
    AllCollisionFree (fun _ : ι ↦ (empty : Database X Y)) :=
  fun _ ↦ collisionFree_empty

/-- The event that at least one database in a family contains a collision. -/
@[expose]
noncomputable def allCollisionLabel {ι : Type*} (D : ι → Database X Y) : Bool :=
  @decide (¬AllCollisionFree D) (Classical.propDecidable _)

open scoped Classical in
/-- Splitting the family collision event into one database and the other databases. -/
theorem allCollisionLabel_update {ι : Type*} [DecidableEq ι]
    (D : ι → Database X Y) (i : ι) (d : Database X Y) :
    allCollisionLabel (Function.update D i d) =
      (decide (∃ j, j ≠ i ∧ ¬(D j).CollisionFree) || d.collisionLabel) := by
  classical
  apply Bool.eq_iff_iff.mpr
  simp only [allCollisionLabel, collisionLabel, Bool.or_eq_true, decide_eq_true_eq,
    AllCollisionFree, Function.forall_update_iff, not_and_or, not_forall]
  simp only [exists_prop, or_comm]

/-- For a family collision event, changing one cell has at most the other-entry count
of that database as changing answers. -/
theorem card_allCollisionFlipSet_le {ι : Type*} [DecidableEq ι]
    [Fintype X] [DecidableEq X] [Fintype Y]
    (D : ι → Database X Y) (i : ι) {r : Database X Y} {x : X} (hr : r x = none) :
    (binaryFlipSet (fun a ↦ allCollisionLabel
      (Function.update D i (Function.update r x a)))).card ≤ r.size := by
  classical
  simp_rw [allCollisionLabel_update]
  exact card_collisionFlipSet_le hr _

end Quantum.Database
