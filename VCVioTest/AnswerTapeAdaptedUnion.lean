/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module

public import VCVio.OracleComp.ProbComp.IndepProductEvents.AdaptedUnion

/-!
# Predictability and dynamic-ticket boundary controls

The current answer cannot select its own singleton target.
Overlapping projections share one word and need no independence premise.
-/

public section

open MeasureTheory AnswerTape
open scoped ENNReal

namespace AnswerTapeAdaptedUnionTest

/-- The averaging law permits dependence on a later coordinate. -/
theorem later_coordinate_target {W : Type} [SampleableType W]
    [MeasurableSpace W] [DiscreteMeasurableSpace W]
    {n : Nat} (i j : Fin n) (different : j ≠ i) (target : W → Set W) :
    𝒟[answerTape W n] {v | v i ∈ target (v j)} =
      ∫⁻ v, 𝒟[($ᵗ W : ProbComp W)] (target (v j)) ∂𝒟[answerTape W n] := by
  apply evalDist_answerTape_setOf_mem_eq_lintegral_of_update_invariant
  intro v value
  simp [different]

/-- With no coordinates, no target comparison can occur. -/
theorem zero_length {W D H : Type} [SampleableType W]
    (slots : Finset H) (projection : H → W → D)
    (targets : Fin 0 → (Fin 0 → W) → H → Finset D) :
    Pr{let v ← answerTape W 0}[
      ∃ i : Fin 0, ∃ h ∈ slots, projection h (v i) ∈ targets i v h] = 0 := by
  simp

/-- An empty finite slot set gives the empty event, even for infinite slot types. -/
theorem empty_slots {W D H : Type} [SampleableType W] {n : Nat}
    (projection : H → W → D) (targets : Fin n → (Fin n → W) → H → Finset D) :
    Pr{let v ← answerTape W n}[
      ∃ i : Fin n, ∃ h ∈ (∅ : Finset H), projection h (v i) ∈ targets i v h] = 0 := by
  simp

/-- Zero tickets give probability zero even when the fiber bound is infinite. -/
theorem zero_tickets_even_top {W D H : Type} [SampleableType W] {n : Nat}
    (slots : Finset H) (projection : H → W → D)
    (targets : Fin n → (Fin n → W) → H → Finset D)
    (predictable : ∀ i v w,
      (∀ j : Fin n, j.val < i.val → v j = w j) → targets i v = targets i w)
    (budget : ∀ v, (∑ i : Fin n, ∑ h ∈ slots, (targets i v h).card) ≤ 0) :
    Pr{let v ← answerTape W n}[
      ∃ i : Fin n, ∃ h ∈ slots, projection h (v i) ∈ targets i v h] = 0 := by
  apply le_antisymm _ bot_le
  simpa using prEvent_answerTape_exists_project_mem_le_tickets
    slots projection targets ⊤ predictable (fun _ _ _ => le_top) budget

/-- A zero fixed-fiber mass gives zero union mass without requiring a positive budget. -/
theorem zero_fiber_mass {W D H : Type} [SampleableType W] {n B : Nat}
    (slots : Finset H) (projection : H → W → D)
    (targets : Fin n → (Fin n → W) → H → Finset D)
    (predictable : ∀ i v w,
      (∀ j : Fin n, j.val < i.val → v j = w j) → targets i v = targets i w)
    (fiberBound : ∀ h ∈ slots, ∀ d,
      Pr{let word ← ($ᵗ W : ProbComp W)}[projection h word = d] ≤ 0)
    (budget : ∀ v, (∑ i : Fin n, ∑ h ∈ slots, (targets i v h).card) ≤ B) :
    Pr{let v ← answerTape W n}[
      ∃ i : Fin n, ∃ h ∈ slots, projection h (v i) ∈ targets i v h] = 0 := by
  apply le_antisymm _ bot_le
  simpa using prEvent_answerTape_exists_project_mem_le_tickets
    slots projection targets 0 predictable fiberBound budget

/-- Two identical projections at the same word give one event, not independent events. -/
theorem overlapping_slots {W : Type} [SampleableType W] {n : Nat}
    (i : Fin n) (targets : (Fin n → W) → Finset W) :
    Pr{let v ← answerTape W n}[∃ h ∈ ({0, 1} : Finset Nat), v i ∈ targets v] =
      Pr{let v ← answerTape W n}[v i ∈ targets v] := by
  apply prEvent_congr
  intro v
  simp

/-- Selecting the current word as its own singleton target makes the event certain. -/
theorem current_selected_singleton_probability :
    Pr{let v ← answerTape (Fin 2) 1}[v 0 ∈ ({v 0} : Finset (Fin 2))] = 1 := by
  let : MeasurableSpace (Fin 1 → Fin 2) := ⊤
  simp [prEvent_eq_evalDist_of_discrete]

/-- Each fixed binary target still has mass one half. -/
theorem binary_fixed_target (target : Fin 2) :
    Pr{let word ← ($ᵗ (Fin 2) : ProbComp (Fin 2))}[word = target] = (2 : ℝ≥0∞)⁻¹ := by
  simpa using SampleableType.prEvent_uniformSample_eq_singleton target

/-- A current-answer singleton fails the empty-prefix predictability requirement. -/
theorem current_selected_singleton_not_predictable :
    ¬ (∀ v w : Fin 1 → Fin 2,
      (∀ j : Fin 1, j.val < 0 → v j = w j) →
      ({v 0} : Finset (Fin 2)) = {w 0}) := by
  intro predictable
  have impossible := predictable (fun _ => 0) (fun _ => 1) (by
    intro j earlier
    omega)
  have member : (0 : Fin 2) ∈ ({1} : Finset (Fin 2)) := by
    rw [← impossible]
    simp
  simp at member

/-- The earlier word allocates exactly one comparison to one of two later positions. -/
theorem adaptive_single_ticket :
    let targets : Fin 3 → (Fin 3 → Fin 2) → Unit → Finset (Fin 2) :=
      fun i v _ => if (i = 1 ∧ v 0 = 0) ∨ (i = 2 ∧ v 0 ≠ 0) then {0} else ∅
    Pr{let v ← answerTape (Fin 2) 3}[
      ∃ i : Fin 3, ∃ h ∈ ({()} : Finset Unit), v i ∈ targets i v h] ≤
      (2 : ℝ≥0∞)⁻¹ := by
  classical
  let targets : Fin 3 → (Fin 3 → Fin 2) → Unit → Finset (Fin 2) :=
    fun i v _ => if (i = 1 ∧ v 0 = 0) ∨ (i = 2 ∧ v 0 ≠ 0) then {0} else ∅
  change Pr{let v ← answerTape (Fin 2) 3}[
    ∃ i : Fin 3, ∃ h ∈ ({()} : Finset Unit), v i ∈ targets i v h] ≤ (2 : ℝ≥0∞)⁻¹
  have predictable : ∀ (i : Fin 3) (v w : Fin 3 → Fin 2),
      (∀ j : Fin 3, j.val < i.val → v j = w j) → targets i v = targets i w := by
    intro i v w earlierValues
    funext h
    by_cases first : i = 0
    · subst i
      simp [targets]
    · have positive : 0 < i.val := Nat.pos_of_ne_zero (by
        intro zero
        exact first (Fin.ext zero))
      have same := earlierValues 0 positive
      simp only [targets, same]
  have budget : ∀ v, (∑ i : Fin 3, ∑ h ∈ ({()} : Finset Unit),
      (targets i v h).card) ≤ 1 := by
    intro v
    by_cases chosen : v 0 = 0 <;> simp [targets, Fin.sum_univ_succ, chosen]
  have bound := prEvent_answerTape_exists_project_mem_le_tickets
    ({()} : Finset Unit) (fun _ (word : Fin 2) => word) targets (2 : ℝ≥0∞)⁻¹ predictable
    (fun _ _ d => (binary_fixed_target d).le) budget
  simpa using bound

end AnswerTapeAdaptedUnionTest
