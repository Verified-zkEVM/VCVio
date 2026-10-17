/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module
public import ToMathlib.Probability.InfiniteTable

/-!
# Resampling one coordinate of an infinite table

Reading a coordinate and retaining the table has the same joint law as independently drawing
that coordinate and overwriting it in an independent table. Retaining the answer in this identity
is essential for adaptive lazy sampling.
-/

public section

open MeasureTheory ProbabilityTheory

namespace MeasureTheory.Measure

variable {D A : Type*} [DecidableEq D] [MeasurableSpace A] [Finite A] [Nonempty A]

/-- A table coordinate is independent of the table with that coordinate erased. -/
theorem uniformTable_indepFun_update (q : D) (value : A) :
    IndepFun (fun g : D → A => g q) (fun g => Function.update g q value) uniformTable := by
  let embed (g : {d : D // d ≠ q} → A) (d : D) := if h : d = q then value else g ⟨d, h⟩
  have hm : Measurable embed := by
    apply Measurable.of_eval
    intro d
    by_cases h : d = q
    · simp only [embed, h, dite_true]; exact measurable_const
    · simp only [embed, h, dite_false]; exact measurable_pi_apply _
  have hi := uniformTable_indepFun_restrict (A := A) ({q} : Set D) {d | d ≠ q}
    (by simp)
  have hh : IndepFun
      ((fun g : ({q} : Set D) → A => g ⟨q, Set.mem_singleton q⟩) ∘ Set.domRestrict {q})
      (embed ∘ Set.domRestrict {d : D | d ≠ q}) (uniformTable (A := A)) :=
    hi.comp (measurable_pi_apply _) hm
  convert hh using 1
  · rfl
  funext g d
  by_cases h : d = q <;> simp [embed, Function.update, h]

/-- Joint answer/table law is preserved when one coordinate is drawn afresh and stored. -/
theorem uniformTable_bind_update (q : D) :
    (uniformOn (Set.univ : Set A)).bind (fun r =>
      (uniformTable (D := D) (A := A)).map (fun g => (r, Function.update g q r))) =
      uniformTable.map (fun g : D → A => (g q, g)) := by
  let a : A := Classical.choice ‹Nonempty A›
  let erase (g : D → A) := Function.update g q a
  let put (p : A × (D → A)) := (p.1, Function.update p.2 q p.1)
  have he : Measurable erase := Measurable.of_eval fun d => by
    by_cases h : d = q
    · subst d; simpa only [erase, Function.update_self] using
        (measurable_const : Measurable (fun _ : D → A => a))
    · simpa only [erase, Function.update_of_ne h] using (measurable_pi_apply d)
  have hp : Measurable put := by
    apply Measurable.prodMk measurable_fst
    apply Measurable.of_eval
    intro d
    by_cases h : d = q
    · subst d; simpa only [Function.update_self] using measurable_fst (α := A) (β := D → A)
    · simpa only [Function.update_of_ne h, Function.comp_def] using
        (measurable_pi_apply d).comp measurable_snd
  have h := (uniformTable_indepFun_update (A := A) q a).map_prod_eq_prod_map_map
    (measurable_pi_apply q).aemeasurable he.aemeasurable
  rw [uniformTable_map_eval] at h
  have hm := congrArg (fun μ : Measure (A × (D → A)) => μ.map put) h
  rw [Measure.map_map hp ((measurable_pi_apply q).prodMk he)] at hm
  simp only [Function.comp_def, put, erase, Function.update_idem, Function.update_eq_self] at hm
  rw [Measure.prod_eq_of_sfinite] at hm
  rw [Measure.map_bind Measurable.map_prodMk_left.aemeasurable hp.aemeasurable] at hm
  simp only [Measure.map_map hp measurable_prodMk_left, Function.comp_def, put] at hm
  have hmap (r : A) :
      (uniformTable.map erase).map (fun g : D → A => (r, Function.update g q r)) =
        uniformTable.map (fun g : D → A => (r, Function.update g q r)) := by
    rw [Measure.map_map (by fun_prop) he]
    simp only [Function.comp_def, erase, Function.update_idem]
  simp only [erase] at hmap
  simp_rw [hmap] at hm
  exact hm.symm

end MeasureTheory.Measure
