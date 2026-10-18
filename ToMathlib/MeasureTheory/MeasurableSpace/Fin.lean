/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.Data.Fin.Tuple.Basic

/-!+# Measurable finite tuple extension

Appending an observation to a finite history is measurable in both arguments.
-/

public section

open MeasureTheory

/-- Extending a finite tuple preserves joint measurability. -/
@[fun_prop] theorem measurable_fin_snoc {S : Type*} [MeasurableSpace S] (n : ℕ) :
    Measurable (fun pair : (Fin n → S) × S =>
      (Fin.snoc pair.1 pair.2 : Fin (n + 1) → S)) := by
  apply Measurable.of_eval
  intro i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simpa only [Fin.snoc_last] using (measurable_snd : Measurable (Prod.snd : (Fin n → S) × S → S))
  · simpa only [Fin.snoc_castSucc, Function.comp_def] using (measurable_pi_apply j).comp
      (measurable_fst : Measurable (Prod.fst : (Fin n → S) × S → (Fin n → S)))

/-- Appending a sampled value to a fixed history is measurable. -/
@[fun_prop] theorem measurable_fin_snoc_right {S : Type*} [MeasurableSpace S] {n : ℕ}
    (history : Fin n → S) : Measurable (Fin.snoc (α := fun _ : Fin (n + 1) => S) history) := by
  simpa only [Function.comp_def, id_eq] using
    (measurable_fin_snoc n).comp ((measurable_const (a := history)).prodMk measurable_id)
